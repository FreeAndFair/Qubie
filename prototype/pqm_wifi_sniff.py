#!/usr/bin/env python

# Polling Queue Monitor Proof of Concept - WiFi Sniffer
# Written by Daniel M. Zimmerman (dmz@galois.com)
# Copyright (C) 2015 Galois, Inc.

import argparse
import binascii
import csv
import operator
import os
import signal
import threading
import time
from scapy.all import *
from scapy.error import *
from watchdog.observers import Observer
from watchdog.events import PatternMatchingEventHandler

MGMT_TYPE = 0
MGMT_SUBTYPES = (0, 2, 4)
UPDATE_INTERVAL = 60
TIMEOUT_INTERVAL = 480

class Sniffer(threading.Thread):
  def __init__(self, ifname, blacklist, whitelist, logfile, numfile, rangefile):
    super(Sniffer, self).__init__()
    
    # initialize signal handler
    signal.signal(signal.SIGINT, self.signaled)
    signal.signal(signal.SIGTERM, self.signaled)
    
    # initialize variables
    self.firsts = {}
    self.lasts = {}
    self.disallowed_macs = set()
    self.locally_managed_macs = set()
    self.past_ranges = []
    self.past_num_devices = []
    self.last_update = time.time()
    self.running = True
    self.ifname = ifname
    self.blacklist = blacklist
    self.whitelist = whitelist
    self.using_whitelist = len(self.whitelist) > 0
    self.logfile = None
    if logfile != None:
      try:
        self.logfile = open(logfile, 'a', 1)
        self.logfile.write('\n---NEW RUN---\n')
      except IOError:
        print('could not open log file {}, proceeding with no log file'.format(logfile))
        self.logfile = None
    self.log('started listening on interface {}'.format(self.ifname))
    if self.using_whitelist:
      self.log('whitelist contains {} OUIs'.format(len(self.whitelist)))
    elif len(self.blacklist) > 0:
      self.log('blacklist contains {} OUIs'.format(len(self.blacklist)))
    else:
      self.log('accepting all OUIs')
    self.numfile = None
    self.numwriter = None
    if numfile != None:
      try:
        self.numfile = open(numfile, 'w', 1)
        self.numwriter = csv.DictWriter(self.numfile, fieldnames=['time', 'num_devices'])
        self.numwriter.writeheader()
      except IOError:
        self.log('could not open number of devices per unit time file {}, proceeding without it'.format(numfile))
        self.numfile = None
    self.rangefile = None
    self.rangewriter = None
    if rangefile != None:
      try:
        self.rangefile = open(rangefile, 'w', 1)
        self.rangewriter = csv.DictWriter(self.rangefile, fieldnames=['device','start_time','end_time'])
        self.rangewriter.writeheader()
      except IOError:
        self.log('could not open device presence range file {}, proceeding without it'.format(rangefile))
        self.rangefile = None
        
  # the run method for this thread
  def run(self):
    while self.running:
      sniff(iface=self.ifname, prn=self.sniff_packet, timeout=30)
    
    self.log('shutting down')
    
    for m in sorted(self.firsts.keys()):
      self.log('mac {} present for {} minutes at shutdown'.format(m, int((self.lasts[m] - self.firsts[m]) // 60)))
      self.past_ranges.append((m, self.firsts[m], self.lasts[m]))
      if self.rangewriter != None:
        self.rangewriter.writerow({'device': m,
                                   'start_time': self.firsts[m],
                                   'end_time': self.lasts[m]})
      self.firsts.pop(m, None)
      self.lasts.pop(m, None)

    if self.logfile != None:
      self.logfile.flush()
      os.fsync(self.logfile)
    if self.numfile != None:
      self.numfile.flush()
      os.fsync(self.numfile)
    if self.rangefile != None:
      self.rangefile.flush()
      os.fsync(self.rangefile)

  # the method to be called when this thread is signaled
  def signaled(self, signum, frame):
    self.running = False
  
  # the stop method for this thread
  def stop(self):
    self.running = False
  
  # the method that determines whether a MAC prefix is disallowed;
  # a MAC prefix on the blacklist is always disallowed, a MAC
  # prefix on the whitelist is always allowed, and a MAC address
  # on neither list is allowed if the blacklist is being used and
  # disallowed if the whitelist is being used; note that only
  # one of the whitelist and blacklist can be used at a time
  def disallowed(self, mac):
    if mac[:6] in self.blacklist:
      return True
    if mac[:6] in self.whitelist:
      return False
    return self.using_whitelist

  # log a message, to either the console or the log file
  def log(self, msg):
    timestamp = time.strftime('[%Y-%m-%d %H:%M:%S %Z]', time.localtime(time.time()))
    entry = '{}: {}'.format(timestamp, msg)
    if self.logfile != None:
      self.logfile.write(entry)
      self.logfile.write('\n')
    else:
      print entry
                                              
  # records a packet and its timestamp if it's a WiFi management packet
  def sniff_packet(self, p):
    # if it's a management packet, let's get its mac address and register
    # it as seen at this time
    mac = None
    if p.haslayer(Dot11):
      mac = p.addr2
      if mac != None:
        macbytes = binascii.unhexlify(mac.replace(b':', b''))
        mac = mac.lower().replace(":","")
        rssi = -(256-ord(p.notdecoded[-4:-3]))
        allowed = True
        
        if (ord(macbytes[0]) & 0x02 > 0):
          if not mac in self.locally_managed_macs:
            self.locally_managed_macs.add(mac)
            timestruct = time.localtime(p.time)
            self.log('locally-managed mac {} appeared'.format(mac))
          allowed = False
        elif self.disallowed(mac):
          if not mac in self.disallowed_macs:
            self.disallowed_macs.add(mac)
            timestruct = time.localtime(p.time)
            self.log('disallowed mac {} appeared'.format(mac))
          allowed = False
        elif mac not in self.firsts:
          self.firsts[mac] = p.time
          timestruct = time.localtime(p.time)
          self.log('mac {} appeared, RSSI {}\n'.format(mac, rssi))
        elif (p.time - self.lasts[mac] > UPDATE_INTERVAL): 
          timestruct = time.localtime(p.time)
          first_timestruct = time.localtime(self.firsts[mac])
          self.log('mac {} has been here {} minutes, RSSI {}'.format(mac, int((p.time - self.firsts[mac]) // 60), rssi))
        
        if allowed:
          self.lasts[mac] = p.time
                    
    # now, update the list of macs in proximity based on our timeout interval
    if (time.time() - self.last_update > UPDATE_INTERVAL):
      self.last_update = time.time()
      timestruct = time.localtime(self.last_update)
      if self.numwriter != None:
        self.numwriter.writerow({'time': int(round(self.last_update - start_time)) / 60,
                                 'num_devices': len(self.firsts)})
      self.log('{} devices assumed to be present'.format(len(self.firsts)))
      for m in sorted(self.firsts.keys()):
        if time.time() - self.lasts[m] > TIMEOUT_INTERVAL:
          self.log('mac {} disappeared after {} minutes\n'.format(m, int((self.lasts[m] - self.firsts[m]) // 60)))
          self.past_ranges.append((m, self.firsts[m], self.lasts[m]))
          if self.rangewriter != None:
            self.rangewriter.writerow({'device': m,
                                       'start_time': self.firsts[m],
                                       'end_time': self.lasts[m]})
          self.firsts.pop(m, None)
          self.lasts.pop(m, None)
        
# the main body of the program

# reads lists of OUIs from either a single CSV file or
# all the CSV files in a specified directory; the MAC address is the
# second field of the file, as in standard IEEE OUI lookup exports
def read_oui_list(l):
  if l == None:
    return set()
  maclist = set()
  files = list()

  # we only descend one level into the directory
  try:
    if os.path.isfile(l):
      files.append(l)
    else:
      for f in os.listdir(l):
        pathname = os.path.join(l, f)
        if os.path.isfile(pathname):
          files.append(pathname)

    for filename in files:
      with open(filename, 'r') as f:
        try:
          macreader = csv.DictReader(f)
          for row in macreader:
            maclist.add(row['Assignment'])
        except csv.Error:
          print "Error reading from OUI data file {}.".format(filename)

  except (OSError, IOError) as e:
    print "Error reading OUI data set {}.".format(l)
    maclist = set()
  return maclist
    
if __name__ == '__main__':
  parser = argparse.ArgumentParser(description='Detect the number of nearby wireless devices over time.')
  parser.add_argument('-i', '--interface', metavar='interface', default='wlan0')
  group = parser.add_mutually_exclusive_group()
  group.add_argument('-b', '--blacklist', metavar='blacklist')
  group.add_argument('-w', '--whitelist', metavar='whitelist')
  parser.add_argument('-l', '--logfile', metavar='logfile')
  parser.add_argument('-n', '--numfile', metavar='numfile')
  parser.add_argument('-r', '--rangefile', metavar='rangefile')
  args = parser.parse_args()
  
  sniffer = Sniffer(args.interface, read_oui_list(args.blacklist), read_oui_list(args.whitelist),
                    args.logfile, args.numfile, args.rangefile)
  start_time = time.time()

  try:
    sniffer.start()
    while sniffer.running:
      time.sleep(10)
  finally:
    sniffer.join()

  timestruct = time.localtime(time.time())
  sniffer.log('execution ended')
  if len(sniffer.disallowed_macs) > 0:
    sniffer.log('disallowed MACs seen:')
  for m in sniffer.disallowed_macs:
    sniffer.log(m)

  