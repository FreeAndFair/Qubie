#!/usr/bin/env python

# Polling Queue Monitor Proof of Concept - WiFi Sniffer
# Written by Daniel M. Zimmerman (dmz@galois.com)
# Copyright (C) 2015 Galois, Inc.

import argparse
import binascii
import csv
import hashlib
import hmac
import netifaces
import os
import pcapy
import random
import re
import signal
import struct
import subprocess
import sys
import threading
import time
from exceptions import OSError

# SYMBOLIC CONSTANTS

# the interval at which the proximity statistics will be updated
UPDATE_INTERVAL = 60

# the interval between sightings of a device before that device is
# considered to be out of proximity
PROXIMITY_TIMEOUT = 31 * 60

# the maximum number of bytes to capture per packet
MAX_CAPTURE_BYTES_PER_PACKET = 1514

# the timeout on capturing a single packet
CAPTURE_TIMEOUT = 0

# the amount of time to stay on each channel, if scanning
SCAN_CHANNEL_TIME = 5

# BTLE main JavaScript file
BTLE_SCRIPT = 'btle.js'

# our network address, filled in after command line argument parsing
NETWORK_ADDRESS = None

# class Logger - logs output to a file
class Logger():
  def __init__(self, logfile):
    # initialize variables

    self.logfile = None
    if logfile != None:
      try:
        self.logfile = open(args.logfile, 'a', 1)
        self.logfile.write('\n---ID {} STARTING NEW RUN---\n'.format(NETWORK_ADDRESS))
      except IOError:
        print('could not open log file {}, proceeding with no log file'.format(logfile))
        self.logfile = None

  # log a message, to either the console or the log file
  def log(self, msg):
    timestamp = time.strftime('[%Y-%m-%d %H:%M:%S %Z]',
                              time.localtime(time.time()))
    entry = '{}: {}'.format(timestamp, msg)
    if self.logfile != None:
      self.logfile.write(entry)
      self.logfile.write('\n')

    else:
      print entry

  # flushes the logfile (if any)
  def flush(self):
    if self.logfile != None:
      self.logfile.flush()
      os.fsync(self.logfile)

# class BTLE - interfaces to a Bluetooth Low Energy service
# to provide basic runtime information

class BTLE():
  def __init__(self, logger):
    # initialize variables
    self.logger = logger
    self.btleproc = subprocess.Popen(['node', BTLE_SCRIPT], stdin=subprocess.PIPE)
    logger.log('started btle service')


# class Scanner - switches the wifi channel on the specified interface among
# the specified list of channels to scan, continuously, until told to stop
class Scanner(threading.Thread):
  def __init__(self, args, logger):
    super(Scanner, self).__init__()

    # initialize variables
    self.scanchannels = args.scanchannels
    self.interface = args.interface
    self.logger = logger
    self.running = False

  # the run method for this thread
  def run(self):
    # if we don't need to scan, we don't need to run
    if not self.scanchannels:
      return

    # attempt to create the channel list
    channel_list = []
    try:
      listproc = subprocess.Popen(['iwlist', self.interface, 'channel'], stdout=subprocess.PIPE)
      for line in listproc.communicate()[0].split('\n'):
        if 'Channel' in line and not 'Frequency' in line:
          channel_list.append(re.findall(r'\d+', line)[0])
    except:
      logger.log('error getting wifi channel list, not scanning')
      return
    logger.log('available wifi channels: {}'.format(channel_list))
    
    # with more than 1 channel, we scan in the order provided
    self.running = True
    while (self.running):
      for channel in channel_list:
        try:
          subprocess.call(['iwconfig', self.interface, 'channel', channel])
          logger.log('wifi switched to channel {}'.format(channel))
        except:
          logger.log('wifi could not switch to channel {}'.format(channel))
        time.sleep(SCAN_CHANNEL_TIME)
        if not self.running:
          break

  # the stop method for this thread
  def stop(self):
    self.running = False

# class Sniffer - extends Thread and runs the actual sniffing, including
# tracking of devices in proximity and statistics about their presence/absence
class Sniffer(threading.Thread):
  def __init__(self, args, logger, btle):
    super(Sniffer, self).__init__()
    
    # initialize signal handler
    signal.signal(signal.SIGINT, self.signaled)
    signal.signal(signal.SIGTERM, self.signaled)
    
    # initialize variables
    self.logger = logger
    self.btle = btle
    self.firsts = {}
    self.lasts = {}
    self.min_rssis = {}
    self.max_rssis = {}
    self.hashes = {}
    self.disallowed_macs = set()
    self.locally_managed_macs = set()
    self.last_update = time.time()
    self.running = False
    self.interface = args.interface
    self.blacklist = read_oui_list(args.blacklist)
    self.whitelist = read_oui_list(args.whitelist)
    self.using_whitelist = len(self.whitelist) > 0

    logger.log('started listening on interface {}'.format(self.interface))
    if self.using_whitelist:
      logger.log('whitelist contains {} OUIs'.format(len(self.whitelist)))
    elif len(self.blacklist) > 0:
      logger.log('blacklist contains {} OUIs'.format(len(self.blacklist)))
    else:
      logger.log('accepting all OUIs')
    
    self.countfile = None
    self.countwriter = None
    if args.countfile != None:
      try:
        self.countfile = open(args.countfile, 'w', 1)
        self.countwriter = csv.DictWriter(self.countfile, fieldnames=['time', 'num_devices'])
        self.countwriter.writeheader()
      except IOError:
        logger.log('could not device count file {}, proceeding without it'.format(numfile))
        self.countfile = None
      
    self.rangefile = None
    self.rangewriter = None
    if args.rangefile != None:
      try:
        self.rangefile = open(args.rangefile, 'w', 1)
        self.rangewriter = csv.DictWriter(self.rangefile,
                                          fieldnames=['device', 'start_time', 'end_time', 'min_rssi', 'max_rssi'])
        self.rangewriter.writeheader()
      except IOError:
        logger.log('could not open device presence time range file {}, proceeding without it'.format(rangefile))
        self.rangefile = None
          
    self.contactfile = None
    self.contactwriter = None
    if args.contactfile != None:
      try:
        self.contactfile = open(args.contactfile, 'w', 1)
        self.contactwriter = csv.DictWriter(self.contactfile,
                                            fieldnames=['device', 'time', 'rssi', 'frequency'])
        self.contactwriter.writeheader()
      except IOError:
        logger.log('could not open contact file {}, proceeding without it'.format(contactfile))
        self.contactfile = None

    self.hashfile = None
    self.hashwriter = None
    if args.hashfile != None:
      try:
        self.hashfile = open(args.hashfile, 'w', 1)
        self.hashwriter = csv.DictWriter(self.hashfile,
                                         fieldnames=['mac', 'hash', 'locally_managed', 'disallowed'])
        self.hashwriter.writeheader()
      except IOError:
        logger.log('could not open device hash file {}, proceeding without it'.format(hashfile))
        self.hashfile = None

    self.encrypted = args.encrypted
    self.key = ''
    if self.encrypted:
      self.key = '%064x' % random.SystemRandom().getrandbits(256)
      logger.log('generated key for MAC address hashing')

    self.mindelay = args.mindelay
      
  # the run method for this thread
  def run(self):
    self.running = True
    while self.running:
      try:
        cap = pcapy.open_live(self.interface, MAX_CAPTURE_BYTES_PER_PACKET,
                              True, CAPTURE_TIMEOUT)
        if cap.datalink() != 0x7F:  # 0x7F == 127 == RadioTap
          logger.log('error: data link type is {}, expected 127 (RadioTap)'.format(cap.datalink()))
          self.running = False
          break
        while self.running:
          (header, pkt) = cap.next()
          self.sniff_packet(pkt)
      except OSError as e:
        logger.log('error {}: {}'.format(e.errno, e.strerror))
        logger.log('waiting 10 seconds')
        time.sleep(10)
      except pcapy.PcapError:
        logger.log('error: {}'.format(sys.exc_info()[1]))
        logger.log('waiting 10 seconds')
        time.sleep(10)
      except:
        logger.log('unexpected error: {}'.format(sys.exc_info()))
        self.running = False

    logger.log('shutting down')
    
    for m in sorted(self.firsts.keys()):
      logger.log('mac {} present for {} minutes at shutdown, min RSSI {}, max RSSI {}'.
               format(m, int((self.lasts[m] - self.firsts[m]) // 60),
                      self.min_rssis[m], self.max_rssis[m]))
      if self.rangewriter != None:
        self.rangewriter.writerow({'device': m,
                                   'start_time': self.firsts[m],
                                   'end_time': self.lasts[m],
                                   'min_rssi': self.min_rssis[m],
                                   'max_rssi': self.max_rssis[m]})
      self.firsts.pop(m, None)
      self.lasts.pop(m, None)

    if self.countfile != None:
      self.countfile.flush()
      os.fsync(self.countfile)
    if self.rangefile != None:
      self.rangefile.flush()
      os.fsync(self.rangefile)

  # the method to be called when this thread is signaled
  def signaled(self, signum, frame):
    logger.log('received signal {}, calling for shutdown'.format(signum))
    self.stop()
  
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
  
  # updates our list of devices in proximity, based on the specified
  # packet being received
  def sniff_packet(self, p):
    rtlen = struct.unpack('h', p[2:4])[0]

    # check for bad RadioTap headers
    if rtlen < 18:
      return
    
    rtap = p[:rtlen]
    frequency = (struct.unpack("I", rtap[-8:-4])[0] & 0x0000FFFF)

    # check for bad frequencies
    if frequency < 2400 or frequency > 6000:
      return
        
    rssi = struct.unpack("b", rtap[-4:-3])[0]
    frame = p[rtlen:]
    mac = frame[10:16].encode('hex')

    # check for bad "mac" addresses
    if len(mac) < 12:
      return

    capture_time = time.time()
    
    # if we're running in encrypted mode, we need to hash the MAC;
    # otherwise, we just use it as is
    hashed_mac = mac
    disallowed = self.disallowed(mac)
    locally_managed = ord(frame[10]) & 0x02 > 0
    
    if self.encrypted:
      if not mac in self.hashes:
        mac_hmac = hmac.new(self.key, mac, hashlib.md5)
        hashed_mac = mac_hmac.hexdigest()
        self.hashes[mac] = hashed_mac
        if self.hashwriter != None:
          logger.log('hashed mac {} to {}'.format(mac, hashed_mac))
          self.hashwriter.writerow({'mac': mac,
                                    'hash': self.hashes[mac],
                                    'locally_managed': locally_managed,
                                    'disallowed': disallowed})
      hashed_mac = self.hashes[mac]
      
    if locally_managed:
      if not hashed_mac in self.locally_managed_macs:
        self.locally_managed_macs.add(hashed_mac)
        logger.log('locally-managed device {} appeared'.format(hashed_mac))
    elif disallowed:
      if not hashed_mac in self.disallowed_macs:
        self.disallowed_macs.add(hashed_mac)
        logger.log('disallowed device {} appeared'.format(hashed_mac))
      allowed = False
    elif hashed_mac not in self.firsts:
      logger.log('device {} appeared, RSSI {} dBm, frequency {} MHz'.
                 format(hashed_mac, rssi, frequency))
      if self.contactwriter != None:
        self.contactwriter.writerow({'device': hashed_mac,
                                     'time': capture_time,
                                     'rssi': rssi,
                                     'frequency': frequency})
      self.firsts[hashed_mac] = capture_time
      self.min_rssis[hashed_mac] = rssi
      self.max_rssis[hashed_mac] = rssi
    elif (capture_time - self.lasts[hashed_mac] >= self.mindelay):
      first_timestruct = time.localtime(self.firsts[hashed_mac])
      if self.contactwriter != None:
        self.contactwriter.writerow({'device': hashed_mac,
                                     'time': capture_time,
                                     'rssi': rssi,
                                     'frequency': frequency})
      logger.log('device {} has been here {} minutes, RSSI {} dBm, frequency {} MHz'.
                 format(hashed_mac, int((capture_time - self.firsts[hashed_mac]) // 60),
                        rssi, frequency))
    
    if not locally_managed and not disallowed:
      self.lasts[hashed_mac] = capture_time
      if rssi < self.min_rssis[hashed_mac]:
        self.min_rssis[hashed_mac] = rssi
      if self.max_rssis[hashed_mac] < rssi:
        self.max_rssis[hashed_mac] = rssi

    # do a list update
    self.update_device_lists()


  # update the lists of devices in proximity based on our
  # update and timeout intervals
  def update_device_lists(self):
    if (time.time() - self.last_update > UPDATE_INTERVAL):
      self.last_update = time.time()
      timestruct = time.localtime(self.last_update)
      if self.countwriter != None:
        self.countwriter.writerow({'time': int(round(self.last_update -
                                                     start_time)) / 60,
                                   'num_devices': len(self.firsts)})
      logger.log('{} devices assumed to be present'.format(len(self.firsts)))
      for m in sorted(self.firsts.keys()):
        if time.time() - self.lasts[m] > PROXIMITY_TIMEOUT:
          logger.log('mac {} disappeared after {} minutes, min RSSI {}, max RSSI {}'.
                     format(m, int((self.lasts[m] - self.firsts[m]) // 60),
                            self.min_rssis[m], self.max_rssis[m]))
          if self.rangewriter != None:
            self.rangewriter.writerow({'device': m,
                                       'start_time': self.firsts[m],
                                       'end_time': self.lasts[m],
                                       'min_rssi': self.min_rssis[m],
                                       'max_rssi': self.max_rssis[m]})
          self.firsts.pop(m, None)
          self.lasts.pop(m, None)
          self.min_rssis.pop(m, None)
          self.max_rssis.pop(m, None)

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
            maclist.add(row['Assignment'].lower())
        except csv.Error:
          print "Error reading from OUI data file {}.".format(filename)

  except (OSError, IOError) as e:
    print "Error reading OUI data set {}.".format(l)
    maclist = set()
  return maclist
    
if __name__ == '__main__':
  # parse the command line
  parser = argparse.ArgumentParser(description='Detect the number of nearby wireless devices over time.')
  parser.add_argument('-i', '--interface', metavar='interface', default='wlan0')
  group = parser.add_mutually_exclusive_group()
  group.add_argument('-b', '--blacklist', metavar='blacklist',
                     help='path to the OUI blacklist file or directory')
  group.add_argument('-w', '--whitelist', metavar='whitelist',
                     help='path to the OUI whitelist file or directory')
  parser.add_argument('-l', '--logfile', metavar='logfile',
                      help='path to the log output file')
  parser.add_argument('-c', '--countfile', metavar='countfile',
                      help='path to the device count output file')
  parser.add_argument('-r', '--rangefile', metavar='rangefile',
                      help='path to the device presence time range output file')
  parser.add_argument('-C', '--contactfile', metavar='contactfile',
                      help='path to the device contact output file')
  parser.add_argument('-H', '--hashfile', metavar='hashfile',
                      help='path to the device MAC hash output file')
  parser.add_argument('-e', '--encrypted', action='store_true',
                      help='encrypt the detected MAC addresses')
  parser.add_argument('-m', '--mindelay', metavar='mindelay', type=int, default=0,
                      help='minimum number of seconds between recording contacts from the same device')
  parser.add_argument('-s', '--scanchannels', action='store_true',
                      help='scan all wifi channels (boolean)')
  parser.add_argument('-B', '--bluetooth', action='store_true',
                      help='broadcast a Bluetooth LE service with status updates')
  args = parser.parse_args()
  
  # create our logger
  logger = Logger(args.logfile)

  # get our network address
  try:
    raw_network_address = netifaces.ifaddresses(args.interface)[netifaces.AF_LINK][0]['addr']
    NETWORK_ADDRESS = raw_network_address.replace(":","")
    logger.log('network address is {}'.format(NETWORK_ADDRESS))
  except:
    NETWORK_ADDRESS = 'ffffffffffff'
    logger.log('could not get network address, using default')

  btle = None
  if args.bluetooth:
    try:
      btle = BTLE(logger)
    except:
      btle = None
      logger.log('error starting btle service, proceeding without it')
  sniffer = Sniffer(args, logger, btle)
  scanner = Scanner(args, logger)

  # start running
  start_time = time.time()
  try:
    sniffer.start()
    scanner.start()
    while sniffer.running:
      time.sleep(10)
  finally:
    sniffer.stop()
    scanner.stop()
    if btle != None:
      btle.stop()
    sniffer.join()
    scanner.join()

  timestruct = time.localtime(time.time())
  logger.log('execution ended')
  if len(sniffer.disallowed_macs) > 0:
    logger.log('disallowed MACs seen:')
  for m in sniffer.disallowed_macs:
    logger.log(m)
