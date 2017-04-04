#!/usr/bin/env python

"""
    Qubie Proof-of-Concept Passive WiFi Monitor
    Written by Daniel M. Zimmerman (dmz@freeandfair.us)
    Copyright (C) 2016 Free & Fair
"""

import argparse
import csv
import hashlib
import hmac
import os
import random
import re
import signal
import struct
import subprocess
import sys
import threading
import time

import netifaces
import pcapy

# SYMBOLIC CONSTANTS

UPDATE_INTERVAL = 60
""" The interval at which the proximity statistics will be updated. """

PROXIMITY_TIMEOUT = 31 * 60
"""
    The interval between sightings of a device before that device is
    considered to be out of proximity.
"""

MAX_CAPTURE_BYTES_PER_PACKET = 1514
""" The maximum number of bytes to capture per packet. """

CAPTURE_TIMEOUT = 0
""" The timeout on capturing a single packet. """

SCAN_CHANNEL_TIME = 5
""" The amount of time to stay on each channel, if scanning. """

BTLE_SCRIPT = './qubie_btle'
""" The main JavaScript file for Bluetooth Low Energy support. """

NETWORK_ADDRESS = None
""" Our network address, filled in after command line argument parsing. """


class Logger(object):
    """ Log output to a file or, if no file is provided, to standard error. """

    def __init__(self, logfile):
        """
            Initialize a new logger.

            Args:
                logfile (str): The fully-qualified pathname to a log file.
        """
        self.logfile = None
        if logfile is not None:
            try:
                self.logfile = open(args.logfile, 'a', 1)
                self.logfile.write('\n---ID {} STARTING NEW RUN---\n'.format(NETWORK_ADDRESS))
            except IOError:
                print 'could not open log file {}, proceeding with no log file'.format(logfile)
                self.logfile = None

    def log(self, msg):
        """
            Log a message.

            Args:
                msg (str): The message to log.
        """
        timestamp = time.strftime('[%Y-%m-%d %H:%M:%S %Z]',
                                  time.localtime(time.time()))
        entry = '{}: {}'.format(timestamp, msg)
        if self.logfile is not None:
            self.logfile.write(entry)
            self.logfile.write('\n')

        else:
            print entry

    def flush(self):
        """ Flush the log file, if one is being used. """

        if self.logfile is not None:
            self.logfile.flush()
            os.fsync(self.logfile)

    def stop(self):
        """ Stop logging and close the log file, if one is being used. """
        if self.logfile is not None:
            self.logfile.write('---ID {} ENDING RUN---\n'.format(NETWORK_ADDRESS))
            self.logfile.close()


class BTLE(object):
    """ Interface to a Bluetooth Low Energy support script (written in node.js). """

    def __init__(self, the_logger):
        """
            Initialize the Bluetooth Low Energy support.

            Args:
                the_logger (Logger): The logger to record status updates with.
        """
        self.logger = the_logger
        self.btleproc = subprocess.Popen([BTLE_SCRIPT, NETWORK_ADDRESS],
                                         stdin=subprocess.PIPE, bufsize=1)
        self.logger.log('started btle service')

    def update(self, updatemsg):
        """ Update the Bluetooth Low Energy broadcast message to the specified string. """
        try:
            print >> self.btleproc.stdin, '{}'.format(updatemsg)
        except Exception as exc:
            logger.log('error updating btle service: {}'.format(exc))

    def stop(self):
        """ Stop the Bluetooth Low Energy service. """
        self.btleproc.terminate()


class Scanner(threading.Thread):
    """ Continuously scan WiFi channels on the sniffing interface. """

    def __init__(self, the_args, the_logger):
        """
            Initialize the WiFi scanner.

            Args:
                the_args (Namespace): The parsed command line arguments. The
                    arguments used here are "scanchannels" and "interface".
                the_logger (Logger): The logger to record status updates with.
        """
        super(Scanner, self).__init__()

        # initialize variables
        self.scanchannels = the_args.scanchannels
        self.interface = the_args.interface
        self.logger = the_logger
        self.running = False

    def run(self):
        """
            Start the thread to continuously scan WiFi channels, switching at interval
            SCAN_CHANNEL_TIME.
        """
        # if we don't need to scan, we don't need to run
        if not self.scanchannels:
            return

        # attempt to create the channel list
        channel_list = []
        try:
            listproc = subprocess.Popen(['iwlist', self.interface, 'channel'],
                                        stdout=subprocess.PIPE, bufsize=1)
            for line in listproc.communicate()[0].split('\n'):
                if 'Channel' in line and 'Frequency' not in line:
                    channel_list.append(re.findall(r'\d+', line)[0])
        except:
            logger.log('error getting wifi channel list, not scanning')
            return
        logger.log('available wifi channels: {}'.format(channel_list))

        # with more than 1 channel, we scan in the order provided
        self.running = True
        while self.running:
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
        """ Stop scanning WiFi channels (and stop the thread). """
        self.running = False


class Sniffer(threading.Thread):
    """ Sniff for packets on a WiFi interface and record information about them. """

    def __init__(self, the_args, the_logger, the_btle):
        """
            Initialize the WiFi sniffer.

            Args:
                the_args (Namespace): the parsed command line arguments. The
                    arguments used here are "interface", "blacklist", "whitelist",
                    "countfile", "rangefile", "contactfile", "hashfile", and
                    "encrypted".
                the_logger (Logger): the logger to record status updates with.
                the_btle (BTLE): the Bluetooth Low Energy interface to use.
        """
        super(Sniffer, self).__init__()

        # initialize signal handler
        signal.signal(signal.SIGINT, self.signaled)
        signal.signal(signal.SIGTERM, self.signaled)

        # initialize variables
        self.logger = the_logger
        self.btle = the_btle
        self.firsts = {}
        self.lasts = {}
        self.min_rssis = {}
        self.max_rssis = {}
        self.hashes = {}
        self.disallowed_macs = set()
        self.locally_managed_macs = set()
        self.last_update = time.time()
        self.running = False
        self.interface = the_args.interface
        self.blacklist = read_oui_list(the_args.blacklist)
        self.whitelist = read_oui_list(the_args.whitelist)
        self.using_whitelist = len(self.whitelist) > 0

        the_logger.log('started listening on interface {}'.format(self.interface))
        if self.using_whitelist:
            the_logger.log('whitelist contains {} OUIs'.format(len(self.whitelist)))
        elif len(self.blacklist) > 0:
            the_logger.log('blacklist contains {} OUIs'.format(len(self.blacklist)))
        else:
            the_logger.log('accepting all OUIs')

        self.countfile = None
        self.countwriter = None
        if the_args.countfile is not None:
            try:
                self.countfile = open(the_args.countfile, 'w', 1)
                self.countwriter = csv.DictWriter(self.countfile,
                                                  fieldnames=['time', 'num_devices', 'min_duration',
                                                              'max_duration', 'avg_duration'])
                self.countwriter.writeheader()
            except IOError:
                the_logger.log('could not device count file {}, proceeding without it'.
                               format(the_args.numfile))
                self.countfile = None

        self.rangefile = None
        self.rangewriter = None
        if the_args.rangefile is not None:
            try:
                self.rangefile = open(the_args.rangefile, 'w', 1)
                self.rangewriter = csv.DictWriter(self.rangefile,
                                                  fieldnames=['device', 'start_time', 'end_time',
                                                              'min_rssi', 'max_rssi'])
                self.rangewriter.writeheader()
            except IOError:
                the_logger.log(
                    'could not open device presence time range file {}, proceeding without it'.
                    format(the_args.rangefile))
                self.rangefile = None

        self.contactfile = None
        self.contactwriter = None
        if the_args.contactfile is not None:
            try:
                self.contactfile = open(the_args.contactfile, 'w', 1)
                self.contactwriter = csv.DictWriter(self.contactfile,
                                                    fieldnames=['device', 'time', 'rssi',
                                                                'frequency'])
                self.contactwriter.writeheader()
            except IOError:
                the_logger.log('could not open contact file {}, proceeding without it'.
                               format(the_args.contactfile))
                self.contactfile = None

        self.hashfile = None
        self.hashwriter = None
        if the_args.hashfile is not None:
            try:
                self.hashfile = open(the_args.hashfile, 'w', 1)
                self.hashwriter = csv.DictWriter(self.hashfile,
                                                 fieldnames=['mac', 'hash', 'locally_managed',
                                                             'disallowed'])
                self.hashwriter.writeheader()
            except IOError:
                the_logger.log('could not open device hash file {}, proceeding without it'.
                               format(the_args.hashfile))
                self.hashfile = None

        self.encrypted = the_args.encrypted
        self.key = ''
        if self.encrypted:
            self.key = '%064x' % random.SystemRandom().getrandbits(256)
            the_logger.log('generated key for MAC address hashing')

        self.mindelay = the_args.mindelay

    def run(self):
        """ Start sniffing for packets on the WiFi interface. """
        self.running = True
        while self.running:
            try:
                cap = pcapy.open_live(self.interface, MAX_CAPTURE_BYTES_PER_PACKET,
                                      True, CAPTURE_TIMEOUT)
                if cap.datalink() != 0x7F:  # 0x7F == 127 == RadioTap
                    logger.log('error: data link type is {}, expected 127 (RadioTap)'.
                               format(cap.datalink()))
                    self.running = False
                    break
                while self.running:
                    (_, pkt) = cap.next()
                    self.sniff_packet(pkt)
            except OSError as exc:
                logger.log('error {}: {}'.format(exc.errno, exc.strerror))
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
        if self.btle is not None:
            self.btle.update('shutting down')

        for mac in sorted(self.firsts.keys()):
            logger.log('mac {} present for {} minutes at shutdown, min RSSI {}, max RSSI {}'.
                       format(mac, int((self.lasts[mac] - self.firsts[mac]) // 60),
                              self.min_rssis[mac], self.max_rssis[mac]))
            if self.rangewriter is not None:
                self.rangewriter.writerow({'device': mac,
                                           'start_time': self.firsts[mac],
                                           'end_time': self.lasts[mac],
                                           'min_rssi': self.min_rssis[mac],
                                           'max_rssi': self.max_rssis[mac]})
            self.firsts.pop(mac, None)
            self.lasts.pop(mac, None)

        if len(sniffer.disallowed_macs) > 0:
            logger.log('{} disallowed devices seen'.format(len(sniffer.disallowed_macs)))

        if self.countfile is not None:
            self.countfile.flush()
            os.fsync(self.countfile)
        if self.rangefile is not None:
            self.rangefile.flush()
            os.fsync(self.rangefile)

    def signaled(self, the_signum, _):
        """
            Handle a signal from the operating system.

            Args:
                the_signum (int): The signal number.
                _: The signal frame (ignored, but required by signal API).
        """
        logger.log('received signal {}, calling for shutdown'.format(the_signum))
        self.stop()

    def stop(self):
        """ Stop sniffing for packets. """
        self.running = False

    def disallowed(self, mac):
        """
            Determine whether a MAC prefix is disallowed. A MAC prefix on the blacklist
            is always disallowed, a MAC prefix on the whitelist is always allowed, and a
            MAC prefix on neither list is allowed if the blacklist is being used and
            disallowed if the whitelist is being used; note that only one of the whitelist
            and blacklist can be used at a time.

            Args:
                mac (str): The MAC prefix to check.
        """
        if mac[:6] in self.blacklist:
            return True
        if mac[:6] in self.whitelist:
            return False
        return self.using_whitelist

    def sniff_packet(self, the_packet):
        """ Unpack and record a single sniffed packet. """
        rtlen = struct.unpack('h', the_packet[2:4])[0]

        # check for bad RadioTap headers
        if rtlen < 18:
            return

        rtap = the_packet[:rtlen]
        frequency = (struct.unpack("I", rtap[-8:-4])[0] & 0x0000FFFF)

        # check for bad frequencies
        if frequency < 2400 or frequency > 6000:
            return

        rssi = struct.unpack("b", rtap[-4:-3])[0]
        frame = the_packet[rtlen:]
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
            if mac not in self.hashes:
                mac_hmac = hmac.new(self.key, mac, hashlib.md5)
                hashed_mac = mac_hmac.hexdigest()
                self.hashes[mac] = hashed_mac
                if self.hashwriter is not None:
                    logger.log('hashed mac {} to {}'.format(mac, hashed_mac))
                    self.hashwriter.writerow({'mac': mac,
                                              'hash': self.hashes[mac],
                                              'locally_managed': locally_managed,
                                              'disallowed': disallowed})
            hashed_mac = self.hashes[mac]

        if locally_managed:
            if hashed_mac not in self.locally_managed_macs:
                self.locally_managed_macs.add(hashed_mac)
                logger.log('locally-managed device {} appeared'.format(hashed_mac))
        elif disallowed:
            if hashed_mac not in self.disallowed_macs:
                self.disallowed_macs.add(hashed_mac)
                logger.log('disallowed device {} appeared'.format(hashed_mac))
        elif hashed_mac not in self.firsts:
            logger.log('device {} appeared, RSSI {} dBm, frequency {} MHz'.
                       format(hashed_mac, rssi, frequency))
            if self.contactwriter is not None:
                self.contactwriter.writerow({'device': hashed_mac,
                                             'time': capture_time,
                                             'rssi': rssi,
                                             'frequency': frequency})
            self.firsts[hashed_mac] = capture_time
            self.min_rssis[hashed_mac] = rssi
            self.max_rssis[hashed_mac] = rssi
        elif capture_time - self.lasts[hashed_mac] >= self.mindelay:
            if self.contactwriter is not None:
                self.contactwriter.writerow({'device': hashed_mac,
                                             'time': capture_time,
                                             'rssi': rssi,
                                             'frequency': frequency})
            logger.log('device {} has been here {} minutes, RSSI {} dBm, frequency {} MHz'.
                       format(hashed_mac,
                              int((capture_time - self.firsts[hashed_mac]) // 60),
                              rssi,
                              frequency))

        if not locally_managed and not disallowed:
            self.lasts[hashed_mac] = capture_time
            if rssi < self.min_rssis[hashed_mac]:
                self.min_rssis[hashed_mac] = rssi
            if self.max_rssis[hashed_mac] < rssi:
                self.max_rssis[hashed_mac] = rssi

        # do a list update
        self.update_device_lists()

    def update_device_lists(self):
        """ Update the list of devices in proximity based on our update and timeout intervals. """
        current_time = time.time()
        if current_time - self.last_update > UPDATE_INTERVAL:
            self.last_update = current_time
            for mac in sorted(self.firsts.keys()):
                if current_time - self.lasts[mac] > PROXIMITY_TIMEOUT:
                    logger.log('mac {} disappeared after {} minutes, min RSSI {}, max RSSI {}'.
                               format(mac, int((self.lasts[mac] - self.firsts[mac]) // 60),
                                      self.min_rssis[mac], self.max_rssis[mac]))
                    if self.rangewriter is not None:
                        self.rangewriter.writerow({'device': mac,
                                                   'start_time': self.firsts[mac],
                                                   'end_time': self.lasts[mac],
                                                   'min_rssi': self.min_rssis[mac],
                                                   'max_rssi': self.max_rssis[mac]})
                    self.firsts.pop(mac, None)
                    self.lasts.pop(mac, None)
                    self.min_rssis.pop(mac, None)
                    self.max_rssis.pop(mac, None)

            accum = 0
            max_wait = 0
            min_wait = float('inf')
            for mac in self.firsts.keys():
                wait = self.lasts[mac] - self.firsts[mac]
                accum = accum + wait
                if wait < min_wait:
                    min_wait = wait
                if max_wait < wait:
                    max_wait = wait
            avg = accum / len(self.firsts)

            if self.countwriter is not None:
                self.countwriter.writerow({'time': int(round(self.last_update - start_time)) / 60,
                                           'num_devices': len(self.firsts),
                                           'min_duration': min_wait,
                                           'max_duration': max_wait,
                                           'avg_duration': avg})

            logger.log('{} devices assumed to be present'.format(len(self.firsts)))
            logger.log('wait durations: {} min, {} max, {} avg'.format(int(min_wait // 60),
                                                                       int(max_wait // 60),
                                                                       int(avg // 60)))
            if self.btle is not None:
                btle.update('{} devices: {} min, {} max, {} avg'.format(len(self.firsts),
                                                                        int(min_wait // 60),
                                                                        int(max_wait // 60),
                                                                        int(avg // 60)))


# the main body of the program

def read_oui_list(the_list):
    """ Read lists of OUIs from either a single CSV file or all the CSV files in a
        specified directory; the MAC address is the second field of the file, as in
        standard IEEE OUI lookup exports.

        Args:
            the_list (List[str]): The OUI list.
    """
    if the_list is None:
        return set()
    maclist = set()
    files = list()

    # we only descend one level into the directory
    try:
        if os.path.isfile(the_list):
            files.append(the_list)
        else:
            for filename in os.listdir(the_list):
                pathname = os.path.join(the_list, filename)
                if os.path.isfile(pathname):
                    files.append(pathname)

        for path in files:
            with open(path, 'r') as dictionary:
                try:
                    macreader = csv.DictReader(dictionary)
                    for row in macreader:
                        maclist.add(row['Assignment'].lower())
                except csv.Error:
                    print "Error reading from OUI data file {}.".format(path)

    except (OSError, IOError):
        print "Error reading OUI data set {}.".format(the_list)
        maclist = set()
    return maclist


if __name__ == '__main__':
    # parse the command line
    parser = argparse.ArgumentParser\
        (description='Detect the number of nearby wireless devices over time.')
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
                        help='minimum number of seconds between recording contacts '
                        'from the same device')
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
        NETWORK_ADDRESS = raw_network_address.replace(":", "")
        logger.log('network address is {}'.format(NETWORK_ADDRESS))
    except:
        NETWORK_ADDRESS = 'ffffffffffff'
        logger.log('could not get network address, using default')

    btle = None
    if args.bluetooth:
        try:
            btle = BTLE(logger)
        except Exception as exc:
            btle = None
            logger.log('error starting btle service ({}), proceeding without it'.format(exc))
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
        if btle is not None:
            btle.stop()
        sniffer.join()
        scanner.join()

    timestruct = time.localtime(time.time())
    logger.stop()
