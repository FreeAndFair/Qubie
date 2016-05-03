// Qubie Proof-of-Concept Bluetooth Low Energy Status Updates
// Written by Daniel M. Zimmerman (dmz@freeandfair.us)
// Copyright (C) 2016 Free & Fair

var util = require('util');
var bleno = require('bleno');
var readline = require('readline');

const UUID = '66726565616e64666169727175626965'; // freeandfairqubie

// the BTLE characteristic that we use to advertise our status
var statusUpdateCharacteristic = new bleno.Characteristic({
  uuid: UUID,
  properties: ['read', 'notify'],
  value: null,
  onReadRequest: function(offset, callback) {
    callback(this.RESULT_SUCCESS, this._value);
  },
  onSubscribe: function(maxValueSize, updateValueCallback) {
    this._updateValueCallback = updateValueCallback;
  },
  onUnsubscribe: function() {
    this._updateValueCallback = null;
  }
});

statusUpdateCharacteristic._value = new Buffer("initializing");

// the primary Bluetooth LE service
var primaryService = new bleno.PrimaryService({
  uuid: UUID,
  characteristics: [ statusUpdateCharacteristic ]
});

// our console reader
var rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout,
  terminal: false
});

// set up the Bluetooth LE advertising service
bleno.on('advertisingStart', function(error) {
  if (!error) {
    bleno.setServices([primaryService]);
  } else {
    console.log(error);
  }
});

bleno.on('stateChange', function(state) {
  if (state === 'poweredOn') {
    bleno.startAdvertising("Qubie", UUID);
    poweredOn = true;
  } else {
    bleno.stopAdvertising();
  }
});

// read lines from standard input
// the first line is used in our identifier string
// each subsequent line is a data update
rl.on('line', (data) => { 
  buffer = new Buffer(data, 'utf8')
  statusUpdateCharacteristic._value = buffer
  callback = statusUpdateCharacteristic._updateValueCallback;
  if (callback != null) {
    callback(buffer);
  }
});
