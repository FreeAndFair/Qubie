// qubie type and constant definitions

#ifndef QUBIE_TYPES
#define QUBIE_TYPES
#include "qubie_defaults.h"
#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>


typedef enum {
	QUBIE_STATE = 0,
	QUBIE_DETECTED_DEVICE,
	WIFI_MONITOR_STATE,
	WIFI_MONITOR_FREQUENCY,
	WIFI_MONITOR_AUTO_HOPPING,
	WIFI_MONITOR_UNSUPPORTED_PACKET,
	ERROR_MESSAGE,
	MAX_MESSAGE_TYPES //design this enum is the length of the array of all message types
} message_t;

typedef unsigned char byte;
typedef unsigned int uint;

//minimum valid length of radiotap (rtap) header
#define MIN_RTAP_LEN 18
//datalink field value for packets with rtap headers
#define RADIOTAP_DATALINK_VAL 127

//mac address is 48 bits (or 6 bytes) until we decide to support EUI-64
#define MAC_SIZE 6
typedef unsigned char mac_t[MAC_SIZE];
//design string representation of (hashed)mac is 2chars per byte + 1 char for NULL termination
#define MAC_STRING_LEN (MAC_SIZE * 2 + 1)

#define KEY_SIZE 64
typedef unsigned char qubie_key_t[KEY_SIZE];


//frequencies are in increments of 1MHz at least up to 5875MHz (less than 2^16 MHz)
typedef unsigned int frequency_t;

//RSSI is defined between 0-255 though some devices measure on scale of 0-60 or 0-100
typedef unsigned char rssi_t;

/* 	a list of possible qubie states
 	design the order of the states is important.
 	with the exception of POWER_OFF which is a final state and can occur from any other state
 	each state moves to the next state in order
 */
typedef enum {START, POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;

typedef struct device_id {
	bool encrypted; //TBD is this field needed?
	char const identifier_string[MAC_STRING_LEN];
} device_id_t;

typedef struct contact_record {
	device_id_t const device_id;
	const time_t contact_time;
	const rssi_t rssi;
	const frequency_t frequency;
} contact_record_t;

typedef struct observations {
	unsigned int size;
	//contact_record_t last;
	FILE *observations_fp;

} qubie_observations_t;

typedef struct log_entry {
	char const message[MAX_MESSAGE_LEN];
	const time_t time;
} log_entry_t;

typedef struct qubie_logger {
	unsigned int size;
	FILE *log_fp;
}qubie_logger_t;

typedef struct keyed_hash {
	bool set;
	qubie_key_t key;
}keyed_hash_t;

typedef struct bt_client bt_client_t;

typedef struct qubie qubie_t;

typedef struct wifi_monitor {
	bool monitor_booted;
	bool monitor_running;
	bool auto_hopping;
	keyed_hash_t keyed_hash;
	frequency_t const channels[NUM_WIFI_CHANNELS]; // FREQUENCY_WIFI_CHANNELS;
	frequency_t frequency; // WIFI_FREQUENCY_DEFAULT;
} wifi_monitor_t;

typedef struct bt_communicator {
	bool subscribed;
	bt_client_t *bt_client;
	state_t const legal_update_states[2]; //{STOPPED, POWERED_OFF};
} bt_communicator_t;

typedef struct bt_client {
	bt_communicator_t *bt_communicator; //pointer to qubie's bluetooth communicator
	state_t qubie_state;
}bt_client_t;


typedef struct qubie {
	// qubie status
	state_t state;
	// pointer to qubie's log, a list of log entries with somee added functionality
	qubie_logger_t log;
	// pointer to qubie's observations, a set of contact records
	qubie_observations_t observations;
	// pointer to wifi monitor
	wifi_monitor_t wifi_monitor;
	// pointer to bluetooth communicator
	bt_communicator_t bt_communicator;
	state_t const legal_update_states[3]; //{RUNNING, STOPPED, POWERED_OFF};
} qubie_t;
#endif

