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
	MAX_MESSAGE_TYPES //@design this enum is the length of the array of all message types
} message_t;

//mac address is 48 bits (or 6 bytes) until we decide to support EUI-64
#define MAC_SIZE 6
typedef unsigned char mac_t[MAC_SIZE];
//@design string representation of (hashed)mac is 2chars per byte + 1 char for NULL termination
#define MAC_STRING_LEN (MAC_SIZE * 2 + 1)
/* doesn't work in C
 * typedef struct mac {
 * 	char& operator[](int i) { return byte[i]; }
 * 	unsigned char bytes[MAC_SIZE];
 * } mac_t;
 */

//hash key is 256 bits (or 64 bytes) in python hashlib.md5
#define KEY_SIZE 64 //TODO should it be 128? check options in C
typedef unsigned char qubie_key_t[KEY_SIZE];
/* doesn't work in C
 * typedef struct key {
 * 	char& operator[](int i) { return byte[i]; }
 * 	unsigned char bytes[KEY_SIZE];
 * } qubie_key_t;
 */

//frequencies are in increments of 1MHz at least up to 5875MHz (less than 2^16 MHz)
typedef unsigned int frequency_t;

//RSSI is defined between 0-255 though some devices measure on scale of 0-60 or 0-100
//TODO perhaps we need to switch to dBm
typedef unsigned char rssi_t;

//only minimal usage of time is needed. it's enough to count seconds since the epoch
typedef unsigned long qubie_time_t;

// a list of possible qubie states
typedef enum {POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;

typedef struct device_id {
	bool encrypted;
	char const identifier_string[MAC_STRING_LEN];
} device_id_t;

typedef struct contact_record contact_record_t;
typedef struct contact_record {
	device_id_t const device_id;
	const qubie_time_t contact_time;
	const rssi_t rssi;
	const frequency_t frequency;
} contact_record_t;

typedef struct observations {
	unsigned int size;
	//contact_record_t last;
	FILE *observations_fp;

} qubie_observations_t;

typedef struct log_entry {
	 char* message;
	qubie_time_t time;
	message_t message_type;
	void *message_val;
} log_entry_t;

typedef struct qubie_logger {
	unsigned int size;
	log_entry_t* last_entry;
	FILE *log_fp;
}qubie_logger_t;

typedef void* hash_t; //@TODO
typedef struct keyed_hash {
	bool set;
	qubie_key_t *key;
	hash_t hash;
}keyed_hash_t;

typedef struct bt_client bt_client_t;

typedef struct qubie qubie_t;

//@ ensures qubie == Result
qubie_t *get_qubie();

typedef struct wifi_monitor {
	bool wifi_booted;
	bool wifi_running;
	bool auto_hopping;
	keyed_hash_t *keyed_hash;
	const frequency_t *frequency_range;
	frequency_t frequency;
	qubie_t *qubie; //pointer to qubie
} wifi_monitor_t;
//static const char *wifi_state_strings[] = {"booted", "running"};

typedef struct bt_communicator {
	bool subscribed;
	bt_client_t *bt_client;
	qubie_t *qubie;
	state_t const *legal_update_states;
} bt_communicator_t;

typedef struct bt_client {
	bt_communicator_t *bt_communicator; //pointer to qubie's bluetooth communicator
	state_t qubie_state;
}bt_client_t;


typedef struct qubie {
	// qubie status
	state_t state;
	// pointer to qubie's log, a list of log entries with somee added functionality
	qubie_logger_t *log;
	// pointer to qubie's observations, a set of contact records
	qubie_observations_t const observations;
	// pointer to wifi monitor
	wifi_monitor_t *wifi_monitor;
	// pointer to bluetooth communicator
	bt_communicator_t *bt_communicator;
	// "qubie" querie just points to "this" so it is not needed here
	state_t const *legal_update_states;
} qubie_t;
#endif

