// qubie type and constant definitions

#include <stddef.h>
#include <stdbool.h>
#ifndef QUBIE_TYPES
#define QUBIE_TYPES
typedef enum {
	QUBIE_STATE,
	QUBIE_CONTACT_RECORD,
	WIFI_MONITOR_STATE,
	WIFI_MONITOR_FREQUENCY,
	WIFI_MONITOR_AUTO_HOPPING,
	WIFI_MONITOR_DETECTED_DEVICE
} message_t;

//mac address is 48 bits (or 6 bytes) until we decide to support EUI-64
#define MAC_SIZE 6
typedef unsigned char mac_t[MAC_SIZE];
/* doesn't work in C
 * typedef struct mac {
 * 	char& operator[](int i) { return byte[i]; }
 * 	unsigned char bytes[MAC_SIZE];
 * } mac_t;
 */

//hash key is 256 bits (or 64 bytes) in python hashlib.md5
#define KEY_SIZE 64 //TODO should it be 128? check options in C
typedef unsigned char key_t[KEY_SIZE];
/* doesn't work in C
 * typedef struct key {
 * 	char& operator[](int i) { return byte[i]; }
 * 	unsigned char bytes[KEY_SIZE];
 * } key_t;
 */

//frequencies are in increments of 1MHz at least up to 5875MHz (less than 2^16 MHz)
typedef unsigned int frequency_t;

//RSSI is defined between 0-255 though some devices measure on scale of 0-60 or 0-100
//TODO perhaps we need to switch to dBm
typedef char rssi_t;

//only minimal usage of time is needed. it's enough to count seconds since the epoch
typedef unsigned long time_t;

// a list of possible qubie states
typedef enum {POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;
static const char *state_strings[] = {"powered on", "booting", "running", "stopped", "powered off"};

typedef struct device_id {
	const bool encrypted;
	const mac_t identifier_string;
} device_id_t;

typedef struct contact_record {
	const device_id_t device_id;
	const time_t contact_time;
	const rssi_t rssi;
	const frequency_t frequency;
} contact_record_t;

typedef struct log_entry {
	const char* message;
	const time_t time;
} log_entry_t;

typedef void* hash_t; //@TODO
typedef struct keyed_hash {
	bool set;
	key_t key;
	hash_t hash;
}keyed_hash_t;

typedef struct bt_client bt_client_t;

typedef struct qubie qubie_t;

//there is only one qubie which is accessed by multiple modules
static qubie_t *qubie;
//@ ensures qubie == Result
qubie_t *get_qubie();

typedef struct wifi_monitor {
	bool wifi_booted;
	bool wifi_running;
	bool auto_hopping;
	keyed_hash_t keyed_hash;
	frequency_t* frequency_range;
	frequency_t frequency;
	qubie_t *qubie; //pointer to qubie
} wifi_monitor_t;
static const char *wifi_state_strings[] = {"booted", "running"};

typedef struct bt_communicator {
	bool subscribed;
	bt_client_t *bt_client;
	qubie_t *qubie;
} bt_communicator_t;

typedef struct bt_client {
	bt_communicator_t *bt_communicator; //pointer to qubie's bluetooth communicator
}bt_client_t;


typedef struct qubie {
	// qubie status
	state_t state;
	// pointer to self. needed when creating subcomponents that communicate back
	qubie_t *qubie;
	// pointer to qubie's log, a list of log entries with somee added functionality
	log_entry_t *log;
	// pointer to qubie's observations, a set of contact records
	contact_record_t *observations;
	// pointer to wifi monitor
	wifi_monitor_t *wifi_monitor;
	// pointer to bluetooth communicator
	bt_communicator_t *bt_communicator;
	// "qubie" querie just points to "this" so it is not needed here
} qubie_t;
#endif

