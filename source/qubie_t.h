// qubie type and constant definitions

#include <stddef.h>
#include <stdbool.h>

/*
 * //max size of log message string in chars. shall we copy from twitter ;)
 * #define MESSAGE_SIZE 140
 * typedef char message_t[MESSAGE_SIZE]; //TODO move to qubie_log.h
 */

//mac address is 48 bits (or 6 bytes) until we decide to support EUI-64
#define MAC_SIZE 6
typedef struct mac {
	char& operator[](int i) { return byte[i]; }
	unsigned char bytes[MAC_SIZE];
} mac_t;

//hash key is 256 bits (or 64 bytes) in python hashlib.md5
#define KEY_SIZE 64 //TODO should it be 128? check options in C
//typedef unsigned char key_t[KEY_SIZE];
typedef struct key {
	char& operator[](int i) { return byte[i]; }
	unsigned char bytes[MAC_SIZE];
} key_t;

//frequencies are in increments of 1MHz at least up to 5875MHz (less than 2^16 MHz)
typedef unsigned int frequency_t;

//RSSI is defined between 0-255 though some devices measure on scale of 0-60 or 0-100
//TODO perhaps we need to switch to dBm
typedef char rssi_t;

//only minimal usage of time is needed. it's enough to count seconds since the epoch
typedef unsigned long time_t;

// a list of possible qubie states
typdef enum {POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;

const static key_t HASH_KEY;

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
typedef struct log_entry
typedef struct qubie qubie_t;
typedef struct wifi_monitor wifi_monitor_t;
typedef struct bt_communicator bt_communicator_t;
typedef struct keyed_hash keyed_hash_t;
typedef struct bt_client {
	bt_communicator_t bt_communicator; //pointer to qubie's bluetooth communicator
}bt_client_t;

//@ TODO move below to relevant .c files
typedef struct qubie {
	// qubie status
	state_t state;
	// pointer to qubie's log, a list of log entries with somee added functionality
	static log_entry_t *log;
	// pointer to qubie's observations, a set of contact records
	static contact_record_t *observations;
	// pointer to wifi monitor
	static wifi_monitor_t *wifi_monitor;
	// pointer to bluetooth communicator
	static bt_communicator_t *bt_communicator;
	// "qubie" querie just points to "this" so it is not needed here
} qubie_t;

typedef struct wifi_monitor {
	bool booted;
	bool running;
	bool auto_hopping;
	static keyed_hash_t keyed_hash; //pointer to keyed_hash
	frequency_t* frequency_range;
	frequency_t frequency;
	qubie_t qubie; //pointer to qubie
} wifi_monitor_t;
