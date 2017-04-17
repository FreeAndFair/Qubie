// qubie type and constant definitions

#include <stddef.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h> //@TODO remove this, and replace with minimal requirements
#include <stdlib.h>
#ifndef QUBIE_TYPES
#define QUBIE_TYPES


typedef enum {
	QUBIE_STATE,
	QUBIE_CONTACT_RECORD,
	WIFI_MONITOR_STATE,
	WIFI_MONITOR_FREQUENCY,
	WIFI_MONITOR_AUTO_HOPPING//,
	//WIFI_MONITOR_DETECTED_DEVICE
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
typedef unsigned char qubie_key_t[KEY_SIZE];
/* doesn't work in C
 * typedef struct key {
 * 	char& operator[](int i) { return byte[i]; }
 * 	unsigned char bytes[KEY_SIZE];
 * } qubie_key_t;
 */

//frequencies are in increments of 1MHz at least up to 5875MHz (less than 2^16 MHz)
typedef unsigned int frequency_t;
/* channels 12 and 13 are not really in use in the us but they are added because they are used in other countries
 * and also in specific cases inside the usa. channel 14 (2484MHz) is omitted because it is not in use by cell phones
 * @TODO verify the channels are correct (current source is wikipedia)
 */
static const frequency_t wifi_channels[68] = {	\
		2412, 2417, 2422, 2427, 2432, 2437, 2442, 2447, 2452, 2457,	\
		2462, 2467, 2472,	\
		5170, 5180, 5190, 5200, 5210, 5220, 5230, 5240, 5250, 5260,	\
		5270, 5280, 5290, 5300, 5310, 5320,	\
		5500, 5510, 5520, 5530, 5540, 5550, 5560, 5570, 5580, 5590,	\
		5600, 5610, 5620, 5630, 5640,	\
		5660, 5670, 5680, 5690, 5700,	\
		5710, 5720,	\
		5745, 5750, 5755, 5760, 5765, 5770, 5775, 5780, 5785, 5790,	\
		5795, 5800, 5805, 5810, 5815, 5820, 5825	\
};
//RSSI is defined between 0-255 though some devices measure on scale of 0-60 or 0-100
//TODO perhaps we need to switch to dBm
typedef char rssi_t;

//only minimal usage of time is needed. it's enough to count seconds since the epoch
typedef unsigned long qubie_time_t;

// a list of possible qubie states
typedef enum {POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;
static const char *state_strings[] = {"powered on", "booting", "running", "stopped", "powered off"};

typedef struct device_id {
	bool encrypted;
	mac_t *identifier_string;
} device_id_t;

typedef struct contact_record contact_record_t;
typedef struct contact_record {
	device_id_t *device_id;
	qubie_time_t contact_time;
	rssi_t rssi;
	const frequency_t *frequency;
	contact_record_t *prev;
} contact_record_t;

typedef struct observations {
	unsigned int size;
	//contact_record_t *first;
	contact_record_t *last;
	FILE *observations_fp;

} qubie_observations_t;

typedef struct log_entry {
	char* message;
	qubie_time_t time;
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

//there is only one qubie which is accessed by multiple modules
static qubie_t *qubie;
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
static const char *wifi_state_strings[] = {"booted", "running"};

typedef struct bt_communicator {
	bool subscribed;
	bt_client_t *bt_client;
	qubie_t *qubie;
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
	qubie_observations_t *observations;
	// pointer to wifi monitor
	wifi_monitor_t *wifi_monitor;
	// pointer to bluetooth communicator
	bt_communicator_t *bt_communicator;
	// "qubie" querie just points to "this" so it is not needed here
} qubie_t;
#endif

