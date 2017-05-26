//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_observations.h"
#include "qubie_log.h"
#include <stdbool.h>

//constructor

// ====================================================================
// bon QUERIES
// ====================================================================

bool monitor_booted();
bool monitor_running();
bool auto_hopping();
keyed_hash_t *keyed_hash();
const frequency_t* channels();
frequency_t frequency();

// ====================================================================
// bon COMMANDS
// ====================================================================

void boot_monitor();

void start_monitor();

void stop_monitor();

void set_frequency( frequency_t the_frequency);

void set_auto_hopping( bool the_truth_val);

void update_monitored_frequency();

void report_detected_device(
		mac_t the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		);

void report_unsupported_packet(char * message);

void poll_wifi_monitor();


