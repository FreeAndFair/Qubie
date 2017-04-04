//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include <stdbool.h>

//constructor
wifi_monitor_t make_wifi_monitor(qubie_t *qubie);

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ requires keyed_hash.set()
bool wifi_booted();
bool wifi_running();
bool auto_hopping();
keyed_hash_t keyed_hash();
frequency_t* frequency_range();
frequency_t frequency();
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires booted
 * 	requires !running
 * 	ensures running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "running")
 */
void start_wifi();

/*@ requires running
 * 	ensures !running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "stopped")
 */
void stop_wifi();

/*@ ensures frequency==the_frequency;
 * 	ensures qubie.log.logged(WIFI_MONITOR_FREQUENCY, the_frequency)
 */
//delta {frequency, qubie.log};
void set_frequency(frequency_t the_frequency);

/*@ ensures auto_hopping==the_truth_val;
 * 	ensures qubie.log.logged(WIFI_MONITOR_AUTO_HOPPING, the_truth_val)
 */
//delta {auto_hopping, qubie.log};
void set_auto_hopping(bool the_truth_val);

/*@ ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 * 	ensures qubie.log.logged(WIFI_MONITOR_DETECTED_DEVICE, {the_mac_address, the_signal_strength})
 */
// delta {qubie.observations, qubie.log};
void report_detected_device(device_id_t* the_mac_address, rssi_t the_signal_strength);








