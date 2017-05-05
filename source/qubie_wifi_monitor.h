//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_observations.h"
#include "qubie_log.h"
#include <stdbool.h>

//constructor
wifi_monitor_t make_wifi_monitor(qubie_t *qubie);

// ====================================================================
// @bon QUERIES
// ====================================================================

bool wifi_booted();
bool wifi_running();
bool auto_hopping();
keyed_hash_t *keyed_hash();
const frequency_t* frequency_range();
frequency_t frequency();
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/* @requires !booted
 * @ensures booted
 * @ensures keyed_hash.set();
 * @ensures qubie.log.logged(WIFI_MONITOR_STATE, "booted")
 * @TODO ensures frequency in frequency_range
 */
void boot_wifi();

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
void set_frequency( frequency_t the_frequency);

/*@ ensures auto_hopping==the_truth_val;
 * 	ensures qubie.log.logged(WIFI_MONITOR_AUTO_HOPPING, the_truth_val)
 */
//delta {auto_hopping, qubie.log};
void set_auto_hopping( bool the_truth_val);

/*@ ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 * 	ensures qubie.log.logged(WIFI_MONITOR_DETECTED_DEVICE, {the_mac_address, the_signal_strength})
 */
// delta {qubie.observations, qubie.log};
void report_detected_device(
		mac_t the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		);

/* @requires message.length < MAX_MESSAGE_LEN - 100
 * @ensures qubie.log.logged(WIFI_MONITOR_UNSUPPORTED_PACKET, message)
 */
void report_unsupported_packet(char * message);

/*@ requires running
 *
 */
void poll_wifi_monitor();


