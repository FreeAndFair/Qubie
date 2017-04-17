//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_observations.h"
#include "qubie_log.h"
#include <stdbool.h>

//constructor
wifi_monitor_t *make_wifi_monitor(qubie_t *qubie);

// ====================================================================
// @bon QUERIES
// ====================================================================

bool wifi_booted(wifi_monitor_t *self);
bool wifi_running(wifi_monitor_t *self);
bool auto_hopping(wifi_monitor_t *self);
keyed_hash_t *keyed_hash(wifi_monitor_t *self);
const frequency_t* frequency_range(wifi_monitor_t *self);
frequency_t frequency(wifi_monitor_t *self);
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !booted
 * 	ensures booted
 * 	ensures keyed_hash.set();
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "booted")
 */
void boot_wifi(wifi_monitor_t *self);

/*@ requires booted
 * 	requires !running
 * 	ensures running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "running")
 */
void start_wifi(wifi_monitor_t *self);

/*@ requires running
 * 	ensures !running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "stopped")
 */
void stop_wifi(wifi_monitor_t *self);

/*@ ensures frequency==the_frequency;
 * 	ensures qubie.log.logged(WIFI_MONITOR_FREQUENCY, the_frequency)
 */
//delta {frequency, qubie.log};
void set_frequency(wifi_monitor_t *self, frequency_t the_frequency);

/*@ ensures auto_hopping==the_truth_val;
 * 	ensures qubie.log.logged(WIFI_MONITOR_AUTO_HOPPING, the_truth_val)
 */
//delta {auto_hopping, qubie.log};
void set_auto_hopping(wifi_monitor_t *self, bool the_truth_val);

/*@ ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 * 	ensures qubie.log.logged(WIFI_MONITOR_DETECTED_DEVICE, {the_mac_address, the_signal_strength})
 */
// delta {qubie.observations, qubie.log};
void report_detected_device(
		wifi_monitor_t *self,
		mac_t *the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		);







