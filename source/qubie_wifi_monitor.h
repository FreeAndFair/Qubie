//implementation summary of qubie wifi monitor

#include "qubie_t.h"

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ requires keyed_hash.set()
bool booted();
bool running();
bool auto_hopping();
keyed_hash_t keyed_hash();
frequency_t* frequency_range();
frequency_t frequency();
qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires booted
 * 	requires not running
 * 	ensures running
 * 	ensures qubie.publish_action()
 */
void start_wifi();

/*@ requires running
 * 	ensures not running
 * 	ensures qubie.publish_action()
 */
void stop_wifi();

/*@ ensures delta {frequency, qubie.log};
 *  ensures frequency==the_frequency;
 *  ensures qubie.publish_action()
 */
void set_frequency(frequency_t the_frequency);

/*@ ensures delta {auto_hopping, qubie.log};
 *  ensures auto_hopping==the_truth_val;
 *  ensures qubie.publish_action()
 */
void set_auto_hopping(bool the_truth_val);

/*@ ensures delta {qubie.observations, qubie.log};
 * 	ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 *  ensures qubie.publish_action()
 */
void report_detected_device(device_id_t* the_mac_address, rssi_t the_signal_strength);








