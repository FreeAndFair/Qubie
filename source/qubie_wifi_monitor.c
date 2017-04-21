//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_defaults.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_keyed_hash.h"
#include <stdbool.h>
#include <stdlib.h>

static const frequency_t wifi_channels[NUM_WIFI_CHANNELS] = FREQUENCY_WIFI_CHANNELS;

//constructor
wifi_monitor_t *make_wifi_monitor(qubie_t *qubie){
	wifi_monitor_t *wifi_monitor_struct=malloc(sizeof(struct wifi_monitor));
	wifi_monitor_struct->wifi_booted = false;
	wifi_monitor_struct->wifi_running = false;
	wifi_monitor_struct->auto_hopping = WIFI_AUTO_HOPPING_DEFAULT;
	wifi_monitor_struct->keyed_hash = make_keyed_hash();
	wifi_monitor_struct->frequency_range = wifi_channels;
	//@design by default start at the begining of the spectrum
	wifi_monitor_struct->frequency = WIFI_FREQUENCY_DEFAULT;
	wifi_monitor_struct->qubie = qubie;
	return wifi_monitor_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================


bool wifi_booted(wifi_monitor_t *self){
	return self->wifi_booted;
};
bool wifi_running(wifi_monitor_t *self){
	return self->wifi_running;
};
bool auto_hopping(wifi_monitor_t *self){
	return self->auto_hopping;
};
keyed_hash_t *keyed_hash(wifi_monitor_t *self){
	return self->keyed_hash;
};
const frequency_t* frequency_range(wifi_monitor_t *self){
	return self->frequency_range;
};
frequency_t frequency(wifi_monitor_t *self){
	return self->frequency;
};
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !booted
 * 	ensures booted
 * 	ensures keyed_hash.set();
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "booted")
 */
void boot_wifi(wifi_monitor_t *self){
	qubie_key_t *the_key = create_random_key();
	set_key(self->keyed_hash, the_key);
	//@TODO boot actual wifi device
	add_log_entry(self->qubie->log, WIFI_MONITOR_STATE, (void *)"booted");
	self->wifi_booted = true;
};

/*@ requires booted
 * 	requires !running
 * 	ensures running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "running")
 */
void start_wifi(wifi_monitor_t *self){
	//@TODO start actual wifi device
	add_log_entry(self->qubie->log, WIFI_MONITOR_STATE, (void *)"running");
	self->wifi_running = true;
};

/*@ requires running
 * 	ensures !running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "stopped")
 */
void stop_wifi(wifi_monitor_t *self){
	//@TODO stop actual wifi device
	add_log_entry(self->qubie->log, WIFI_MONITOR_STATE, (void *)"stopped");
	self->wifi_running = false;
};

/*@ ensures frequency==the_frequency;
 * 	ensures qubie.log.logged(WIFI_MONITOR_FREQUENCY, the_frequency)
 */
//delta {frequency, qubie.log};
void set_frequency(wifi_monitor_t *self, frequency_t the_frequency){
	self->frequency = the_frequency;
	//@TODO set frequency of actual wifi device
	add_log_entry(self->qubie->log, WIFI_MONITOR_FREQUENCY, (void *)the_frequency);
};

/*@ ensures auto_hopping==the_truth_val;
 * 	ensures qubie.log.logged(WIFI_MONITOR_AUTO_HOPPING, the_truth_val)
 */
//delta {auto_hopping, qubie.log};
void set_auto_hopping(wifi_monitor_t *self, bool the_truth_val){
	self->auto_hopping = the_truth_val;
	//@TODO set auto hopping state of actual wifi device
	add_log_entry(self->qubie->log, WIFI_MONITOR_AUTO_HOPPING, (void *)the_truth_val);

};

/*@ ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 * 	ensures qubie.log.logged(WIFI_MONITOR_DETECTED_DEVICE, {the_mac_address, the_signal_strength})
 */
// delta {qubie.observations, qubie.log};
void report_detected_device(
		wifi_monitor_t *self,
		mac_t *the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		){
	printf("DEBUG - making device id\n");
	device_id_t the_device_id = make_device_id(self->keyed_hash, the_mac_address);
	printf("DEBUG - making contact record\n");
	contact_record_t the_contact_record = make_contact_record(the_device_id, current_time(NULL), the_signal_strength, the_frequency);
	printf("DEBUG - recording observation\n");
	record_observation(self->qubie, the_contact_record);
};








