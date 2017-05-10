//qubie module implementation summary

#include "qubie_t.h"
#include "qubie.h"
#include "qubie_bt_communicator.h"
#include "qubie_log.h"
#include "qubie_observations.h"
#include "qubie_wifi_monitor.h"
#include "qubie_bt_client.h"
#include "wifi_stub.h"

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

//globals
//@design must be synced to typedef enum {START, POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;
static const char *state_strings[] = {"start", "powered on", "booting", "running", "stopped", "powered off"};

qubie_t the_qubie = {
		.observations = {
				.size = 0,
				.observations_fp = NULL //fopen("qubie_observations.csv", "w") //@TODO init file with header
		},
		.log = {   //make_qubie_logger("qubie_log.txt"),
				.size = 0,
				.log_fp = NULL //fopen("qubie_log.txt","w")
		},
		.wifi_monitor = {
				.wifi_booted = false,
				.wifi_running = false,
				.auto_hopping = WIFI_AUTO_HOPPING_DEFAULT,
				.keyed_hash = {
					.set = false
				},
				.frequency_range = FREQUENCY_WIFI_CHANNELS
				//@design frequency field will be initialized in boot stage
		},
		.bt_communicator = {
				.subscribed = false,
				.bt_client = NULL,
				.legal_update_states = {STOPPED, POWERED_OFF}
		},
		.legal_update_states = {RUNNING, STOPPED, POWERED_OFF},
		.state = POWERED_ON
};

//helper functions

/*@ requires initialized;
 * 	ensures (the_qubie_state == new_state);
 * 	ensures logical_logged(new_state);
 *  ensures logical_published(new_state);
 *  assigns the_qubie_state, the_qubie.log, bt_client_qubie_state;
 */
void __set_and_publish( state_t new_state){
	the_qubie.state=new_state;
	qubie_publish_action(new_state);
};

/*@
 * requires !initialized;
 * ensures initialized;
 * assigns initialized;
 */
void __initialize_qubie(){
	//init the log
	the_qubie.log.log_fp = fopen("qubie_log.txt","w");
	//init observations
	the_qubie.observations.observations_fp = fopen("qubie_observations.csv", "w");
	fprintf(the_qubie.observations.observations_fp, "device,time,rssi,frequency\n");
	fflush(the_qubie.observations.observations_fp);

};


//constructor
qubie_t *make_qubie(){
	/* old settings @TODO remove
	qubie_t *qubie_struct = malloc(sizeof(struct qubie));
	qubie_observations_t observations = make_qubie_observations("qubie_observations.csv");
	qubie_struct->state = POWERED_ON;
	qubie_struct->log = make_qubie_logger("qubie_log.txt");
	memcpy((qubie_observations_t *)&qubie_struct->observations, &observations, sizeof(struct observations));
	//free(&observations); //@TODO is this freed automatically when the function exists?
	qubie_struct->wifi_monitor = make_wifi_monitor(qubie_struct);
	qubie_struct->bt_communicator = make_bt_communicator(qubie_struct);
	qubie_struct->legal_update_states = legal_update_states;
	*/
	__initialize_qubie();
	return &the_qubie;
};

//@ TODO define predicates in acsl file

// ====================================================================
// @bon QUERIES
// ====================================================================

// qubie status
state_t state(){
	return the_qubie.state;
};

// pointer to qubie's log, a list of log entries with some added functionality
qubie_logger_t *get_log(){
	return &the_qubie.log;
};
// pointer to qubie's observations, a list of contact records
qubie_observations_t *observations(){
	return &the_qubie.observations;
};
// pointer to wifi monitor
wifi_monitor_t *wifi_monitor(){
	return &the_qubie.wifi_monitor;
};
// pointer to bluetooth communicator
bt_communicator_t *bt_communicator(){
	return &the_qubie.bt_communicator;
};

/*@ ensures {STOPPED, POWERED_OFF} == \result;
 * 	assigns \nothing;
 */
const state_t *qubie_legal_update_states(){
	return the_qubie.legal_update_states;
};

/*@	ensures the_qubie.log.size == 0 &&  the_qubie.observations.size == 0;
 * 	ensures \result == initialized;
 * 	assigns \nothing;
 */
bool initialized(){
	return log_empty() && observations_empty();
};

/*@ ensures \result == (the_qubie_state == POWERED_ON);
 * 	assigns \nothing;
 */
bool powered_on(){
	return POWERED_ON == the_qubie.state;
};
/*@ ensures \result == (the_qubie_state == BOOTING);
 * 	assigns \nothing;
 */
bool booting(){
	return BOOTING == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == RUNNING);
 * 	assigns \nothing;
 */
bool running(){
	return RUNNING == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == STOPPED);
 * 	assigns \nothing;
 */
bool stopped(){
	return STOPPED == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == POWERED_OFF);
 * 	assigns \nothing;
 */
bool powered_off(){
	return POWERED_OFF == the_qubie.state;
};

//@ design this should not be called it is only for the purpose of defining a contract
/*@ ensures logical_publish(the_state);
 * 	assigns \nothing;
 */
bool action_published( state_t the_state){
	//@assert(false)
	assert(false);
	return logged(QUBIE_STATE , (void *)state_strings[the_state]) &&
			bt_communicator_action_published( the_state);
};


// ====================================================================
// @bon COMMANDS
// ====================================================================


/*@	requires the_qubie_state == START;
 *  ensures (the_qubie_state == POWERED_ON);
 *  ensures logical_published(state);
 *  assigns the_qubie_state;
 */
void power_on(){
	__initialize_qubie();
	__set_and_publish(POWERED_ON);
};

/*@ requires (the_qubie_state == POWERED_ON);
 *  ensures (the_qubie_state == BOOTING);
 *  ensures logical_published(state);
 *  assigns the_qubie_state;
 */
void start_booting(){
	boot_wifi();
	//TBD is action needed for bt_communicator?
	__set_and_publish(BOOTING);
};

/*@ requires (the_qubie_state == BOOTING);
 *  ensures (the_qubie_state == RUNNING);
 *  ensures logical_published(state);
 *  assigns the_qubie_state;
 */
void start_running(){
	start_wifi();
	__set_and_publish(RUNNING);
};

/*@ requires (the_qubie_state == RUNNING);
 *  ensures (the_qubie_state == STOPPED);
 *  ensures logical_published(state);
 *  assigns the_qubie_state;
 */
void stop_running(){
	stop_wifi();
	__set_and_publish(STOPPED);
};

/*@ ensures (the_qubie_state == POWERED_OFF);
 *  ensures logical_published(state);
 *  assigns the_qubie_state;
 */
void power_off(){
	__set_and_publish(POWERED_OFF);
	//@TBD move cleanup code to the relevant modules.
	fclose(the_qubie.log.log_fp);
	fclose(the_qubie.observations.observations_fp);
};

/*@	requires (the_qubie_state == START);
 * 	ensures (the_qubie_state == RUNNING);
 * 	assigns the_qubie_state;
 */
void power_on_boot_and_run(){
	power_on();
	start_booting();
	start_running();
};

//@TODO define qubie_legal_update_state(the_state)
/*@ requires the_state == STOPPED || the_state == POWERED_OFF;
 * 	ensures the_qubie_state == the_state;
 * 	assigns the_qubie_state;
 */
void update_state( state_t the_state){
	//TBD switch to an array of function pointers
	if (STOPPED == the_state){
		stop_running();
	} else if (POWERED_OFF == the_state) {
		power_off();
	} else {
		//not a legal state
		//@assert(false)
		assert(false);
	}
};

/*@ ensures logical_published(the_state);
 * 	ensures logical_logged(QUBIE_STATE, state_strings[the_state]);
 * 	assigns \nothing;
 */
void qubie_publish_action( state_t the_state){
	add_log_entry(QUBIE_STATE , (void *)state_strings[the_state]);
	bt_communicator_publish_action(the_state);
};

/*@ ensures logical_observations_contains(the_contact_record);
 * 	ensures logical_logged();
 * 	assigns the_qubie.log, the_qubie.observations;
 */
void record_observation( contact_record_t the_contact_record){
	//@design the contract record belongs to observations which will eventually free the memory
	//log the data from the log entry first, while it is certain to exist.
	add_log_entry(QUBIE_DETECTED_DEVICE, &the_contact_record);
	add_contact_record(the_contact_record);
};


/*@	requires the_qubie_state == RUNNING;
 * 	ensures wifi_monitor_polled && bt_communicator_polled;
 * 	ensures state != RUNNINNG || iterations >= MAX_TEST_ITERATIONS;
 * 	assigns \nothing;
 */
void run_loop(){
	unsigned long iterations = 0;
	while (running() && iterations < MAX_TEST_ITERATIONS){
		printf("DEBUG - iteration: %lu\n",iterations);
		poll_wifi_monitor();
		poll_bt_communicator();
		iterations++;
	}
};














