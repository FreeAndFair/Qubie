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
//static const state_t legal_update_states[] = {RUNNING, STOPPED, POWERED_OFF};
//@design must be synced to typedef enum {POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;
const char *state_strings[] = {"powered on", "booting", "running", "stopped", "powered off"};

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

/*@ ensures (state == new_state);
 *  ensures action_published(new_state);
 */
void __set_and_publish( state_t new_state){
	the_qubie.state=new_state;
	qubie_publish_action(new_state);
};

//@ensures initialized
void __initialize_qubie(){
	//@init the log
	the_qubie.log.log_fp = fopen("qubie_log.txt","w");
	//@init observations
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

//@ ensures {stopped, powered_off} == Result
const state_t *qubie_legal_update_states(){
	return the_qubie.legal_update_states;
};

//@ensures log.empty() and observations.empty()
bool initialized(){
	return log_empty() && observations_empty();
};

//@ TODO add relevant predicates to avoid error prone syntax
/*@ ensures Result == (state == POWERED_ON)
 */
bool powered_on(){
	return POWERED_ON == the_qubie.state;
};
//@ ensures Result == (state == BOOTING)
bool booting(){
	return BOOTING == the_qubie.state;
};
//@ ensures Result == (state == RUNNING)
bool running(){
	return RUNNING == the_qubie.state;
};
//@ ensures Result == (state == STOPPED)
bool stopped(){
	return STOPPED == the_qubie.state;
};
//@ ensures Result == (state == POWERED_OFF)
bool powered_off(){
	return POWERED_OFF == the_qubie.state;
};
/*@ ensures log.logged(QUBIE_STATE , state_strings[state]) &&
 *  (!bt_communicator.subscribed || bt_communicator.action_published(state))
 *
 * @design this should not be called it is only for the purpose of defining a contract
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


/*
 *@  ensures (state == POWERED_ON);
 *@  ensures action_published(state);
 */
void power_on(){
	__initialize_qubie();
	__set_and_publish(POWERED_ON);
};

/*@ requires (state == POWERED_ON);
 *  ensures (state == BOOTING);
 *  ensures action_published(state);
 */
void start_booting(){
	boot_wifi();
	//@TBD is action needed for bt_communicator?
	__set_and_publish(BOOTING);
};

/*@ requires (state == BOOTING);
 *  ensures (state == RUNNING);
 *  ensures action_published(state);
 */
void start_running(){
	start_wifi();
	__set_and_publish(RUNNING);
};

/*@ requires (state == RUNNING);
 *  ensures (state == STOPPED);
 *  ensures action_published(state);
 */
void stop_running(){
	stop_wifi();
	__set_and_publish(STOPPED);
};

/*@ ensures (state == POWERED_OFF);
 *  ensures action_published(state);
 */
void power_off(){
	__set_and_publish(POWERED_OFF);
	//@TBD move cleanup code to the relevant modules.
	fclose(the_qubie.log.log_fp);
	fclose(the_qubie.observations.observations_fp);
};

/* @requires (state < BOOTING);
 * @ensures (state == RUNNING);
 */
void power_on_boot_and_run(){
	power_on();
	start_booting();
	start_running();
};

//@TODO define qubie_legal_update_state(the_state)
/*@ requires qubie_legal_update_state(the_state);
 * 	ensures the_state == state;
 */
void update_state( state_t the_state){
	//@TODO switch to an array of function pointers
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

/*@ ensures action_published(the_state)
 */
void qubie_publish_action( state_t the_state){
	add_log_entry(QUBIE_STATE , (void *)state_strings[the_state]);
	bt_communicator_publish_action(the_state);
};

/*@ ensures observations.contains(the_contact_record)
 * 	ensures log.logged()
 */
//delta {observations, log}
void record_observation( contact_record_t the_contact_record){
	//@design the contract record belongs to observations which will eventually free the memory
	//log the data from the log entry first, while it is certain to exist.
	add_log_entry(QUBIE_DETECTED_DEVICE, &the_contact_record);
	add_contact_record(the_contact_record);
};


/* @requires running()
 * @TODO ensures wifi_monitor and bt_client are polled
 * @ensures state > running;
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














