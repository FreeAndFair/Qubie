//qubie module implementation summary

#include "qubie_t.h"
#include "qubie.acsl"
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
//design must be synced to typedef enum {START, POWERED_ON, BOOTING, RUNNING, STOPPED, POWERED_OFF} state_t;
static const char *state_strings[] = {"start", "powered on", "booting", "running", "stopped", "powered off"};
extern qubie_observations_t the_observations;

/*	Leior May 2016
 * 	for the sake of simplicity and verifiability initialize as much of qubie
 * 	as opssible including subcomponents.
 * 	Additional initialization is done via helper function
 * 	TODO find way to initialize subcomponents in their own files without doing
 * 	complex pointer/address conversions in order to avoid problems with const fields
 */
qubie_t the_qubie = {
		.observations = {
				.size = 0,
				.observations_fp = NULL
		},
		.log = {
				.size = 0,
				.log_fp = NULL
		},
		.wifi_monitor = {
				.monitor_booted = false,
				.monitor_running = false,
				.auto_hopping = WIFI_AUTO_HOPPING_DEFAULT,
				.keyed_hash = {
					.set = false
				},
				.channels = FREQUENCY_WIFI_CHANNELS
				//design frequency field will be initialized in boot stage
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

/*@ requires logical_initialized;
   	ensures (the_qubie_state == new_state);
   	ensures logical_logged(QUBIE_STATE, state_strings[new_state]);
    ensures logical_published(new_state);
    assigns the_qubie.log;
 */
void __set_and_publish( state_t new_state){
	the_qubie.state=new_state;
	qubie_publish_action(new_state);
};

/*@
   requires !logical_initialized;
   requires the_qubie.log.log_fp == \null && the_qubie.observations.observations_fp == \null;
   ensures logical_initialized;
   ensures \valid_read(the_qubie.observations.observations_fp) && \valid_read(the_qubie.observations.observations_fp);
   assigns \nothing;
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
	return(&the_qubie.wifi_monitor);
};
// pointer to bluetooth communicator
bt_communicator_t *bt_communicator(){
	return &the_qubie.bt_communicator;
};

/*@ ensures the_qubie.legal_update_states == \result;
   	assigns \nothing;
 */
const state_t *qubie_legal_update_states(){
	return the_qubie.legal_update_states;
};

/*@	ensures the_qubie.log.size == 0 &&  the_qubie.observations.size == 0;
   	ensures \result == logical_initialized;
   	assigns \nothing;
 */
bool initialized(){
	return log_empty() && observations_empty();
};

/*@ ensures \result == (the_qubie_state == POWERED_ON);
   	assigns \nothing;
 */
bool powered_on(){
	return POWERED_ON == the_qubie.state;
};
/*@ ensures \result == (the_qubie_state == BOOTING);
   	assigns \nothing;
 */
bool booting(){
	return BOOTING == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == RUNNING);
   	assigns \nothing;
 */
bool running(){
	return RUNNING == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == STOPPED);
   	assigns \nothing;
 */
bool stopped(){
	return STOPPED == the_qubie.state;
};

/*@ ensures \result == (the_qubie_state == POWERED_OFF);
   	assigns \nothing;
 */
bool powered_off(){
	return POWERED_OFF == the_qubie.state;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================


/*@	requires the_qubie_state == START;
    ensures (the_qubie_state == POWERED_ON);
    ensures logical_published(POWERED_ON);
    assigns \nothing;
 */
void power_on(){
	__initialize_qubie();
	__set_and_publish(POWERED_ON);
};

/*@ requires (the_qubie_state == POWERED_ON);
    ensures (the_qubie_state == BOOTING);
    ensures logical_published(BOOTING);
    assigns \nothing;
 */
void start_booting(){
	boot_monitor();
	//TBD is action needed for bt_communicator?
	__set_and_publish(BOOTING);
};

/*@ requires (the_qubie_state == BOOTING);
    ensures (the_qubie_state == RUNNING);
    ensures logical_published(RUNNING);
    assigns \nothing;
 */
void start_running(){
	start_monitor();
	__set_and_publish(RUNNING);
};

/*@ requires (the_qubie_state == RUNNING);
    ensures (the_qubie_state == STOPPED);
    ensures logical_published(STOPPED);
    assigns \nothing;
 */
void stop_running(){
	stop_monitor();
	__set_and_publish(STOPPED);
};

/*@ requires the_qubie_state != POWERED_OFF;
   	ensures (the_qubie_state == POWERED_OFF);
    ensures logical_published(POWERED_OFF);
    assigns \nothing;
 */
void power_off(){
	__set_and_publish(POWERED_OFF);
	//TBD move cleanup code to the relevant modules.
	//if(the_qubie.log.log_fp) {
		fclose(the_qubie.log.log_fp);
	//}
	//if(the_qubie.observations.observations_fp) {
		fclose(the_qubie.observations.observations_fp);
	//}
};

/*@	requires (the_qubie_state == START);
   	ensures (the_qubie_state == RUNNING);
   	assigns \nothing;
 */
void power_on_boot_and_run(){
	power_on();
	start_booting();
	start_running();
};

/*@
   	ensures (the_qubie_state == POWERED_OFF);
    ensures logical_published(POWERED_OFF);
    assigns \nothing;
 */
void shut_down(){
	if (the_qubie.state != POWERED_OFF) {
		power_off();
	}
};

//TODO define qubie_legal_update_state(the_state)
/*@ requires (the_qubie_state == RUNNING && the_state == STOPPED) ||
 	 	 	 (the_qubie_state != POWERED_OFF &&the_state == POWERED_OFF);
   	ensures the_qubie_state == the_state;
   	assigns \nothing;
 */
void update_state( state_t the_state){
	//TBD switch to an array of function pointers
	if (STOPPED == the_state){
		stop_running();
	} else if (POWERED_OFF == the_state) {
		power_off();
	} else {
		//not a legal state
		//@assert(false);
		assert(false);
	}
};

/*@ ensures logical_published(the_state);
   	ensures logical_logged(QUBIE_STATE, state_strings[the_state]);
   	assigns \nothing;
 */
void qubie_publish_action( state_t the_state){
	add_log_entry(QUBIE_STATE , (void *)state_strings[the_state]);
	bt_communicator_publish_action(the_state);
};

/*@ ensures logical_observations_contains(*contact_record_ptr);
   	ensures logical_logged(QUBIE_DETECTED_DEVICE, contact_record_ptr);
   	assigns \nothing;
 */
void record_observation( contact_record_t *contact_record_ptr){
	//design the contract record belongs to observations which will eventually free the memory
	//log the data from the log entry first, while it is certain to exist.
	add_log_entry(QUBIE_DETECTED_DEVICE, (void *)contact_record_ptr);
	add_contact_record(*contact_record_ptr);
};


/*@	requires the_qubie_state == RUNNING;
   	ensures wifi_monitor_polled && bt_communicator_polled;
   	ensures the_qubie_state != RUNNING;
   	assigns \nothing;
 */
void run_loop(){
	unsigned long iterations = 0;
	/*@
	  	loop assigns iterations;
	  	loop invariant 0<=iterations<MAX_TEST_ITERATIONS;
	  	loop invariant the_qubie_state == RUNNING;
	  	loop variant MAX_TEST_ITERATIONS - iterations;
	 */
	while (running() && iterations < MAX_TEST_ITERATIONS){
		//printf("DEBUG - iteration: %lu\n",iterations);
		poll_wifi_monitor();
		poll_bt_communicator();
		iterations++;
	}
	if(running()) {
		stop_running();
	}
};














