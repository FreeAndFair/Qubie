// stub file for running qubie with a subscribed bluetooth client

#include "qubie_t.h"
#include "qubie.acsl"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stddef.h>
#include <stdlib.h>

//globals
bt_client_t the_bt_client;
static bt_client_t *self = &the_bt_client;

//helper functions

//constructor
/*@	ensures \result->bt_communicator == bt_communicator;
   	ensures \result->	qubie_state == the_qubie_state;
   	assigns self, the_bt_client;
 */
bt_client_t *make_bt_client(bt_communicator_t *bt_communicator){
	the_bt_client.bt_communicator = bt_communicator;
	the_bt_client.qubie_state = bt_communicator_qubie_state();
	return &the_bt_client;
};


// ====================================================================
// @bon QUERIES
// ====================================================================

//long name to ensure it is not confused with qubie's method
/*@ requires true;
   	ensures \result == the_bt_client.bt_communicator;
   assigns \nothing;
 */
bt_communicator_t *bt_client_communicator(){
	return the_bt_client.bt_communicator;
};

//ack that a qubie state update has been received
/*@
   	requires true;
   	ensures \result == (the_qubie_state == bt_client_qubie_state);
   	assigns \nothing;
 */
bool published( state_t the_state){
	return the_bt_client.qubie_state == the_state;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================
/*@ ensures the_qubie_state == bt_client_qubie_state;
   assigns \nothing;
 */
void publish_from_bt_communicator( state_t the_state){
	the_bt_client.qubie_state = the_state;
};

/*@ requires the_state == STOPPED ^^ the_state == POWERED_OFF; //design: legal states
   	ensures the_state == the_qubie.state;
   	ensures the_state == the_qubie_state;
   	assigns the_qubie.state;
 */
void bt_client_update_qubie_state( state_t the_state){
	bt_communicator_update_qubie_state(the_state);
};

/*@ requires !bt_client_subscribed;
   ensures bt_client_subscribed;
   assigns  the_bt_client, self, the_bt_client.bt_communicator->subscribed;
 */
void create_and_subscribe_bt_client(){
	bt_client_t *the_bt_client = make_bt_client(bt_client_communicator());
	subscribe(the_bt_client);
};

//design allow bt_client to do whatever is in its spec.
/*@
   	assigns the_bt_client.bt_communicator->subscribed, the_bt_client.bt_communicator->bt_client, the_qubie.state;
 */
void poll_bt_client(){
	//design chance determined in parts per 10000 (when in relevant state)
	//TBD move these to defaults for better control (if needed)
	uint subscribe_chance = 5000;
	uint unsubscribe_chance = 500;
	uint stop_chance = 2;
	uint power_off_chance = 1;

	unsigned int rand_val = (rand() % 10000);
	if(subscribed()){
		if (rand_val < unsubscribe_chance) {
			unsubscribe();
		} else if (rand_val < unsubscribe_chance + stop_chance){
			bt_client_update_qubie_state(STOPPED);
		} else if (rand_val < unsubscribe_chance + stop_chance + power_off_chance){
			bt_client_update_qubie_state(POWERED_OFF);
		};
	} else if (rand_val <=subscribe_chance) { //not subscribed
		subscribe(self);
	}
};








