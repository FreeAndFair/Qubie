// stub file for running qubie with a subscribed bluetooth client

#include "qubie_t.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stddef.h>
#include <stdlib.h>

//globals
bt_client_t the_bt_client;
static bt_client_t *self = &the_bt_client;

//helper functions

//constructor
bt_client_t *make_bt_client(bt_communicator_t *bt_communicator){
	/*
	bt_client_t *bt_client_struct = malloc(sizeof(struct bt_client));
	bt_client_struct->bt_communicator = bt_communicator;
	bt_client_struct->qubie_state = bt_communicator_qubie_state();
	return *bt_client_struct;
	*/
	the_bt_client.bt_communicator = bt_communicator;
	the_bt_client.qubie_state = bt_communicator_qubie_state();
	return &the_bt_client;
};


// ====================================================================
// @bon QUERIES
// ====================================================================

//long name to ensure it is not confused with qubie's method
bt_communicator_t *bt_client_communicator(){
	return self->bt_communicator;
};

//ack that a qubie state update has been received
bool published( state_t the_state){
	//@TODO? how to deal with quick state changes. is it enough to check the current state?
	return self->qubie_state == the_state;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================
/*@ ensures published(the_state);
 *  TODO ensures delta Current
 */
void publish_from_bt_communicator( state_t the_state){
	self->qubie_state = the_state;
};

/*@ TODO requires the_state in legal_update_states
 * 	ensures published(the_state)
 *	ensures the_state == qubie.state
 */
void bt_client_update_qubie_state( state_t the_state){
	bt_communicator_update_qubie_state(the_state);
};

/*@ requires !subscribed()
 *@ ensures subscribed()
 */
void create_and_subscribe_bt_client(){
	bt_client_t *the_bt_client = make_bt_client(bt_client_communicator());
	subscribe(the_bt_client);
};


void poll_bt_client(){
	//@design chance determined in parts per 10000 (when in relevant state)
	//TBD move these to defaults for better control
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








