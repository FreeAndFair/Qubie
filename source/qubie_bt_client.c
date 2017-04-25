// stub file for running qubie with a subscribed bluetooth client

#include "qubie_t.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stddef.h>
#include <stdlib.h>

//globals
bt_client_t the_bt_client;
static bt_client_t *self = &the_bt_client;

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



