// stub file for running qubie with a subscribed bluetooth client

#include "qubie_t.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stddef.h>
#include <stdlib.h>


//constructor
bt_client_t *make_bt_client(bt_communicator_t *bt_communicator){
	bt_client_t *bt_client_struct = malloc(sizeof(struct bt_client));
	bt_client_struct->bt_communicator = bt_communicator;
	bt_client_struct->qubie_state = bt_communicator_qubie_state(bt_communicator);
	return bt_client_struct;
};


// ====================================================================
// @bon QUERIES
// ====================================================================

//long name to ensure it is not confused with qubie's method
bt_communicator_t *bt_client_communicator(bt_client_t *self){
	return self->bt_communicator;
};

//ack that a qubie state update has been received
bool received(bt_client_t *self, state_t the_state){
	//@TODO? how to deal with quick state changes. is it enough to check the current state?
	return self->qubie_state == the_state;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================
/*@ ensures received(the_state);
 *  TODO ensures delta Current
 */
void receive_state(bt_client_t *self, state_t the_state){
	self->qubie_state = the_state;
};

/*@ TODO requires the_state in legal_update_states
 * 	ensures received(the_state)
 *	ensures the_state == qubie.state
 */
void bt_client_update_qubie_state(bt_client_t *self, state_t the_state){
	bt_communicator_update_qubie_state(self->bt_communicator, the_state);
};



