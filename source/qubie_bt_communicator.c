//implementation summary of qubie blootooth communicator

#include "qubie_t.h"
#include "qubie.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>

//@TODO is there a better way to define and store this data?
static const state_t bt_communicator_legal_update_states[2] = {STOPPED, POWERED_OFF};

//constructor
bt_communicator_t *make_bt_communicator(qubie_t *qubie){
	bt_communicator_t *bt_communicator_struct = malloc(sizeof(struct bt_communicator));
	bt_communicator_struct->subscribed = false;
	bt_communicator_struct->bt_client = NULL;
	bt_communicator_struct->qubie = qubie;
	bt_communicator_struct->legal_update_states=bt_communicator_legal_update_states;
	return bt_communicator_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================

/* booleans implemented in QUBIE_INTERFACE representing specific states
 * e.g. booting, running, etc. are not needed in this abstraction and
 * are therefore left out
 */

// qubie status
//@ ensures Result == qubie.state
state_t bt_communicator_qubie_state(bt_communicator_t *self){
	return state(self->qubie);
};

//pointer to the qubie module that is connected to this communicator
// moved to central location: qubie_t qubie();

// pointer to qubie's log, a list of log entries with some added functionality
qubie_logger_t *get_qubie_log(bt_communicator_t *self){
	return get_log(self->qubie);
};

bool subscribed(bt_communicator_t *self){
	return self->subscribed;
};
//@ requires subscribed
bt_client_t *bt_client(bt_communicator_t *self){
	return self->bt_client;
};

/*@ ensure !subscribed or bt_client.received(the_state);
 *
 */
bool bt_communicator_action_published(bt_communicator_t *self, state_t the_state){
	bool Result = false;
	if (!self->subscribed) {
		Result = true; //published to the empty set or clients
	} else {
		Result = received(self->bt_client,the_state);
	}
	return Result;
};

/*@ ensures {stopped, powered_off} == Result;
 */
const state_t *get_bt_communicator_legal_update_states(bt_communicator_t *self){
	return self->legal_update_states;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================

/* specific stage changing commands implemented in QUBIE_INTERFACE
 * e.g. start_running, etc. are not needed in this abstraction and
 * are therefore left out
 */

/*@ requires !subscribed
 * 	ensures bt_client==the_bluetooth_client;
 * 	ensures subscribed;
 */
//@ delta {bt_client, subscribed};
void subscribe(bt_communicator_t *self, bt_client_t *the_bluetooth_client){
	self->bt_client = the_bluetooth_client;
	self->subscribed = true;
};

/*@ requires subscribed
 * 	ensures !subscribed;
 */
//@ delta {bt_client, subscribed};
void unsubscribe(bt_communicator_t *self){
	self->bt_client = NULL;
	self->subscribed = false;
};

/*@ ensures !subscribed || bt_client.received(the_state)
 */
void bt_communicator_publish_action(bt_communicator_t *self, state_t the_state){
	if (self->subscribed) {
		receive_state(self->bt_client, the_state);
	};
};

/*@ requires the_state in bt_communicator_legal_update_states;
 * 	ensures the_state == qubie.state;
 */
void bt_communicator_update_qubie_state(bt_communicator_t *self, state_t the_state){
	update_state(self->qubie, the_state);
};





















