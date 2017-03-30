//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

// ====================================================================
// @bon QUERIES
// ====================================================================

/* booleans implemented in QUBIE_INTERFACE representing specific states
 * e.g. booting, running, etc. are not needed in this abstraction and
 * are therefore left out
 */

// qubie status
//@ ensures Result == qubie.state
state_t state();

//pointer to the qubie module that is connected to this communicator
qubie_t qubie();

// pointer to qubie's log, a list of log entries with some added functionality
log_entry_t* log();

bool subscribed();
//@ requires subscribed
bt_client_t bt_client();

//@ ensure Result == {running, stopped}
static const state_t bt_communicator_legal_update_states[2] = {STOPPED, POWERED_OFF};


// ====================================================================
// @bon COMMANDS
// ====================================================================

/* specific stage changing commands implemented in QUBIE_INTERFACE
 * e.g. start_running, etc. are not needed in this abstraction and
 * are therefore left out
 */

/*@ requires not subscribed
 * 	ensures delta {bt_client, subscribed};
 * 	ensures bt_client==the_bluetooth_client;
 * 	ensures subscribed;
 */
void subscribe(bt_client_t the_bluetooth_client);

/*@ requires subscribed
 * 	ensures delta {bt_client, subscribed};
 * 	ensures not subscribed;
 */
void unsubscribe();

/*@ TODO ensures *notify client when subscribed and message is relevant*
 */
void bt_communicator_publish_action(TBD); //TODO

/*@ requires the_state in legal_update_state;
 * 	ensures (the_state == booting) -> qubie.start_booting;
 *	ensures (the_state == running) -> qubie.start_running;
 *	ensures (the_state == stopped) -> qubie.stop_running;
 *	ensures	(the_state == powered_off) -> qubie.power_off;
 *
 */
void update_qubie_state(state_t the_state);





















