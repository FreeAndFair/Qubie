//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

//constructor
bt_communicator_t *make_bt_communicator(qubie_t *qubie);

// ====================================================================
// @bon QUERIES
// ====================================================================

/* booleans implemented in QUBIE_INTERFACE representing specific states
 * e.g. booting, running, etc. are not needed in this abstraction and
 * are therefore left out
 */

// qubie status
//@ ensures Result == qubie.state
state_t bt_communicator_qubie_state();

//pointer to the qubie module that is connected to this communicator
// moved to central location: qubie_t qubie();

// pointer to qubie's log, a list of log entries with some added functionality
qubie_logger_t *get_qubie_log();

bool subscribed();
//@ requires subscribed
bt_client_t *bt_client();

/*@ ensure !subscribed or bt_client.published(the_state);
 *
 */
bool bt_communicator_action_published( state_t the_state);

/*@ ensures {stopped, powered_off} == Result;
 */
const state_t *get_bt_communicator_legal_update_states();

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
void subscribe( bt_client_t *the_bluetooth_client);

/*@ requires subscribed
 * 	ensures !subscribed;
 */
//@ delta {bt_client, subscribed};
void unsubscribe();

/*@ ensures bt_client.published(the_state)
 */
void bt_communicator_publish_action( state_t the_state);

/*@ requires the_state in bt_communicator_legal_update_states;
 * 	ensures the_state == qubie.state;
 */
void bt_communicator_update_qubie_state( state_t the_state);





















