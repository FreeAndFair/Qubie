//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

//constructor

// ====================================================================
// bon QUERIES
// ====================================================================

/* booleans implemented in QUBIE_INTERFACE representing specific states
 * e.g. booting, running, etc. are not needed in this abstraction and
 * are therefore left out
 */

// qubie status
// ensures Result == qubie.state
state_t bt_communicator_qubie_state();

// pointer to qubie's log, a list of log entries with some added functionality
qubie_logger_t *get_qubie_log();

bool subscribed();
// requires subscribed
bt_client_t *bt_client();

bool bt_communicator_action_published( state_t the_state);

const state_t *get_bt_communicator_legal_update_states();

// ====================================================================
// bon COMMANDS
// ====================================================================

/* specific stage changing commands implemented in QUBIE_INTERFACE
 * e.g. start_running, etc. are not needed in this abstraction and
 * are therefore left out
 */

void subscribe( bt_client_t *the_bluetooth_client);

void unsubscribe();

void bt_communicator_publish_action( state_t the_state);

void bt_communicator_update_qubie_state( state_t the_state);

void poll_bt_communicator();



















