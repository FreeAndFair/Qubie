// stub file for running qubie with a subscribed bluetooth client

#include "qubie_t.h"


//constructor
bt_client_t *make_bt_client(bt_communicator_t *bt_communicator);


// ====================================================================
// bon QUERIES
// ====================================================================

//long name to ensure it is not confused with qubie's method
bt_communicator_t *bt_client_communicator();



//ack that a qubie state update has been received
//ensures qubie_state == the_state
bool published( state_t the_state);

// ====================================================================
// bon COMMANDS
// ====================================================================
/* ensures published(the_state);
 * ensures qubie_state == the_state
 * TODO requires bt_client_communicator.bt_client==*me*
 */
void publish_from_bt_communicator( state_t the_state);

/* TODO requires the_state in legal_update_states
 * 	ensures published(the_state)
 *	ensures the_state == qubie.state
 */
void bt_client_update_qubie_state( state_t the_state);

/* requires !subscribed()
 * ensures subscribed()
 */
void create_and_subscribe_bt_client();

void poll_bt_client();


