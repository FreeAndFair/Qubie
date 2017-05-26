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
bool published( state_t the_state);

// ====================================================================
// bon COMMANDS
// ====================================================================

void publish_from_bt_communicator( state_t the_state);

void bt_client_update_qubie_state( state_t the_state);

void create_and_subscribe_bt_client();

void poll_bt_client();


