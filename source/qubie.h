//qubie module implementation summary

#include "qubie_t.h"

//constructor
qubie_t *make_qubie();



// ====================================================================
// bon QUERIES
// ====================================================================

state_t state();

qubie_logger_t *get_log();

qubie_observations_t *observations();

wifi_monitor_t *wifi_monitor();

bt_communicator_t *bt_communicator();

const state_t* qubie_legal_update_states();

bool initialized();

bool powered_on();

bool booting();

bool running();

bool stopped();

bool powered_off();

// ====================================================================
// bon COMMANDS
// ====================================================================

void power_on();

void start_booting();

void start_running();

void stop_running();

void power_off();

void power_on_boot_and_run();

void shut_down();

void update_state( state_t the_state);

void qubie_publish_action( state_t the_state);

void record_observation( contact_record_t *contact_record_ptr);

void run_loop();














