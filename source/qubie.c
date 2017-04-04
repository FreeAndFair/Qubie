//qubie module implementation summary

#include "qubie_t.h"

//constructor
qubie_t make_qubie(qubie_t *qubie);

//@ ensure Result == {running, stopped}
static const state_t legal_update_states[3] = {RUNNING, STOPPED, POWERED_OFF};


//@ TODO define predicates in acsl file

// ====================================================================
// @bon QUERIES
// ====================================================================

// qubie status
state_t state();

// pointer to qubie's log, a list of log entries with some added functionality
log_entry_t* get_log();
// pointer to qubie's observations, a list of contact records
contact_record_t observations();
// pointer to wifi monitor
wifi_monitor_t wifi_monitor();
// pointer to bluetooth communicator
bt_communicator_t bt_communicator();
// "qubie" querie just points to "this" so it is not needed here

//@ ensures {stopped, powered_off} == Result
const state_t* qubie_legal_update_states();

//@ TODO add relevant predicates to avoid error prone syntax
/*@ ensures Result == (state == POWERED_ON)
 * ensures log.empty
 * ensures observations.empty
 */
bool powered_on();
//@ ensures Result == (state == BOOTING)
bool booting();
//@ ensures Result == (state == RUNNING)
bool running();
//@ ensures Result == (state == STOPPED)
bool stopped();
//@ ensures Result == (state == POWERED_OFF)
bool powered_off();
/*@ ensures log.logged(QUBIE_STATE , state_strings[state]) &&
 *  (!bt_communicator.subscribed || bt_communicator.action_published(state))
 */
bool action_published(state_t state);

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires (state == POWERED_ON);
 *  ensures (state == BOOTING);
 *  ensures action_published(state);
 */
void start_booting();

/*@ requires (state == BOOTING);
 *  ensures (state == RUNNING);
 *  ensures action_published(state);
 */
void start_running();

/*@ requires (state == RUNNING);
 *  ensures (state == STOPPED);
 *  ensures action_published(state);
 */
void stop_running();

/*@ ensures (state == POWERED_OFF);
 *  ensures action_published(state);
 */
void power_off();

//@TODO define qubie_legal_update_state(the_state)
/*@ requires qubie_legal_update_state(the_state);
 * 	ensures the_state == state;
 */
void update_state(state_t the_state);

/*@ ensures action_published(the_state)
 */
void qubie_publish_action(state_t the_state);

/*@ ensures observations.contains(the_contact_record)
 * 	ensures log.logged()
 */
//delta {observations, log}
void record_observation(contact_record_t the_contact_record);

















