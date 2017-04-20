//qubie module implementation summary

#include "qubie_t.h"

//constructor
qubie_t *make_qubie();


//@ TODO define predicates in acsl file

// ====================================================================
// @bon QUERIES
// ====================================================================

// qubie status
state_t state(qubie_t *self);

// pointer to qubie's log, a list of log entries with some added functionality
qubie_logger_t *get_log(qubie_t *self);
// pointer to qubie's observations, a list of contact records
qubie_observations_t *observations(qubie_t *self);
// pointer to wifi monitor
wifi_monitor_t *wifi_monitor(qubie_t *self);
// pointer to bluetooth communicator
bt_communicator_t *bt_communicator(qubie_t *self);
// "qubie" querie just points to "this" so it is not needed here

//@ ensures {stopped, powered_off} == Result
const state_t* qubie_legal_update_states(qubie_t *self);

//@ TODO add relevant predicates to avoid error prone syntax
/*@ ensures Result == (state == POWERED_ON)
 * ensures log.empty
 * ensures observations.empty
 */
bool powered_on(qubie_t *self);
//@ ensures Result == (state == BOOTING)
bool booting(qubie_t *self);
//@ ensures Result == (state == RUNNING)
bool running(qubie_t *self);
//@ ensures Result == (state == STOPPED)
bool stopped(qubie_t *self);
//@ ensures Result == (state == POWERED_OFF)
bool powered_off(qubie_t *self);
/*@ ensures log.logged(QUBIE_STATE , state_strings[state]) &&
 *  (!bt_communicator.subscribed || bt_communicator.action_published(state))
 */
bool action_published(qubie_t *self, state_t the_state);

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires (state == POWERED_ON);
 *  ensures (state == BOOTING);
 *  ensures action_published(state);
 */
void start_booting(qubie_t *self);

/*@ requires (state == BOOTING);
 *  ensures (state == RUNNING);
 *  ensures action_published(state);
 */
void start_running(qubie_t *self);

/*@ requires (state == RUNNING);
 *  ensures (state == STOPPED);
 *  ensures action_published(state);
 */
void stop_running(qubie_t *self);

/*@ ensures (state == POWERED_OFF);
 *  ensures action_published(state);
 */
void power_off(qubie_t *self);

//@TODO define qubie_legal_update_state(the_state)
/*@ requires qubie_legal_update_state(the_state);
 * 	ensures the_state == state;
 */
void update_state(qubie_t *self, state_t the_state);

/*@ ensures action_published(the_state)
 */
void qubie_publish_action(qubie_t *self, state_t the_state);

/*@ ensures observations.contains(the_contact_record)
 * 	ensures log.logged()
 */
//delta {observations, log}
void record_observation(qubie_t *self, contact_record_t *the_contact_record);

















