//qubie module implementation summary

#include "qubie_t.h"



//@ ensure Result == {running, stopped}
static const state_t legal_update_states[3] = {RUNNING, STOPPED, POWERED_OFF};


//@ TODO define predicates in acsl file

// ====================================================================
// @bon QUERIES
// ====================================================================

// qubie status
state_t state();

// pointer to qubie's log, a list of log entries with some added functionality
log_entry_t* log();
// pointer to qubie's observations, a list of contact records
contact_record_t observations();
// pointer to wifi monitor
wifi_monitor_t wifi_monitor();
// pointer to bluetooth communicator
bt_communicator_t bl_communicator();
// "qubie" querie just points to "this" so it is not needed here

//@ ensure Result == {running, stopped}
const state_t* qubie_legal_update_states();


//@ ensures Result == (state == POWERED_ON)
//@ ensures log.empty -- initialized //@TODO
//@ ensures observations.empty -- initialized //@TODO
bool powered_on();
//@ ensures Result == (state == BOOTING)
bool booting();
//@ ensures Result == (state == RUNNING)
bool running();
//@ ensures Result == (state == STOPPED)
bool stopped();
//@ ensures Result == (state == POWERED_OFF)
bool powered_off();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires (state == POWERED_ON);
 *  ensures (state == BOOTING);
 *  ensures publish_action();
 */
void start_booting();

/*@ requires (state == BOOTING);
 *  ensures (state == RUNNING);
 *  ensures publish_action();
 */
void start_running();

/*@ requires (state == RUNNING);
 *  ensures (state == STOPPED);
 *  ensures publish_action();
 */
void stop_running();

/*@ ensures (state == POWERED_OFF);
 *  ensures publish_action();
 *  ensures log.flushed
 */
void power_off();

/*@ ensures delta log;
 *  ensures log.publish()
 */
void publish_log();

/*@ requires the_state in legal_update_state;
 * 	ensures (the_state == booting) -> start_booting;
 *	ensures (the_state == running) -> start_running;
 *	ensures (the_state == stopped) -> stop_running;
 *	ensures	(the_state == powered_off) -> power_off;
 *
 */
void update_state(state_t the_state);

/*@ ensures log.logged()
 *  ensures bt_communicator.publish_action()
 */
void qubie_publish_action(TBD); //TODO

/*@ ensures delta {observations, log}
 * 	ensures observations.contains(contact_record)
 * 	ensures publish_action()
 */
void record_observation(contact_record_t contact_record);

















