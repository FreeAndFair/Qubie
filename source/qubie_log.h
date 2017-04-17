//qubie log module implementation summary

#include "qubie_t.h"

//constructors
log_entry_t *make_log_entry(message_t message_type, void* message_val);
qubie_logger_t *make_qubie_logger();

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool log_empty(qubie_logger_t *self);

/*@ TODO ensures log_contains(the_log_entry);
 */
// delta element(size);
bool logged(qubie_logger_t *self, message_t message_type, void* message_val);


qubie_time_t current_time();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ ensures logged(message_type, message_val);
 */
void add_log_entry(qubie_logger_t *self, message_t message_type, void* message_val);



