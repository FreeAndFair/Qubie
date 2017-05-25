//qubie log module implementation summary

#include "qubie_t.h"

//constructors
log_entry_t make_log_entry(message_t message_type, void* message_val);
qubie_logger_t make_qubie_logger(const char* filename);

// ====================================================================
// bon QUERIES
// ====================================================================

// ensures (0 == size) == Result
bool log_empty();

/* TODO ensures log_contains(the_log_entry);
 */
// delta element(size);
bool logged( message_t message_type, void* message_val);


time_t current_time(time_t *seconds);

// ====================================================================
// bon COMMANDS
// ====================================================================

/* ensures logged(message_type, message_val);
 */
void add_log_entry( message_t message_type, void* message_val);



