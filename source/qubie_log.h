//qubie log module implementation summary

#include "qubie_t.h"

//constructors
log_entry_t make_log_entry(message_t message_type, void* message_val);

// ====================================================================
// bon QUERIES
// ====================================================================

bool log_empty();

time_t current_time(time_t *seconds);

// ====================================================================
// bon COMMANDS
// ====================================================================

void add_log_entry( message_t message_type, void* message_val);



