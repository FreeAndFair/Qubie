//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

//constructor

// ====================================================================
// bon QUERIES
// ====================================================================

bool set();
// ensures write-once
const qubie_key_t *key();

char const *hashed_string( bool encrypted, mac_t the_string);

qubie_key_t *create_random_key();

// ====================================================================
// bon COMMANDS
// ====================================================================

void set_key( qubie_key_t *the_key);

















