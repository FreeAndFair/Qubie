//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

//constructor
keyed_hash_t make_keyed_hash(const key_t the_key);

// ====================================================================
// @bon QUERIES
// ====================================================================

bool set();
//@ ensures write-once
key_t *key();

//@ TODO query to get the hash module

/*@ requires set
 * 	ensures hash.hash(the_string) == Result;
 */
mac_t *hashed_string(mac_t the_string);


// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !set
 * 	ensures key == the_key;
 * 	ensures set
 */
//@ delta {set, hash, key};
void set_key(const key_t the_key);
















