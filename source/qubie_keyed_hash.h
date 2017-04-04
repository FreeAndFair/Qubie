//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

//constructor
keyed_hash_t make_keyed_hash();

// ====================================================================
// @bon QUERIES
// ====================================================================

bool set(keyed_hash_t *self);
//@ ensures write-once
qubie_key_t *key(keyed_hash_t *self);

//@ TODO query to get the hash module

/*@ requires set
 * 	ensures hash.hash(the_string) == Result;
 */
const mac_t *hashed_string(keyed_hash_t *self, mac_t the_string);

qubie_key_t *create_random_key();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !set
 * 	ensures key == the_key;
 * 	ensures set
 */
//@ delta {set, hash, key};
void set_key(keyed_hash_t *self, qubie_key_t *the_key);

















