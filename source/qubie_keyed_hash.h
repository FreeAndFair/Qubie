//implementation summary of qubie blootooth communicator

#include "qubie_t.h"

// ====================================================================
// @bon QUERIES
// ====================================================================

bool set();
//@ ensures write-once
const key_t key();

//@ TODO query to get the hash module

/*@ requires set
 * 	ensures Result = hash.hash(the_string);
 */
mac_t hashed_string(mac_t the_string)


// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires not set
 * 	ensures delta {set, hash, key};
 * 	ensures key == the_key;
 * 	ensures set
 */
void set_key(const key_t the_key);
















