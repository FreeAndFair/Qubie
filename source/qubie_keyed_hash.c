//implementation summary of qubie blootooth communicator

#include "qubie_t.h"
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include "sodium.h"
#include "qubie_keyed_hash.h"

//constructor
keyed_hash_t make_keyed_hash(){
	struct keyed_hash *keyed_hash_struct = malloc(sizeof(struct keyed_hash));
	keyed_hash_struct->set=false;
	qubie_key_t *the_key = create_random_key();
	set_key(keyed_hash_struct, the_key);
	return *keyed_hash_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures write-once
bool set(keyed_hash_t *self){
	return self->set;
};

qubie_key_t *key(keyed_hash_t *self){;
	return self->key;
};

/*@ requires set
 * 	ensures hash.hash(the_string) == Result;
 */
const mac_t *hashed_string(keyed_hash_t *self, mac_t the_string){
	if (!self->set) {
		  assert(false);
		  //@ assert bottom: false;
	};
	mac_t *mac_buf = malloc(sizeof(mac_t) * MAC_SIZE);
	crypto_generichash(*mac_buf, MAC_SIZE,
	                   the_string, MAC_SIZE,
	                   *(self->key), KEY_SIZE);
	return (const mac_t *)mac_buf;
};

//implemetned with libsodium
qubie_key_t *create_random_key(){
	qubie_key_t *key_buf = malloc(sizeof(qubie_key_t) * KEY_SIZE);
	randombytes_buf((void *)key_buf, (const size_t)KEY_SIZE);
	return key_buf;
};


// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !set
 * 	ensures key == the_key;
 * 	ensures set
 */
//@ delta {set, hash, key};
void set_key(keyed_hash_t *self, qubie_key_t *the_key){
	self->key = the_key;
	self->set = true;
};
















