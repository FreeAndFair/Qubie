//implementation summary of qubie blootooth communicator

#include "qubie_t.h"
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <sodium.h>
#include "qubie_keyed_hash.h"

//constructor
keyed_hash_t *make_keyed_hash(){
	struct keyed_hash *keyed_hash_struct = malloc(sizeof(struct keyed_hash));
	keyed_hash_struct->set=false;
	qubie_key_t *the_key = create_random_key();
	set_key(keyed_hash_struct, the_key);
	return keyed_hash_struct;
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

/* convert array of binary bytes to a printable (\0 delimited) array of char
 * from libsodium package
 * char *sodium_bin2hex(char * const hex, const size_t hex_maxlen,
 *                   const unsigned char * const bin, const size_t bin_len);
 */
char const * binToString(unsigned char * the_binary, const size_t num_bytes){
	const size_t hashed_string_max_length = num_bytes * 2 +1;
	char * const hashed_string = malloc(hashed_string_max_length);
	char *sodium_return;
	sodium_return = sodium_bin2hex(hashed_string, hashed_string_max_length, the_binary, num_bytes);
	assert(!sodium_return);
	return hashed_string;
}


/*@ requires set
 * 	ensures hash.hash(the_string) == Result;
 */
char const *hashed_string(keyed_hash_t *self, bool encrypted, mac_t *the_string){
	unsigned char *mac_buf;
	if(encrypted) {
		//@design TODO keep a single static buffer instead of allocating and freeing every time.
		mac_buf = malloc(sizeof(mac_t) * MAC_SIZE);
		crypto_generichash(mac_buf, MAC_SIZE,
	                   *the_string, MAC_SIZE,
	                   (const unsigned char *)self->key, KEY_SIZE);
	} else {
		mac_buf = (unsigned char *)the_string;
	}
	if(encrypted) {
		free(mac_buf);
	}
	//@TBD do I need to free the_string?
	return binToString(mac_buf, MAC_SIZE);
};

//implemetned with libsodium
qubie_key_t *create_random_key(){
	assert(!sodium_init());
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
















