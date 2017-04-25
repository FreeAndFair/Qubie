//implementation summary of qubie blootooth communicator

#include "qubie_t.h"
#include "qubie_keyed_hash.h"
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <sodium.h>
#include <string.h>

//globals
extern qubie_t the_qubie;
static keyed_hash_t *self = &the_qubie.wifi_monitor.keyed_hash;

//constructor
keyed_hash_t make_keyed_hash(){
	struct keyed_hash *keyed_hash_struct = malloc(sizeof(struct keyed_hash));
	keyed_hash_struct->set=false;
	//@ TODO key is set by wifi monitor but perhaps it should be done here:
	//qubie_key_t *the_key = create_random_key();
	//set_key(keyed_hash_struct, the_key);
	return *keyed_hash_struct;
};

//helper functions

//@requires num_bytes == the_binary.length
//@TODO ensures Result is an exact string representation of the binary
char * const __binToString(unsigned char * the_binary, const size_t num_bytes){
	const size_t string_max_length = num_bytes * 2 +1;
	char * the_string = (char *)malloc(string_max_length);
	char *string_ptr = the_string;
	unsigned char * binary_ptr = the_binary;
	//*(string_ptr+num_bytes) = '\0';
	for (int i = 0; i < num_bytes; i++)
	{
		string_ptr += sprintf(string_ptr, "%02X", (unsigned int)*(binary_ptr++));
	}
	*(string_ptr+1) = '\0';
	printf("DEBUG - __binToString result: %s\n", the_string);
	return (char * const)the_string;
};


// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures write-once
bool set(){
	return self->set;
};

const qubie_key_t *key(){;
	return &self->key;
};

/*@ requires set
 * 	ensures hash.hash(the_string) == Result;
 */
char const *hashed_string( bool encrypted, mac_t the_string){
	unsigned char *mac_buf;
	char const *string_ptr;
	if(encrypted) {
		//@design TBD keep a single static buffer instead of allocating and freeing every time.
		mac_buf = malloc(sizeof(mac_t) * MAC_SIZE);
		crypto_generichash(mac_buf, MAC_SIZE, the_string, MAC_SIZE, (const unsigned char *)self->key, KEY_SIZE);
		string_ptr = __binToString(mac_buf, MAC_SIZE);
		free(mac_buf);
	} else {
		string_ptr = __binToString((unsigned char *)the_string, MAC_SIZE);
	}
	return string_ptr;
};

//implemetned with libsodium
qubie_key_t *create_random_key(){
	unsigned char sodium_init_ret = sodium_init();
	printf("DEBUG - sodium_init return val: %d\n", sodium_init_ret);
	//@assert(!sodium_init_ret);
	assert(!sodium_init_ret);
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
void set_key( qubie_key_t *the_key){
	memcpy((qubie_key_t *)&self->key,the_key,sizeof(qubie_key_t));
	//@design this is the only location where set can be modified
	*(bool *)&self->set = true;
};
















