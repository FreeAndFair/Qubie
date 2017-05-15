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

//helper functions

//TODO ensures Result is an exact string representation of the binary
/*@	requires  num_bytes == MAC_SIZE;
  	requires \valid_read(the_binary + (0 .. num_bytes));
   	ensures \valid_read(\result + (0 .. num_bytes * 2 +1));
   	assigns \nothing;
 */
char * const __binToString(unsigned char * the_binary, const size_t num_bytes){
	const size_t string_max_length = num_bytes * 2 +1;
	char * the_string = (char *)malloc(string_max_length);
	char *string_ptr = the_string;
	unsigned char * binary_ptr = the_binary;
	//*(string_ptr+num_bytes) = '\0';
	/*@	loop invariant 0<= i < num_bytes;
	 	loop invariant \at(string_ptr,Pre) +2*i == string_ptr;
	 	loop invariant \at(binary_ptr,Pre) +i == binary_ptr;
	 	loop variant num_bytes - i;
	 */
	for (int i = 0; i < num_bytes; i++)
	{
		sprintf(string_ptr, "%02X", (unsigned int)*(binary_ptr));
		string_ptr += 2;
		binary_ptr+=1;
	}
	*(string_ptr+1) = '\0';
	//printf("DEBUG - __binToString result: %s\n", the_string);
	return (char * const)the_string;
};

//constructor
keyed_hash_t make_keyed_hash(){
	struct keyed_hash *keyed_hash_struct = malloc(sizeof(struct keyed_hash));
	keyed_hash_struct->set=false;
//	TODO key is set by wifi monitor but perhaps it should be done here:
	//qubie_key_t *the_key = create_random_key();
	//set_key(keyed_hash_struct, the_key);
	return *keyed_hash_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================
//TODO ensures write-once
/*@ ensures \result == self->set;
   	assigns \nothing;
 */
bool set(){
	return self->set;
};

// only for contract purposes
//const qubie_key_t *key(){;
//	return &self->key;
//};

//TODO ensures hash.hash(the_string) == Result;
/*@ requires self->set;
   	ensures \valid_read(\result + (0 .. MAC_STRING_LEN));
   	assigns \nothing;
 */
char const *hashed_string( bool encrypted, mac_t the_string){
	unsigned char *mac_buf;
	char const *string_ptr;
	if(encrypted) {
		//design// TBD keep a single static buffer instead of allocating and freeing every time.
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
/*@ requires true;
   	ensures \valid_read(\result + (0 .. KEY_SIZE));
   	assigns \nothing;
 */
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

/*@ requires !self->set;
   	ensures self->key == *the_key;
   	ensures self->set;
   	assigns *(self->key + (0 .. KEY_SIZE-1)), self->set;
 */
void set_key( qubie_key_t *the_key){
	memcpy((qubie_key_t *)&self->key,the_key,sizeof(qubie_key_t));
	//design this is the only location where set can be modified
	*(bool *)&self->set = true;
};
















