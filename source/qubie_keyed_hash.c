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
/*@
  	requires \valid_read(the_binary + (0 .. MAC_SIZE));
   	ensures \valid_read(\result + (0 .. MAC_STRING_LEN));
   	assigns \nothing;
 */
char * const __binToString(unsigned char * the_binary){
	//const size_t string_max_length = num_bytes * 2 +1;
	char * the_string = (char *)malloc(MAC_STRING_LEN);
	char ascii_array[17] = "0123456789ABCDEF";
	//char *string_ptr = the_string;
	//unsigned char * binary_ptr = the_binary;
	//*(string_ptr+num_bytes) = '\0';
	/*@	loop invariant 0<= i < MAC_SIZE;
	 	//loop invariant \at(string_ptr,Pre) +2*i == string_ptr;
	 	//loop invariant \at(binary_ptr,Pre) +i == binary_ptr;
	 	loop variant MAC_SIZE - i;
	 */
	for (int i = 0; i < MAC_SIZE; i++)
	{
		//sprintf(the_string[2*i], "%02X", the_binary[i]);
		the_string[2*i] = ascii_array[the_binary[i]>>4];
		the_string[2*i+1] = ascii_array[the_binary[i] & 0xF];
		//string_ptr += 2;
		//binary_ptr+=1;
	}
	//*(string_ptr+1) = '\0';
	the_string[MAC_STRING_LEN - 1] = '\0';
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


void __crypto_generichash( unsigned char *mac_buf, mac_t the_string){
	crypto_generichash(mac_buf, MAC_SIZE, the_string, MAC_SIZE, (const unsigned char *)self->key, KEY_SIZE);
};


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
		__crypto_generichash(mac_buf, the_string);
		//crypto_generichash(mac_buf, MAC_SIZE, the_string, MAC_SIZE, (const unsigned char *)self->key, KEY_SIZE);
		string_ptr = __binToString(mac_buf);
		free(mac_buf);
	} else {
		string_ptr = __binToString((unsigned char *)the_string);
	}
	return string_ptr;
};

// calls function from sodium.h
void __randombytes_buf(qubie_key_t * key_buf){
	randombytes_buf((void *)key_buf, (const size_t)KEY_SIZE);
};

//implemented with libsodium
/*@ requires true;
   	ensures \valid_read(\result + (0 .. KEY_SIZE));
   	assigns \nothing;
 */
qubie_key_t *create_random_key(){
	unsigned char sodium_init_ret = sodium_init();
	printf("DEBUG - sodium_init return val: %d\n", sodium_init_ret);
	//@assert(!sodium_init_ret);
	assert(!sodium_init_ret);
	qubie_key_t *key_buf = malloc(sizeof(qubie_key_t));
	__randombytes_buf(key_buf);
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
















