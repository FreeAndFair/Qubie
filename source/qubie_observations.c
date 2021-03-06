//implementation summary of qubie observations and contact records

#include "qubie_defaults.h"
#include "qubie.h"
#include "qubie.acsl"
#include "qubie_observations.h"
#include "qubie_log.h"
#include "qubie_keyed_hash.h"
#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


//globals
extern qubie_t the_qubie;

//helper functions
//design format: device,time,rssi,frequency
/*@ ensures the_last_contact_record == the_contact_record;
   	assigns *the_qubie.observations.observations_fp;
 */
void __write_contact_record_to_file( contact_record_t the_contact_record){
	fprintf(the_qubie.observations.observations_fp, "%s,%lu,%d,%d\n",
			the_contact_record.device_id.identifier_string,
			the_contact_record.contact_time,
			the_contact_record.rssi,
			the_contact_record.frequency
			);
	fflush(the_qubie.observations.observations_fp);
};

//constructors

/*@ requires true;
   	ensures \result->device_id == device_id;
   	ensures \result->contact_time == contact_time;
   	ensures \result->rssi == rssi;
   	ensures \result->frequency == frequency;
   	assigns \nothing;
 */
contact_record_t *make_contact_record( device_id_t const device_id,
								time_t const contact_time,
								const rssi_t rssi,
								const frequency_t frequency
								){
	contact_record_t *contact_record_struct = malloc (sizeof(struct contact_record));
	memcpy((device_id_t *)&contact_record_struct->device_id, &device_id,sizeof(struct device_id));
	//design device_id is only used in the context of the contact record
	*(time_t *)&contact_record_struct->contact_time = contact_time;
	*(rssi_t *)&contact_record_struct->rssi = rssi;
	*(frequency_t *)&contact_record_struct->frequency = frequency;
	return contact_record_struct;
};
/*@
   requires !ENCRYPTED_DEFAULT ==> TEST_MODE;
   //TODO ensures identifier_string is created from raw_identifier
   assigns \nothing;
 */
device_id_t make_device_id(mac_t raw_identifier){
	device_id_t *device_id_struct = malloc(sizeof(struct device_id));
	char const * identifier_string;
	device_id_struct->encrypted = ENCRYPTED_DEFAULT;
	//@assert(ENCRYPTED_DEFAULT || TEST_MODE);
	assert(ENCRYPTED_DEFAULT || TEST_MODE);
	identifier_string = hashed_string(device_id_struct->encrypted, raw_identifier);
	strncpy((char *)device_id_struct->identifier_string, identifier_string, MAC_STRING_LEN);
	free((void *)identifier_string);
	return *device_id_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================

/*@ ensures (0 == the_qubie.observations.size) == \result;
   	assigns \nothing;
 */
bool observations_empty(){
	return 0 == the_qubie.observations.size;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@
   	ensures \old(the_qubie.observations.size) + 1 == the_qubie.observations.size;
   	ensures the_last_contact_record == the_contact_record;
   	assigns \nothing;
 */
void add_contact_record( contact_record_t the_contact_record){
	__write_contact_record_to_file(the_contact_record);
	the_qubie.observations.size++;
};





