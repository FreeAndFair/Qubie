//implementation summary of qubie observations and contact records

#include "qubie.h"
#include "qubie_defaults.h"
#include "qubie_observations.h"
#include "qubie_log.h"
#include "qubie_keyed_hash.h"
#include <sodium.h> //@design for converting mac/key arrays to strings with rawToChar
#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

//constructors
qubie_observations_t *make_qubie_observations(const char *filename){
	qubie_observations_t *observations_struct = malloc(sizeof(struct observations));
	observations_struct->size = 0;
	observations_struct->last=NULL;
	observations_struct->observations_fp = fopen(filename, "w");
	//@design print header file
	//@TBD the best way to sync header with data
	fprintf(observations_struct->observations_fp, "device,time,rssi,frequency");
	fflush(observations_struct->observations_fp);
	return observations_struct;
};

contact_record_t *make_contact_record(device_id_t *device_id,
								qubie_time_t contact_time,
								rssi_t rssi,
								frequency_t frequency
								){
	contact_record_t *contact_record_struct = malloc (sizeof(struct contact_record));
	contact_record_struct->device_id = device_id;
	contact_record_struct->contact_time = contact_time;
	*(rssi_t *)&contact_record_struct->rssi = rssi;
	*(frequency_t *)&contact_record_struct->frequency = frequency;
	return contact_record_struct;
};

device_id_t *make_device_id(keyed_hash_t *hash, mac_t *raw_identifier){
	device_id_t *device_id_struct = malloc(sizeof(struct device_id));
	device_id_struct->encrypted = ENCRYPTED_DEFAULT;
	assert(ENCRYPTED_DEFAULT); //@TODO modify to allow unencrypted in test mode
	device_id_struct->identifier_string = hashed_string(hash, device_id_struct->encrypted, raw_identifier);
	return device_id_struct;
};

//destructors
void free_contact_record(contact_record_t *the_contact_record){
	//free(the_contact_record->device_id->identifier_string);
	free(the_contact_record->device_id);
	free(the_contact_record);
};

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool observations_empty(qubie_observations_t *self){
	//assumes linked list format
	return 0 == self->size;
};

//@design helper function to compare contact records for the sake of checking existence
bool contact_records_match(contact_record_t *cr1, contact_record_t *cr2){
	//return false if the contact records are not well formed
	//@design each contact record is only created once so it is enough to compare the addresses
	return  cr1 == cr2;
};

/*@ensures the_contact_record in observations
 */
bool observations_contains(qubie_observations_t *self, contact_record_t *the_contact_record){
	contact_record_t *tmp_cr = self->last;
	bool found = false;

	while (!found && tmp_cr) {
		found = contact_records_match(tmp_cr, the_contact_record);
	};
	return found;
};

/*@ ensures observations_contains(the_contact_record);
 */
//@design format: device,time,rssi,frequency
void write_contact_record_to_file(qubie_observations_t *self, contact_record_t *the_contact_record){
	//@TBD do I need to implement according to binary files?
	fprintf(self->observations_fp, "%s,%lu,%du,%du",
			the_contact_record->device_id->identifier_string,
			the_contact_record->contact_time,
			the_contact_record->rssi,
			the_contact_record->frequency
			);
	fflush(self->observations_fp);
};


/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record(qubie_observations_t *self, contact_record_t *the_contact_record){
	free_contact_record(self->last);
	self->last = the_contact_record;
	write_contact_record_to_file(self, the_contact_record);
	self->size++;
};





