//implementation summary of qubie observations and contact records

#include "qubie_t.h"
#include "qubie_defaults.h"
#include "qubie_observations.h"
#include <stddef.h>
#include <stdbool.h>
#include <stdlib.h>

//constructors
qubie_observations_t *make_qubie_observations(){
	observations_t *observations_struct = malloc(sizeof(struct observations));
	observations_struct->size = 0;
	observations_struct->first=NULL;
	observations_struct->last=NULL;
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
	contact_record_struct->rssi = rssi;
	contact_record_struct->frequency = frequency;
	contact_record_struct->prev = NULL;
	return contact_record_struct;
};

device_id_t *make_device_id(mac_t *identifier_string){
	device_id_t *device_id_struct = malloc(sizeof(struct device_id));
	device_id_struct->encrypted = ENCRYPTED_DEFAULT;
	device_id_struct->identifier_string = identifier_string;
	return device_id_struct;
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

/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record(qubie_observations_t *self, contact_record_t *the_contact_record){
	the_contact_record->prev = self->last;
	self->last = the_contact_record;
	self->size++;
};





