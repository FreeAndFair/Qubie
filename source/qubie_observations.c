//implementation summary of qubie observations and contact records

#include "qubie_t.h"
#include "qubie_observations.h""
#include <stddef.h>
#include <stdbool.h>

//constructors
observations_t *make_observations();
contact_record_t make_contact_record(device_id_t device_id, rssi_t rssi, frequency_t frequency){

};
device_id_t make_device_id(const bool encrypted, const mac_t *identifier_string){
	struct device_id_t *device_id_struct = malloc(sizeof(struct device_id));
	device_id_struct->encrypted = encrypted;
	device_id_struct->identifier_string = identifier_string;
};

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool observations_empty(observations_t *self){
	//assumes linked list format
	return 0 == self->size;
};

//@ TODO ensures the_contact_record in observasions
bool observations_contains(contact_record_t the_contact_record);

/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record(contact_record_t *the_contact_record);





