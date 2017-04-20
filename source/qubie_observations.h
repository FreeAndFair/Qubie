//implementation summary of qubie observations and contact records

#include "qubie_t.h"

//constructors
qubie_observations_t *make_qubie_observations();

contact_record_t *make_contact_record(device_id_t *device_id,
								qubie_time_t contact_time,
								rssi_t rssi,
								frequency_t frequency
								);

device_id_t *make_device_id(keyed_hash_t *hash, mac_t *raw_identifier);

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool observations_empty(qubie_observations_t *self);

/*@rTODO ensures the_contact_record in observations
 */
bool observations_contains(qubie_observations_t *self, contact_record_t *the_contact_record);

/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record(qubie_observations_t *self, contact_record_t *the_contact_record);
