//implementation summary of qubie observations and contact records

#include "qubie_t.h"

//constructors
qubie_observations_t make_qubie_observations();

contact_record_t make_contact_record(const device_id_t device_id,
								const qubie_time_t contact_time,
								const rssi_t rssi,
								const frequency_t frequency
								);

device_id_t make_device_id(mac_t raw_identifier);

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool observations_empty();

/*@rTODO ensures the_contact_record in observations
 */
bool observations_contains( contact_record_t the_contact_record);

/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record( contact_record_t the_contact_record);
