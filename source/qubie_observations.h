//implementation summary of qubie observations and contact records

#include "qubie_t.h"

//constructors
contact_record_t *make_observations();
contact_record_t make_contact_record(device_id_t device_id, rssi_t rssi, frequency_t frequency);
device_id_t make_device_id(const bool encrypted, const mac_t *identifier_string);

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool observations_empty();

//@ TODO ensures the_contact_record in observasions
bool observations_contains(contact_record_t *the_contact_record);

/*@ ensures old size + 1 == size;
 * 	ensures observations_contains(the_contact_record);
 */
void add_contact_record(contact_record_t *the_contact_record);
