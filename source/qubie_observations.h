//implementation summary of qubie observations and contact records

#include "qubie_t.h"

//constructors

contact_record_t *make_contact_record(const device_id_t device_id,
								const time_t contact_time,
								const rssi_t rssi,
								const frequency_t frequency
								);

device_id_t make_device_id(mac_t raw_identifier);

// ====================================================================
// bon QUERIES
// ====================================================================

bool observations_empty();

// ====================================================================
// @bon COMMANDS
// ====================================================================

void add_contact_record( contact_record_t the_contact_record);
