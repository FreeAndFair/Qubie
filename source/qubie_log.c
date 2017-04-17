//qubie log module implementation summary

#include "qubie_t.h"
#include "qubie_log.h"

//constructors
log_entry_t *make_log_entry(message_t message_type, void* message_val){
	log_entry_t *log_entry_struct = malloc(sizeof(struct log_entry));
	char *message = malloc(sizeof(message_val));
	memcpy(message, message_val, sizeof(message_val));
	log_entry_struct->message = message;
	log_entry_struct->time = current_time();
	return log_entry_struct;
};

qubie_logger_t *make_qubie_logger();

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool log_empty(qubie_t *self){
	return !ftell(self->log);
};

/*@ TODO ensures log_contains(the_log_entry);
 */
bool logged(qubie_logger_t *self, message_t message_type, void* message_val){
	//@TODO
	//@assert(false)
	assert(false);
	return false;
};

qubie_time_t current_time(){
	//@TODO this is OS specific
	//@assert(false);
	assert(false);
	return 0;
};

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ ensures logged(message_type, message_val);
 *  @TODO ensures delta log[size];
 */
void add_log_entry(qubie_t *self, message_t message_type, void* message_val){

};



