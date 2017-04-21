//qubie log module implementation summary

#include "qubie_t.h"
#include "qubie_log.h"
#include <sodium.h>
#include <time.h> //@TODO take only what is needed from this library
#include <assert.h>

char *make_log_message(message_t message_type, void *message_val, qubie_time_t message_time){
	int buff_size = 512;
	char *buff = malloc(sizeof(char) * buff_size);
	switch(message_type){
	case QUBIE_STATE:
		snprintf(buff, buff_size, "%lu qubie state changed to: %s", (unsigned long)message_time, (char *)message_val);
		break;
	case QUBIE_DETECTED_DEVICE:
		snprintf(buff, buff_size, "%lu device detected with ID:%s, rssi:%du, frequency: %du MHz",
				(unsigned long)message_time,
				((contact_record_t *)message_val)->device_id.identifier_string,
				(unsigned int)((contact_record_t *)message_val)->rssi,
				(unsigned int)((contact_record_t *)message_val)->frequency
				);
		break;
	case WIFI_MONITOR_STATE:
		snprintf(buff, buff_size, "%lu wifi monitor %s", (unsigned long)message_time, (char *)message_val);
		break;
	case WIFI_MONITOR_FREQUENCY:
		snprintf(buff, buff_size, "%lu wifi monitor frequency changed to: %du", (unsigned long)message_time, (unsigned int)message_val);
		break;
	case WIFI_MONITOR_AUTO_HOPPING:
		snprintf(buff, buff_size, "%lu wifi monitor auto hopping set to: %du",(unsigned long) message_time, (unsigned int)message_val);
		break;
	default:
		//assert(false)
		assert(false);

	}
	return buff;
};


//constructors
log_entry_t *make_log_entry(message_t message_type, void* message_val){
	log_entry_t *log_entry_struct = malloc(sizeof(struct log_entry));
	qubie_time_t message_time = current_time(NULL);
	char *message = make_log_message(message_type, message_val, message_time);
	log_entry_struct->message = message;
	log_entry_struct->time = message_time;
	return log_entry_struct;
};

qubie_logger_t *make_qubie_logger(const char* filename){
	qubie_logger_t *qubie_logger_struct = malloc(sizeof(struct qubie_logger));
	qubie_logger_struct->size = 0;
	qubie_logger_struct->last_entry=NULL;
	qubie_logger_struct->log_fp = fopen(filename, "w");
	return qubie_logger_struct;
};

//destructors
void free_log_entry(log_entry_t *the_entry){
	if (the_entry) {
		printf("DEBUG - freeing the log entry: %s\n",the_entry->message);
		free(the_entry->message);
		//free(the_entry->message_val);
		free(the_entry);
	}
};

// ====================================================================
// @bon QUERIES
// ====================================================================

//@ ensures (0 == size) == Result
bool log_empty(qubie_logger_t *self){
	return 0==self->size;
};

/*@ TODO ensures log_contains(the_log_entry);
 */
bool logged(qubie_logger_t *self, message_t message_type, void* message_val){

	return (self->last_entry) &&
			(message_type == self->last_entry->message_type) &&
			(message_val == self->last_entry->message_val);
};

qubie_time_t current_time(qubie_time_t *seconds){
	//@TODO this is OS specific
	return time((time_t *)seconds);
};

// ====================================================================
// @bon COMMANDS
// ====================================================================


void write_log_entry_to_file(qubie_logger_t *self, log_entry_t *the_entry){
	fprintf(self->log_fp, "%s\n", the_entry->message);
	fflush(self->log_fp);
};



/*@ ensures logged(message_type, message_val);
 *  @TODO ensures delta log[size];
 */
void add_log_entry(qubie_logger_t *self, message_t message_type, void* message_val){
	log_entry_t *the_entry = make_log_entry(message_type, message_val);
	write_log_entry_to_file(self, the_entry);
	free_log_entry(self->last_entry);
	self->last_entry = the_entry;
};





