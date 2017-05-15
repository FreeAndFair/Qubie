//qubie log module implementation summary

#include "qubie_t.h"
#include "qubie.acsl"
#include "qubie_log.h"
//#include <sodium.h>
#include <time.h>// TODO take only what is needed from this library
#include <assert.h>
#include <string.h>

//globals
extern qubie_t the_qubie;
//static qubie_logger_t *self = &the_qubie.log;

//helper functions
/*@	requires \valid(the_qubie.log.log_fp);
   	assigns *the_qubie.log.log_fp;
 */
void __write_log_entry_to_file( log_entry_t the_entry){
	fprintf(the_qubie.log.log_fp, "%s\n", the_entry.message);
	fflush(the_qubie.log.log_fp);
};


//constructors
/*@ //requires \valid(message_val);
   	ensures \valid_read(\result);
   	assigns \nothing;
 */
char const *make_log_message(message_t message_type, void *message_val, qubie_time_t message_time){
	int buff_size = MAX_MESSAGE_LEN;
	char *buff = malloc(sizeof(char) * buff_size);
	switch((int)message_type){
	case QUBIE_STATE:
		snprintf(buff, buff_size, "%lu qubie state changed to: %s", (unsigned long)message_time, (char *)message_val);
		break;
	case QUBIE_DETECTED_DEVICE:
		snprintf(buff, buff_size, "%lu device detected with ID:%s, rssi:%d, frequency: %d MHz",
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
		snprintf(buff, buff_size, "%lu wifi monitor frequency changed to: %d", (unsigned long)message_time, (unsigned int)message_val);
		break;
	case WIFI_MONITOR_AUTO_HOPPING:
		snprintf(buff, buff_size, "%lu wifi monitor auto hopping set to: %d",(unsigned long) message_time, (unsigned int)message_val);
		break;
	case WIFI_MONITOR_UNSUPPORTED_PACKET:
		snprintf(buff, buff_size, "%lu wifi monitor detected unsupported packet: %s",(unsigned long) message_time, (char *)message_val);
		break;
	case ERROR_MESSAGE:
		snprintf(buff, buff_size, "%lu ERROR: %s",(unsigned long) message_time, (char *)message_val);
		break;
	default:
		//@assert(false);
		assert(false);

	}
	return (char const *)buff;
};

/*@ //requires \valid(message_val);
   	//ensures \valid_read(\result);
   	assigns \nothing;
 */
log_entry_t make_log_entry(message_t message_type, void* message_val){
	log_entry_t *log_entry_struct = malloc(sizeof(struct log_entry));
	qubie_time_t message_time = current_time(NULL);
	char const *message = make_log_message(message_type, message_val, message_time);
	memcpy((char *)log_entry_struct->message, message, sizeof(char[MAX_MESSAGE_LEN]));
	free((char *)message);
	*(qubie_time_t *)&log_entry_struct->time = message_time;
	return *log_entry_struct;
};


qubie_logger_t make_qubie_logger(const char* filename){
	qubie_logger_t *qubie_logger_struct = malloc(sizeof(struct qubie_logger));
	qubie_logger_struct->size = 0;
	//qubie_logger_struct->last_entry=NULL;
	qubie_logger_struct->log_fp = fopen(filename, "w");
	return *qubie_logger_struct;
};

// ====================================================================
// @bon QUERIES
// ====================================================================

/*@ ensures (0 == the_qubie.log.size) == \result;
   	assigns \nothing;
 */
bool log_empty(){
	return 0==the_qubie.log.size;
};

/*@	//design this method is only for defining contracts
   //requires \valid(message_val);
   ensures \result == ((the_last_log_entry_message_type == message_type)
   					&& (the_last_log_entry_message_val == message_val));
   	assigns \nothing;
 */
bool logged( message_t message_type, void* message_val){
	//@assert(false);
	assert(false);
	//return (the_qubie.log.last_entry) &&
	//		(message_type == the_qubie.log.last_entry->message_type) &&
	//		(message_val == the_qubie.log.last_entry->message_val);
	return false;
};

//@ assigns \nothing;
qubie_time_t current_time(qubie_time_t *seconds){
	return time((time_t *)seconds);
};

// ====================================================================
// @bon COMMANDS
// ====================================================================


/*@ //requires \valid(message_val);
   	ensures the_last_log_entry_message_type == message_type;
   	ensures the_last_log_entry_message_val == message_val;

   	assigns \nothing;
 */
void add_log_entry( message_t message_type, void* message_val){
	log_entry_t the_entry = make_log_entry(message_type, message_val);
	__write_log_entry_to_file(the_entry);
	//free_log_entry(the_qubie.log.last_entry);
	//the_qubie.log.last_entry = the_entry;
};





