//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_defaults.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_keyed_hash.h"
#include "wifi_stub.h"
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <pcap.h>

//globals
extern qubie_t the_qubie;
static wifi_monitor_t *self = &the_qubie.wifi_monitor;
static pcap_t *handle;
static const byte *current_packet;

//constructor
wifi_monitor_t make_wifi_monitor(qubie_t *qubie){
	wifi_monitor_t *wifi_monitor_struct=malloc(sizeof(struct wifi_monitor));
	wifi_monitor_struct->wifi_booted = false;
	wifi_monitor_struct->wifi_running = false;
	wifi_monitor_struct->auto_hopping = WIFI_AUTO_HOPPING_DEFAULT;
	wifi_monitor_struct->keyed_hash = make_keyed_hash();
	//wifi_monitor_struct->frequency_range = wifi_channels;
	//@design by default start at the begining of the spectrum
	//wifi_monitor_struct->frequency = WIFI_FREQUENCY_DEFAULT;
	//wifi_monitor_struct->qubie = qubie;
	return *wifi_monitor_struct;
};

// ====================================================================
// @bon PRIVATE
// ====================================================================

//queries


//commands

/*@ requires !\valid(handle)
 * 	ensures \valid(handle)
 * 	assigns handle
 */
void __open_wifi_interface_from_file(char * filename){
	FILE * pcap_fp = fopen(PCAP_TEST_FILE, "r");
	char pcap_error_buffer[PCAP_ERRBUF_SIZE];
	handle = pcap_fopen_offline(pcap_fp, pcap_error_buffer);
};

/*@ requires !\valid(handle)
 * 	ensures \valid(handle)
 * 	assigns handle
 */
void __open_wifi_interface() {
    char pcap_error_buffer[PCAP_ERRBUF_SIZE];
    char *device;

    device = pcap_lookupdev(pcap_error_buffer);
    if (!device){
    	add_log_entry(ERROR_MESSAGE, pcap_error_buffer);
    	//TODO handle errors
    	assert(false);
    }
    handle = pcap_open_live(device,BUFSIZ, PACKET_COUNT_LIMIT, WIFI_TIMEOUT, pcap_error_buffer);
}

/*@ requires !\valid(handle)
 * 	ensures \valid(handle)
 * 	assigns handle
 * 	TODO enables monitor_mode
 */
void __boot_wifi_interface(){
#ifdef PCAP_TEST_FILE
	__open_wifi_interface_from_file(PCAP_TEST_FILE);
#else
	__open_wifi_interface();
#endif
	//enable monitor mode
	pcap_set_rfmon(handle, 1);
	//TBD set filters
};

/*@ requires wifi_interface_polled
 *	ensures Result implies \valid(current_packet)
 */
bool __packet_ready() {
	return current_packet != NULL;
}

/*@ requires __packet_ready()
 * 	TODO result is length of rtap header
 */
uint __rtap_length() {
	return (uint)current_packet[3]<<8|(uint)current_packet[2];
}

/*@ requires __packet_ready()
 * 	TODO ensures packet has valid rtap header
 */
bool __good_packet() {
	int dlt; //datalink type
	unsigned int rtap_len;

	dlt = pcap_datalink(handle);
	rtap_len = __rtap_length();
	//TODO check that the rtap header is in the supported format
	//printf("DEBUG - dlt: %d, rtal_len: %d\n", dlt, rtap_len);
	return(RADIOTAP_DATALINK_VAL==dlt && rtap_len >= MIN_RTAP_LEN);
};


/*
 * Return codes for pcap_read() are:
 *   -  0: timeout
 *   - -1: error
 *   - -2: loop was broken out of with pcap_breakloop()
 *   - >1: OK
 * The first one ('0') conflicts with the return code of 0 from
 * pcap_offline_read() meaning "end of file".
*/


/*@ requires running
 * 	ensures wifi_interface_polled
 */
void __get_packet(){
	const byte *packet = NULL;
	struct pcap_pkthdr *header_ptr;
	int res = pcap_next_ex(handle, &header_ptr, &packet);
	if (-1 == res) {
		//printf("DEBUG - packet error.\n");
		add_log_entry(ERROR_MESSAGE, pcap_geterr(handle));
		packet = NULL; //TBD is this needed?
	} else if (0 == res) {
		//printf("DEBUG - No packet found before timeout.\n");
		packet = NULL; //TBD is this needed?
	} else if (-2 == res) {
		//@assert(TEST_MODE)
		assert(TEST_MODE);
		//printf("DEBUG - no more packets in pcap test file.\n");
	}
	current_packet = packet;
	//printf("DEBUG - res: %d, current_packet: %d\n",res, (uint)current_packet);
};

/*@	requires __good_packet()
 * 	ensures !__packet_ready()
 * 	TODO ensures observations.contains(packet)
 */
void __process_packet() {
	const byte *packet = current_packet;
	mac_t *smac_ptr;
	uint rtap_len = __rtap_length();
	frequency_t the_frequency = (uint)packet[rtap_len - 7]<<8|(uint)packet[rtap_len - 8];
	rssi_t the_rssi = packet[rtap_len - 4];
	//@design skip over the rtap header and the dmac field of the ethernet header to point to the smac field
	smac_ptr = (mac_t *)(packet + rtap_len + MAC_SIZE);
	report_detected_device(*smac_ptr, the_rssi, the_frequency);
}

/*@ requires running
 *
 * 	TODO __good_packet() => observations.contains(packet)
 */
void __poll_wifi_interface(){
	int collected_packets = 0;
	bool more_packets = true;
	while (collected_packets < PACKET_COUNT_LIMIT && more_packets) {
		//printf("DEBUG - getting packet\n");
		__get_packet();
		more_packets = __packet_ready();
		if (more_packets && __good_packet()){
			//printf("DEBUG - processing packet\n");
			__process_packet();
		}
		collected_packets++;
	}

}

// ====================================================================
// @bon QUERIES
// ====================================================================


bool wifi_booted(){
	return self->wifi_booted;
};
bool wifi_running(){
	return self->wifi_running;
};
bool auto_hopping(){
	return self->auto_hopping;
};
keyed_hash_t *keyed_hash(){
	return &self->keyed_hash;
};
const frequency_t* frequency_range(){
	return self->frequency_range;
};
frequency_t frequency(){
	return self->frequency;
};
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires !booted
 * ensures booted
 * ensures keyed_hash.set();
 * ensures qubie.log.logged(WIFI_MONITOR_STATE, "booted")
 * TODO ensures frequency in frequency_range
 */
void boot_wifi(){
	qubie_key_t *the_key = create_random_key();
	set_key(the_key);
	free(the_key);
	self->frequency = self->frequency_range[WIFI_CHANNEL_DEFAULT];
	//@TODO boot actual wifi device
	__boot_wifi_interface();
	add_log_entry(WIFI_MONITOR_STATE, (void *)"booted");
	self->wifi_booted = true;
};

/*@ requires booted
 * 	requires !running
 * 	ensures running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "running")
 */
void start_wifi(){
	//@TODO start actual wifi device
	add_log_entry(WIFI_MONITOR_STATE, (void *)"running");
	self->wifi_running = true;
};

/*@ requires running
 * 	ensures !running
 * 	ensures qubie.log.logged(WIFI_MONITOR_STATE, "stopped")
 */
void stop_wifi(){
	//@TODO stop actual wifi device
	add_log_entry(WIFI_MONITOR_STATE, (void *)"stopped");
	self->wifi_running = false;
};

/*@ ensures frequency==the_frequency;
 * 	ensures qubie.log.logged(WIFI_MONITOR_FREQUENCY, the_frequency)
 */
//delta {frequency, qubie.log};
void set_frequency( frequency_t the_frequency){
	self->frequency = the_frequency;
	//@TODO set frequency of actual wifi device
	add_log_entry(WIFI_MONITOR_FREQUENCY, (void *)the_frequency);
};

/*@ ensures auto_hopping==the_truth_val;
 * 	ensures qubie.log.logged(WIFI_MONITOR_AUTO_HOPPING, the_truth_val)
 */
//delta {auto_hopping, qubie.log};
void set_auto_hopping( bool the_truth_val){
	self->auto_hopping = the_truth_val;
	//@TODO set auto hopping state of actual wifi device
	add_log_entry(WIFI_MONITOR_AUTO_HOPPING, (void *)the_truth_val);

};

/*@ ensures qubie.observations.contains(CONTACT_RECORD.make(keyed_hash, the_mac_address, the_signal_strength));
 * 	ensures qubie.log.logged(WIFI_MONITOR_DETECTED_DEVICE, {the_mac_address, the_signal_strength})
 */
// delta {qubie.observations, qubie.log};
void report_detected_device(
		mac_t the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		){
	//printf("DEBUG - making device id\n");
	device_id_t the_device_id = make_device_id(the_mac_address);
	//printf("DEBUG - making contact record\n");
	contact_record_t the_contact_record = make_contact_record(the_device_id, current_time(NULL), the_signal_strength, the_frequency);
	//printf("DEBUG - recording observation\n");
	record_observation(the_contact_record);
};

/* @requires message.length < MAX_MESSAGE_LEN - 100
 * @ensures qubie.log.logged(WIFI_MONITOR_UNSUPPORTED_PACKET, message)
 */
void report_unsupported_packet(char * message){
	//@design message length should be less than (MAX_MESSAGE_LEN - 100) to avoid being truncated
	add_log_entry(WIFI_MONITOR_UNSUPPORTED_PACKET, (void *)message);
};

/*@ requires running
 *
 */
void poll_wifi_monitor(){
	__poll_wifi_interface();
	if(auto_hopping()){
		update_monitored_frequency();
	}
};



