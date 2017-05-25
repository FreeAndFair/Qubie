//implementation summary of qubie wifi monitor

#include "qubie_t.h"
#include "qubie_defaults.h"
#include "qubie.acsl"
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
static pcap_t *handle = NULL;
static const byte *current_packet;
static unsigned int wifi_channel_index = WIFI_CHANNEL_DEFAULT;

/*@
 	 global invariant the_logical_and_real_wifi_monitor_states:
 	 	 	 	(the_logical_wifi_monitor_state == MONITOR_START <==> !the_qubie.wifi_monitor.monitor_running && !the_qubie.wifi_monitor.monitor_booted) &&
 	 	 	 	(the_logical_wifi_monitor_state == MONITOR_BOOTED <==> !the_qubie.wifi_monitor.monitor_running && the_qubie.wifi_monitor.monitor_booted) &&
 	 	 	 	(the_logical_wifi_monitor_state == MONITOR_BOOTED <==> the_qubie.wifi_monitor.monitor_running);
 */

//constructor

// ====================================================================
// @bon PRIVATE
// ====================================================================

//queries


//commands

/*@ requires !\valid(handle);
   	ensures \valid(handle);
   	assigns handle;
 */
void __open_wifi_interface_from_file(char * filename){
	FILE * pcap_fp = fopen(PCAP_TEST_FILE, "r");
	char pcap_error_buffer[PCAP_ERRBUF_SIZE];
	handle = pcap_fopen_offline(pcap_fp, pcap_error_buffer);
};

/*@ requires !\valid(handle);
   	ensures \valid(handle);
   	assigns handle;
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

/*@ requires !\valid(handle);
   	ensures \valid(handle);
   	ensures monitor_mode_enabled;
   	assigns handle;
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

/*@ requires wifi_interface_polled;
   ensures \result <==> \valid(current_packet);
   assigns \nothing;
 */
bool __packet_ready() {
	return current_packet != NULL;
}

/*@ requires \valid(current_packet);
   	assigns \nothing;
 */
uint __rtap_length() {
	return (uint)current_packet[3]<<8|(uint)current_packet[2];
}

/*@ requires \valid(current_packet);
   	ensures \result == rtap_header_valid;
   	assigns \nothing;
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
   Return codes for pcap_read() are:
     -  0: timeout
     - -1: error
     - -2: loop was broken out of with pcap_breakloop()
     - >1: OK
   The first one ('0') conflicts with the return code of 0 from
   pcap_offline_read() meaning "end of file".
*/


/*@ requires the_logical_wifi_monitor_state == MONITOR_RUNNING;
   	ensures wifi_interface_polled;
   	assigns current_packet;
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
		//@assert(TEST_MODE);
		assert(TEST_MODE);
		//printf("DEBUG - no more packets in pcap test file.\n");
	}
	current_packet = packet;
	//printf("DEBUG - res: %d, current_packet: %d\n",res, (uint)current_packet);
};

/*@	requires rtap_header_valid;
   	ensures !wifi_interface_polled;
   	ensures \old(rtap_header_valid) ==> the_qubie.observations.size == \old(the_qubie.observations.size) +1;
   	assigns \nothing;
 */
void __process_packet() {
	const byte *packet = current_packet;
	mac_t *smac_ptr;
	uint rtap_len = __rtap_length();
	frequency_t the_frequency = (uint)packet[rtap_len - 7]<<8|(uint)packet[rtap_len - 8];
	rssi_t the_rssi = packet[rtap_len - 4];
	//design skip over the rtap header and the dmac field of the ethernet header to point to the smac field
	smac_ptr = (mac_t *)(packet + rtap_len + MAC_SIZE);
	report_detected_device(*smac_ptr, the_rssi, the_frequency);
}

/*@ requires the_logical_wifi_monitor_state == MONITOR_RUNNING;
 	//TODO change packet limit to time limit + limit on number of processed packets
   	ensures !wifi_interface_polled;
   	ensures \old(the_qubie.observations.size) <= the_qubie.observations.size <= \old(the_qubie.observations.size) + PACKET_COUNT_LIMIT;
   	assigns \nothing;
 */
void __poll_wifi_interface(){
	int collected_packets = 0;
	__get_packet();
	/*@
	  	loop assigns collected_packets;
	  	loop invariant 0<=collected_packets<PACKET_COUNT_LIMIT;
	  	loop invariant wifi_interface_polled;
	  	loop variant PACKET_COUNT_LIMIT-collected_packets;
	 */
	while (collected_packets < PACKET_COUNT_LIMIT && __packet_ready()) {
		//printf("DEBUG - getting packet\n");
		if (__packet_ready() && __good_packet()){
			//printf("DEBUG - processing packet\n");
			__process_packet();
		}
		if (collected_packets < PACKET_COUNT_LIMIT) {
			__get_packet();
		}
		collected_packets++;
	}
	//enforce !wifi_interface_polled even when max packets is reached
	current_packet = NULL;

}

// ====================================================================
// @bon QUERIES
// ====================================================================

/*@ ensures \result <==> (the_qubie.wifi_monitor.monitor_booted);
   	assigns \nothing;
 */
bool monitor_booted(){
	return the_qubie.wifi_monitor.monitor_booted;
};
/*@ ensures \result <==> (the_qubie.wifi_monitor.monitor_running);
   	assigns \nothing;
 */
bool monitor_running(){
	return the_qubie.wifi_monitor.monitor_running;
};
//@ assigns \nothing;
bool auto_hopping(){
	return the_qubie.wifi_monitor.auto_hopping;
};
//@ assigns \nothing;
keyed_hash_t *keyed_hash(){
	return &the_qubie.wifi_monitor.keyed_hash;
};
/*@ requires \valid(the_qubie.wifi_monitor.channels);
   	assigns \nothing;
 */
const frequency_t* channels(){
	return the_qubie.wifi_monitor.channels;
};
//@ assigns \nothing;
frequency_t frequency(){
	return the_qubie.wifi_monitor.frequency;
};
// moved to central location: qubie_t qubie();

// ====================================================================
// @bon COMMANDS
// ====================================================================

/*@ requires the_logical_wifi_monitor_state == MONITOR_START;
   ensures the_logical_wifi_monitor_state == MONITOR_BOOTED;
   ensures the_qubie.wifi_monitor.keyed_hash.set;
   ensures logical_logged(WIFI_MONITOR_STATE, "booted");
   ensures the_qubie.wifi_monitor.frequency == the_qubie.wifi_monitor.channels[wifi_channel_index];
   assigns the_qubie.wifi_monitor.monitor_booted, the_qubie.wifi_monitor.frequency;
 */
void boot_monitor(){
	qubie_key_t *the_key = create_random_key();
	set_key(the_key);
	free(the_key);
	the_qubie.wifi_monitor.frequency = the_qubie.wifi_monitor.channels[wifi_channel_index];
//	TODO boot actual wifi device
	__boot_wifi_interface();
	add_log_entry(WIFI_MONITOR_STATE, (void *)"booted");
	the_qubie.wifi_monitor.monitor_booted = true;
};

/*@ requires the_logical_wifi_monitor_state == MONITOR_BOOTED;
   	ensures the_logical_wifi_monitor_state == MONITOR_RUNNING;
   	ensures logical_logged(WIFI_MONITOR_STATE, "running");
   	assigns the_qubie.wifi_monitor.monitor_running;
 */
void start_monitor(){
//	TODO start actual wifi device
	add_log_entry(WIFI_MONITOR_STATE, (void *)"running");
	the_qubie.wifi_monitor.monitor_running = true;
};

//design there is no difference between booted and stopped because both can lead to running (but are not currently running)
/*@ requires the_logical_wifi_monitor_state == MONITOR_RUNNING;
   	ensures the_logical_wifi_monitor_state == MONITOR_START;
   	ensures !\valid(handle);
   	ensures logical_logged(WIFI_MONITOR_STATE, "stopped");
   assigns handle, the_qubie.wifi_monitor.monitor_running, the_qubie.wifi_monitor.monitor_booted;
 */
void stop_monitor(){
//	TODO stop actual wifi device
	pcap_close(handle);
	add_log_entry(WIFI_MONITOR_STATE, (void *)"stopped");
	the_qubie.wifi_monitor.monitor_running = false;
	the_qubie.wifi_monitor.monitor_booted = false;
};

/*@ ensures the_qubie.wifi_monitor.frequency==the_frequency;
   	ensures logical_logged(WIFI_MONITOR_FREQUENCY, (void *)the_frequency);
   	assigns the_qubie.wifi_monitor.frequency;
 */

void set_frequency( frequency_t the_frequency){
	the_qubie.wifi_monitor.frequency = the_frequency;
//	TODO set frequency of actual wifi device
	add_log_entry(WIFI_MONITOR_FREQUENCY, (void *)the_frequency);
};

/*@ ensures the_qubie.wifi_monitor.auto_hopping==the_truth_val;
   	ensures logical_logged(WIFI_MONITOR_AUTO_HOPPING, (void *)the_truth_val);
   	assigns the_qubie.wifi_monitor.auto_hopping;
 */
void set_auto_hopping( bool the_truth_val){
	the_qubie.wifi_monitor.auto_hopping = the_truth_val;
//	TODO set auto hopping state of actual wifi device
	add_log_entry(WIFI_MONITOR_AUTO_HOPPING, (void *)the_truth_val);

};

//design circularly increment the channel index and set "the_frequency" according to the relevant channel
/*@	requires 0 <= wifi_channel_index < NUM_WIFI_CHANNELS;
 	ensures 0 <= wifi_channel_index < NUM_WIFI_CHANNELS;
   	ensures the_qubie.wifi_monitor.frequency == the_qubie.wifi_monitor.channels[wifi_channel_index];
   	behavior auto_hopping_on:
   		assumes the_qubie.wifi_monitor.auto_hopping;
   	   	ensures wifi_channel_index != \old(wifi_channel_index);
   		assigns wifi_channel_index;
   	behavior auto_hopping_off:
   	   	assumes !the_qubie.wifi_monitor.auto_hopping;
   	   	ensures wifi_channel_index == \old(wifi_channel_index);
   		assigns	\nothing;
   	complete behaviors auto_hopping_on, auto_hopping_off;
   	disjoint behaviors auto_hopping_on, auto_hopping_off;
 */
void update_monitored_frequency(){
	if(auto_hopping()){
		wifi_channel_index = (wifi_channel_index + 1)% NUM_WIFI_CHANNELS;
		set_frequency(channels()[wifi_channel_index]);
	}

};

/*@ ensures the_qubie.observations.size == \old(the_qubie.observations.size) + 1;
   	ensures (the_last_contact_record.rssi == the_signal_strength) && (the_last_contact_record.frequency == the_frequency);
   	ensures logical_logged(QUBIE_DETECTED_DEVICE, (void *){the_mac_address, the_signal_strength});
   	//assigns the_qubie.observations, the_qubie.log;
   	assigns \nothing;
 */
void report_detected_device(
		mac_t the_mac_address,
		rssi_t the_signal_strength,
		frequency_t the_frequency
		){
	//printf("DEBUG - making device id\n");
	device_id_t the_device_id = make_device_id(the_mac_address);
	//printf("DEBUG - making contact record\n");
	contact_record_t *contact_record_ptr = make_contact_record(the_device_id, current_time(NULL), the_signal_strength, the_frequency);
	//printf("DEBUG - recording observation\n");
	record_observation(contact_record_ptr);
};

//design message is null terminated and the length is no more than MAX_MESSAGE_LEN - 100 (to leave room for additional text)
/*@	requires \exists int i; 0<=i < MAX_MESSAGE_LEN - 100 && message[i]==0;
   	ensures logical_logged(WIFI_MONITOR_UNSUPPORTED_PACKET, message);
   	assigns \nothing;
 */
void report_unsupported_packet(char * message){
	//design message length should be less than (MAX_MESSAGE_LEN - 100) to avoid being truncated
	add_log_entry(WIFI_MONITOR_UNSUPPORTED_PACKET, (void *)message);
};

/*@ requires the_logical_wifi_monitor_state == MONITOR_RUNNING;
   	ensures wifi_monitor_polled;
   assigns \nothing;
 */
void poll_wifi_monitor(){
	__poll_wifi_interface();
	if(auto_hopping()){
		update_monitored_frequency();
	}
};



