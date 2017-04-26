
#include "qubie_t.h"
#include "qubie_wifi_monitor.h"
#include "wifi_stub.h"

static unsigned int wifi_channel_index = WIFI_CHANNEL_DEFAULT;

//@TODO requires randoms_initiated
void report_random_device(){
	//@assert(TEST_MODE)
	assert(TEST_MODE);

	mac_t the_mac;
	rssi_t the_rssi = (rssi_t)(rand() % 256);
	frequency_t the_frequency = frequency();
	for(int i=0; i<MAC_SIZE; ++i){
		the_mac[i]=(unsigned char)(rand() % 256);
	}
	report_detected_device(the_mac, the_rssi, the_frequency);
};

void update_monitored_frequency(){
	if(auto_hopping()){
		//@design circularly increment the channel index and set "the_frequency" according to the relevant channel
		set_frequency(frequency_range()[++wifi_channel_index % NUM_WIFI_CHANNELS]);
	}

};
