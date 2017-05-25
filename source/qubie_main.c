//implementation summary of qubie scenarios
#include "qubie_t.h"
#include "qubie.acsl"
#include "qubie_main.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include "wifi_stub.h"
#include <stdio.h>

//globals
extern qubie_t the_qubie;
extern bt_client_t the_bt_client;

//helper functions

/*	to init pseudo random test seeds.
  	does not effect hash key. NOT SECURE FOR HASH KEY SEEDS!!!
 */
/*@	requires !randoms_initiated;
   	ensures randoms_initiated;
   	assigns \nothing;
 */
void init_random_number_generator(){
	unsigned long seed;
#ifdef RANDOM_SEED
	seed = RANDOM_SEED;
#else
	seed = (unsigned long) current_time(NULL);
#endif
	printf("DEBUG - random seed is: %lu", seed);
	srand(seed);
};


//"Power On, Boot Qubie, Start Qubie, Power Off"
// @scenario
void SmokeTest(){
	power_on_boot_and_run();
	power_off();
};

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Device, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
void SimpleTest(){
	power_on_boot_and_run();
	create_and_subscribe_bt_client();
	report_detected_device((mac_t){255,1,2,3,4,0}, 201, 5720);
	bt_communicator_update_qubie_state(STOPPED);
	bt_communicator_update_qubie_state(POWERED_OFF);
};

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Devices, Change Frequency, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
// @scenario
void NormalTest(){
	init_random_number_generator();
	power_on_boot_and_run();
	create_and_subscribe_bt_client();
	run_loop();
	shut_down();
};

//TBD --include multiple subscribe/unsubscribe and multiple options of detecting devices on different frequencies
//TODO expand
// @scenario
void FullTest(){
	NormalTest();
};

void __PcapTest(){
	power_on_boot_and_run();
	create_and_subscribe_bt_client();
	pcap_test();
	bt_communicator_update_qubie_state(STOPPED);
	bt_communicator_update_qubie_state(POWERED_OFF);
};

//"Normal Test but with encrypted=false"
//design implemented by NormalTest and setting #define ENCRYPTED false
// @scenario
void UnencryptedTest(){
	//@ assert bottom: false;
};

int main(void){
	printf("hello qubie\n\r");
	//SmokeTest();
	//SimpleTest();
	NormalTest();
	//__PcapTest();
	return 0;
};
