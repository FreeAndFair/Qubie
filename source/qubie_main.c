//implementation summary of qubie scenarios
#include "qubie_t.h"
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
/* @TODO requires !randoms_initiated
 * @TODO ensures randoms_initiated
 * @design to init pseudo random test seeds.
 * @design does not effect hash key. NOT SECURE FOR HASH KEY SEEDS!!!
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



void SimpleTest(){
	power_on_boot_and_run();
	create_and_subscribe_bt_client();
	report_detected_device((mac_t){255,1,2,3,4,0}, 201, 5720);
	bt_communicator_update_qubie_state(STOPPED);
	bt_communicator_update_qubie_state(POWERED_OFF);
};

void NormalTest(){
	init_random_number_generator();
	power_on_boot_and_run();
	create_and_subscribe_bt_client();
	run_loop();
	bt_communicator_update_qubie_state(POWERED_OFF);
};


int main(void){
	printf("hello qubie\n\r");
	//qubie_t *my_qubie = make_qubie();
	//printf("my qubie is booting:%d, running:%d, stopped:%d\n", booting(my_qubie), running(my_qubie), stopped(my_qubie));
	//@TODO implement
	//printf("DEBUG - starting simple test\n");
	//SimpleTest();
	NormalTest();
	return 0;
};
