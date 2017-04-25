//implementation summary of qubie scenarios
#include "qubie_t.h"
#include "qubie_main.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stdio.h>

//globals
extern qubie_t the_qubie;
extern bt_client_t the_bt_client;

void SimpleTest(){
	printf("DEBUG - starting power_on_boot_and_run\n");
	power_on_boot_and_run();
	bt_client_t *the_bt_client = make_bt_client(bt_communicator());
	subscribe(the_bt_client);
	mac_t mac = {255,1,2,3,4,0};
	printf("DEBUG - starting report_detected_device\n");
	report_detected_device(mac, 201, 5720);
	printf("DEBUG - stopping qubie\n");
	bt_communicator_update_qubie_state(STOPPED);
	printf("DEBUG - powering off qubie\n");
	bt_communicator_update_qubie_state(POWERED_OFF);
};


int main(void){
	printf("hello qubie\n\r");
	//qubie_t *my_qubie = make_qubie();
	//printf("my qubie is booting:%d, running:%d, stopped:%d\n", booting(my_qubie), running(my_qubie), stopped(my_qubie));
	//@TODO implement
	printf("DEBUG - starting simple test\n");
	SimpleTest();
	return 0;
};
