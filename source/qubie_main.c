//implementation summary of qubie scenarios
#include "qubie_t.h"
#include "qubie_main.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_bt_communicator.h"
#include "qubie_bt_client.h"
#include <stdio.h>

void SimpleTest(qubie_t *self){
	printf("DEBUG - starting power_on_boot_and_run\n");
	power_on_boot_and_run(self);
	bt_client_t *the_client = make_bt_client(self->bt_communicator);
	subscribe(self->bt_communicator, the_client);
	mac_t mac = {255,1,2,3,4,0};
	printf("DEBUG - starting report_detected_device\n");
	report_detected_device(self->wifi_monitor, &mac, 201, 5720);
	printf("DEBUG - stopping qubie\n");
	bt_communicator_update_qubie_state(self->bt_communicator,STOPPED);
	printf("DEBUG - powering off qubie\n");
	bt_communicator_update_qubie_state(self->bt_communicator,POWERED_OFF);
};


int main(void){
	printf("hello qubie\n\r");
	qubie_t *my_qubie = make_qubie();
	//printf("my qubie is booting:%d, running:%d, stopped:%d\n", booting(my_qubie), running(my_qubie), stopped(my_qubie));
	//@TODO implement
	printf("DEBUG - starting simple test\n");
	SimpleTest(my_qubie);
	return 0;
};
