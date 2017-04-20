//implementation summary of qubie scenarios
#include "qubie_main.h"
#include "qubie.h"
#include <stdio.h>

int main(void){
	printf("hello qubie\n\r");
	qubie_t *my_qubie = make_qubie();
	printf("my qubie is booting:%d, running:%d, stopped:%d\n", booting(my_qubie), running(my_qubie), stopped(my_qubie));
	//@TODO implement
};
