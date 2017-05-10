
#include "qubie_t.h"
#include "qubie.h"
#include "qubie_wifi_monitor.h"
#include "qubie_bt_client.h"
#include "wifi_stub.h"
#include <stdio.h>
#include <pcap.h>

//globals

static pcap_t *handle;			/* Session handle */


/*
This document is Copyright 2002 Tim Carstens. All rights reserved. Redistribution and use, with or without modification, are permitted provided that the following conditions are met:

Redistribution must retain the above copyright notice and this list of conditions.
The name of Tim Carstens may not be used to endorse or promote products derived from this document without specific prior written permission.
*/

/* Insert 'wh00t' for the BSD license here */

//@TODO remove -- only for test purposes
void __print_byte_array(char *title, const unsigned char *arr, const uint size ){
	printf("DEBUG - %s: ", title);
	for (int i=0; i< size; ++i){
		printf("%02X",arr[i]);
	}
	printf("\n");
};


/* @requires pcap_closed
 * @ensures pcap_open
 */
int qubie_pcap_init(){
	char *dev;			/* The device to sniff on */
	char errbuf[PCAP_ERRBUF_SIZE];	/* Error string */
	bpf_u_int32 mask;		/* Our netmask */
	bpf_u_int32 net;		/* Our IP */

	/* Define the device */
	dev = pcap_lookupdev(errbuf);
	if (dev == NULL) {
		fprintf(stderr, "Couldn't find default device: %s\n", errbuf);
		return(2);
	}
	/* Find the properties for the device */
	if (pcap_lookupnet(dev, &net, &mask, errbuf) == -1) {
		fprintf(stderr, "Couldn't get netmask for device %s: %s\n", dev, errbuf);
		net = 0;
		mask = 0;
	}
	/* Open the session */
	handle = pcap_open_live(dev, BUFSIZ, 1, WIFI_TIMEOUT, errbuf);
	if (handle == NULL) {
		fprintf(stderr, "Couldn't open device %s: %s\n", dev, errbuf);
		return(2);
	}

	//enable monitor mode
	pcap_set_rfmon(handle, 1);
	/* Compile and apply the filter */
#ifdef WIFI_FILTER_STR
	struct bpf_program fp;		/* The compiled filter */
	char filter_exp[] = "port 23";	/* The filter expression */

	if (pcap_compile(handle, &fp, filter_exp, 0, net) == -1) {
		fprintf(stderr, "Couldn't parse filter %s: %s\n", filter_exp, pcap_geterr(handle));
		return(2);
	}
	if (pcap_setfilter(handle, &fp) == -1) {
		fprintf(stderr, "Couldn't install filter %s: %s\n", filter_exp, pcap_geterr(handle));
		return(2);
	}

#endif
	return(0);
};

int qubie_pcap_init_from_file(){
	FILE * pcap_fp = fopen(PCAP_TEST_FILE, "r");
	char errbuf[PCAP_ERRBUF_SIZE];	/* Error string */
	handle = pcap_fopen_offline(pcap_fp, errbuf);

	//enable monitor mode
	pcap_set_rfmon(handle, 1);

	return(0);
};


//@requires pcap_open
int qubie_pcap_get_packet(){
	/* Grab a packet */
	struct pcap_pkthdr header;	/* The header that pcap gives us */
	const u_char *packet;		/* The actual packet */
	struct pcap_pkthdr *header_ptr;
	int res = pcap_next_ex(handle, &header_ptr, &packet);
	int dlt; //datalink type
	unsigned int rtap_len;
	frequency_t the_frequency;
	byte the_rssi;
	printf("DEBUG - pcap_next_ex result: %d\n",res);
	if (-1 == res ) {
		printf("pcap_next_ex error: %s\n",pcap_geterr(handle));
	}
	header = *header_ptr;
	//packet = pcap_next(handle, &header);
    if (0 == res) {
       printf("No packet found.\n");
       return(2);
   }
	/* Print its length */
	printf("Jacked a packet with length of [%d]\n", header.len);
	dlt = pcap_datalink(handle);
	if (dlt != 127) {	//rtap header
		int msg_size = 100;
		char msg[msg_size];
		snprintf(msg, msg_size, "dlt = %d", dlt);
		report_unsupported_packet((void *)msg);
		return(2);
	}
	printf("DEBUG - dlt: %X\n", dlt);
//	struct pcap_pkthdr {
//		struct timeval ts; /* time stamp */
//		bpf_u_int32 caplen; /* length of portion present */
//		bpf_u_int32 len; /* length this packet (off wire) */
//	};

	//@TODO verify we need little endian
	rtap_len = (uint)packet[3]<<8|(uint)packet[2];
	printf("DEBUG - rtap length: %d\n", rtap_len);
	__print_byte_array("rtap header", packet, rtap_len);
	if (rtap_len < MIN_RTAP_LEN) {
		report_unsupported_packet((void *)"bad radiotap header length");
		return(2);
	}
	//@design two bytes to represent the channel frequency (disregard flag data)
	the_frequency = (uint)packet[rtap_len - 7]<<8|(uint)packet[rtap_len - 8];
	the_rssi = packet[rtap_len - 4];

	//move pointer to the beginning of the eth packet
	packet = packet + rtap_len;

	/* Ethernet addresses are 6 bytes */
	#define ETHER_ADDR_LEN	6

	/* Ethernet header */
	struct sniff_ethernet {
		u_char ether_dhost[ETHER_ADDR_LEN]; /* Destination host address */
		u_char ether_shost[ETHER_ADDR_LEN]; /* Source host address */
		u_short ether_type; /* IP? ARP? RARP? etc */
	};
	printf("DEBUG - packet ptr: %u\n",(unsigned int) packet);

	const struct sniff_ethernet *ethernet; /* The ethernet header */
	ethernet = (struct sniff_ethernet*)(packet);

	__print_byte_array("SMAC", ethernet->ether_shost, MAC_SIZE);
	__print_byte_array("DMAC", ethernet->ether_dhost, MAC_SIZE);

	//@TODO test in (wifi) monitor mode
	//@design using static "0" rssi (rssi only valid in (wifi) monitor mode)
	//report_detected_device((unsigned char *)ethernet->ether_shost, 0, frequency());
	report_detected_device((unsigned char *)ethernet->ether_shost, the_rssi, the_frequency);


	return(0);
};

/* @requrires pcap_open
 * @ensures pcap_closed
 */
void qubie_pcap_close(){
	pcap_close(handle);
};


/* @requires running()
 * @TODO ensures wifi_monitor and bt_client are polled
 * @ensures state > running;
 */
void __pcap_run_loop(){
	unsigned long iterations = 0;
	int pcap_ret = 0;
	while (running() && !pcap_ret && iterations < MAX_TEST_ITERATIONS){
		printf("DEBUG - iteration: %lu\n",iterations);
		pcap_ret = qubie_pcap_get_packet();
		poll_bt_client();
		iterations++;
	}
};



//design for testing purposes determine which test function to run
void pcap_test(){
	int Result;
	//Result = qubie_pcap_init();
	Result = qubie_pcap_init_from_file();
	if(!Result) {
		//Result = qubie_pcap_get_packet();
		__pcap_run_loop();
		qubie_pcap_close();
	}
};

//@ design create a device with random data and record it in observations and lng
/*@	requires randoms_initiated;
 * 	requires TEST_MODE;
 * 	ensures the_qubie.observations.size == \old(the_qubie.observations.size) + 1;
 * 	assigns observations_array, the_qubie.observations, the_qubie.log;
 */
void report_random_device(){
	assert(TEST_MODE);

	mac_t the_mac;
	rssi_t the_rssi = (rssi_t)(rand() % 256);
	frequency_t the_frequency = frequency();
	for(int i=0; i<MAC_SIZE; ++i){
		the_mac[i]=(unsigned char)(rand() % 256);
	}
	report_detected_device(the_mac, the_rssi, the_frequency);
};





