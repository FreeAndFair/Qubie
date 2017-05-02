
#include "qubie_t.h"
#include "qubie_wifi_monitor.h"
#include "wifi_stub.h"
#include <stdio.h>
#include <pcap.h>

//globals
static unsigned int wifi_channel_index = WIFI_CHANNEL_DEFAULT;
static pcap_t *handle;			/* Session handle */


/*
This document is Copyright 2002 Tim Carstens. All rights reserved. Redistribution and use, with or without modification, are permitted provided that the following conditions are met:

Redistribution must retain the above copyright notice and this list of conditions.
The name of Tim Carstens may not be used to endorse or promote products derived from this document without specific prior written permission.
*/

/* Insert 'wh00t' for the BSD license here */

//@TODO remove -- only for test purposes
void __print_mac(char *title, const unsigned char *mac ){
	printf("DEBUG - %s: ", title);
	for (int i=0; i< MAC_SIZE; ++i){
		printf("%02X",mac[i]);
	}
	printf("\n");
};

int __pcap_test1(){
	//@assert(false)
	char *dev, errbuf[PCAP_ERRBUF_SIZE];

	dev = pcap_lookupdev(errbuf);
	if (dev == NULL) {
		fprintf(stderr, "Couldn't find default device: %s\n", errbuf);
		return(2);
	}
	printf("Device: %s\n", dev);

	//@defined moved to global
	//pcap_t *handle;

	handle = pcap_open_live(dev, BUFSIZ, 1, 1000, errbuf);
	if (handle == NULL) {
	 fprintf(stderr, "Couldn't open device %s: %s\n", dev, errbuf);
	 return(2);
	}
	//@TBD this may be too strict at limiting to only one type of eth packets
	if (pcap_datalink(handle) != DLT_EN10MB) {
		fprintf(stderr, "Device %s doesn't provide Ethernet headers - not supported\n", dev);
		return(2);
	}


	return(0);
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

//@requires pcap_open
int qubie_pcap_get_packet(){
	/* Grab a packet */
	struct pcap_pkthdr header;	/* The header that pcap gives us */
	const u_char *packet;		/* The actual packet */
	struct pcap_pkthdr *header_ptr;
	int res = pcap_next_ex(handle, &header_ptr, &packet);
	int dlt; //datalink type
	printf("DEBUG - pcap_next_ex result: %d\n",res);
	if (-1 == res ) {
		printf("pcap_next_ex error: %s\n",pcap_geterr(handle));
	}
	header = *header_ptr;
	//packet = pcap_next(handle, &header);
    if (0 == res) {
       printf("No packet found.\n");
       return 2;
   }
	/* Print its length */
	printf("Jacked a packet with length of [%d]\n", header.len);
	dlt = pcap_datalink(handle);
	printf("DEBUG - dlt: %X\n", dlt);
//	struct pcap_pkthdr {
//		struct timeval ts; /* time stamp */
//		bpf_u_int32 caplen; /* length of portion present */
//		bpf_u_int32 len; /* length this packet (off wire) */
//	};

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

	__print_mac("SMAC", ethernet->ether_shost);
	__print_mac("DMAC", ethernet->ether_dhost);

	//@TODO test in (wifi) monitor mode
	//@design using static "0" rssi (rssi only valid in (wifi) monitor mode)
	report_detected_device((unsigned char *)ethernet->ether_shost, 0, frequency());


	return(0);
};

/* @requrires pcap_open
 * @ensures pcap_closed
 */
void qubie_pcap_close(){
	pcap_close(handle);
};

//design for testing purposes determine which test function to run
int pcap_test(){
	int Result;
	Result = qubie_pcap_init();
	if(!Result) {
		Result = qubie_pcap_get_packet();
		qubie_pcap_close();
	}
	return(Result);
};



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



