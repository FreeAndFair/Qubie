


#ifndef QUBIE_DEFAULTS
#define QUBIE_DEFAULTS


// ====================================================================
// TEST RELATED DEFAULTS
// ====================================================================

#define TEST_MODE true
//change to false for unencrypted test mode
#define ENCRYPTED_DEFAULT true //true
//default value for wifi monitor auto hopping state
#define WIFI_AUTO_HOPPING_DEFAULT true

//@design unremark in order to test with a specific seed
//#define RANDOM_SEED 1

//@design all times listed in seconds but actual tests will be sped up 1000x
//to avoid infinite loop set max number of run loop iterations before shutting down.
//@design only relevant in test mode
#define MAX_TEST_ITERATIONS 54000 //15 hours
//@design the amount of time to wait in each wifi sniffing interval
#define WIFI_PAUSE_TIME 5 //5 seconds

//@TODO model voter related intervals according to poisson distribution

//@design average interval between voters arriving
//for exponential distribution of intervals
//which results in poisson distribution of voters
#define VOTER_ARRIVAL_INTERVAL (10*60) //10 minutes



// ====================================================================

#define WIFI_TIMEOUT 5000 //5 seconds

//@design a string to define a filter for the wifi device
//unremark to activate the filter
//#define WIFI_FILTER_STR ""

/* channels 12 and 13 are not really in use in the us but they are added because they are used in other countries
 * and also in specific cases inside the usa. channel 14 (2484MHz) is omitted because it is not in use by cell phones
 * @TODO verify the channels are correct (current source is wikipedia)
 */
#define FREQUENCY_WIFI_CHANNELS {	\
		2412, 2417, 2422, 2427, 2432, 2437, 2442, 2447, 2452, 2457,	\
		2462, 2467, 2472,	\
		5170, 5180, 5190, 5200, 5210, 5220, 5230, 5240, 5250, 5260,	\
		5270, 5280, 5290, 5300, 5310, 5320,	\
		5500, 5510, 5520, 5530, 5540, 5550, 5560, 5570, 5580, 5590,	\
		5600, 5610, 5620, 5630, 5640,	\
		5660, 5670, 5680, 5690, 5700,	\
		5710, 5720,	\
		5745, 5750, 5755, 5760, 5765, 5770, 5775, 5780, 5785, 5790,	\
		5795, 5800, 5805, 5810, 5815, 5820, 5825	\
}
//default value for starting wifi frequency (MHz)
#define NUM_WIFI_CHANNELS 68
//@TODO verify WIFI_CHANNEL_DEFAULT < NUM_WIFI_CHANNELS
#define WIFI_CHANNEL_DEFAULT 0

//the maximum length of a log message (including null terminator)
#define MAX_MESSAGE_LEN 512

#endif
