


#ifndef QUBIE_DEFAULTS
#define QUBIE_DEFAULTS

#define TEST_MODE true

//change to false for unencrypted test mode
#define ENCRYPTED_DEFAULT true //true

//default value for wifi monitor auto hopping state
#define WIFI_AUTO_HOPPING_DEFAULT true

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
};
//default value for starting wifi frequency (MHz)
#define NUM_WIFI_CHANNELS 68
#define WIFI_FREQUENCY_DEFAULT 2412

//the maximum length of a log message (including null terminator)
#define MAX_MESSAGE_LEN 512

#endif
