//implementation summary of qubie scenarios

#include "qubie_t.h"

//"Power On, Boot Qubie, Start Qubie, Power Off"
// scenario
void SmokeTest();

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Device, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
// scenario
void SimpleTest();

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Devices, Change Frequency, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
// scenario
void NormalTest();

//TBD --include multiple subscribe/unsubscribe and multiple options of detecting devices on different frequencies
// scenario
void FullTest();

//"Normal Test but with encrypted=false"
// scenario
void UnencryptedTest();



