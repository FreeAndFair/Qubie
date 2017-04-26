//implementation summary of qubie scenarios

#include "qubie_t.h"

//"Power On, Boot Qubie, Start Qubie, Power Off"
void SmokeTest();

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Device, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
void SimpleTest();

//"Power On, Boot Qubie, Start Qubie, Subscribe Bluetooth Client, Detect Devices, Change Frequency, Bluetooth Client Command to Stop, Bluetooth Client Command to Power Off, Power Off"
void NormalTest();

//TBD --include multiple subscribe/unsubscribe and multiple options of detecting devices on differnt frequencies
void FullTest();

//"Normal Test but with encrypted=false"
void UnencryptedTest();



