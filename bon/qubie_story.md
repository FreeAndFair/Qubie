Qubie is powered on at the polling place. Qubie sets up new, empty log file and optionally an observations file. Qubie enables a bluetooth communicator to be connected to a single bluetooth client. Qubie automatically begins the booting. 
Qubie instructs the wifi monitor to boot up. The wifi monitor generates a random key and initializes a keyed hash. the wifi monitor sets its first frequency. 
Once booted, Qubie automatically begins running. 
While running, Qubie's bluetooth communicator is periodically polled for updated status and commands regarding subscribed bluetooth clients. 
While running, the wifi monitor begins searching for wifi devices. For each device that is found it creates a report that includes an identifier, rssi, the time and the frequency each identifier is encrypted by the keyed hash before it is recorded. 
While Running, the wifi monitor checks if auto hopping is enabled and if so, hops to the next frequency after a delay. 
Each detected device, change of frequency, or change of qubie state is logged in the log.
When Qubie receives a command to stop or power down (either from the bluetooth client or a low battery signal) it tells the wifi monitor to stop. The wifi monitor stops. The log is updated with the stop command. The Qubie is powered down. Before powering down for any reason (including low battery) the qubie saves and closes the log in a way that ensures it will be accessible later.

--TODO: 
	--need to define a secure way for qubie to connect to a bluetooth client
	--led or screen indications of status: power(red led), running (green constant led), detecting devices (green blinking led)
	--create a button to stop and/or power down the qubie
	--mode to retreive data from qubie without running
	--option to save data from previous runs.
