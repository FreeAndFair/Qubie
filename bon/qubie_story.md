Qubie is powered on at the polling place. Qubie sets up a new, empty log file. Qubie enables a bluetooth communicator to connect to a bluetooth client if one exists. If no client is found immediately the communicator will allow a client to be connected later (either by being visible to bluetooth devices or by periodically searching). Once a bluetooth client found it will stop looking as long as the client is connected. 

Qubie instructs the wifi monitor to boot up. If The wifi monitor fails to boot correctly Qubie must log the error and stop, perhaps after attempting to try again and/or troubleshoot. The wifi monitor generates a random key and initializes a keyed hash. the wifi monitor sets its first frequency. The wifi monitor begins searching for wifi devices. for each device that is found it creates a report that includes an identifier, rssi, the time and thre frequency. The wifi monitor checks if auto hopping is enabled and if so, hops to the next frequency after a delay. The wifi monitor continues to search for devices this way until it is told to stop or until it is powered down. each change of frequency and each change of auto hopping state is logged. each contact report is loged in the log.

If Qubie receives a command to stop (from the bluetooth client) it tells the wifi monitor to stop. The wifi monitor stops. The log is updated with the stop command. The Qubie is powered down. Before powering down for any reason (including low battery) the qubie saves and closes the log in a way that ensures it will be accessible later.

--TODO: 
	--can we allow BTLE device to connect as a BT client? perhaps we need a password
	--allow non-encrypted test mode
	--led or screan indications of status: power(red led), running (green constant led), detecting devices (green blinking led)
	--how do we configure the qubie: time, frequencis, delays, test/encrypted mode
	--create a button to stop and/or power down the qubie
