Qubie Installation
===

To install Qubie from scratch on a Raspberry Pi, do the following:

* Install Raspbian (either from NOOBS or directly), 32GB SD card recommended
* Update/upgrade the package repository, OS and kernel: 

       sudo apt-get update 
       sudo apt-get upgrade
       sudo rpi-update
	
* Reboot if necessary and install required packages, including removing the default, obsolete Node.js installation:

	   sudo apt-get install python-pcapy python-netifaces
	   
	   # if using Bluetooth Low Energy for status indications, also run the commands below
	   sudo apt-get remove nodered nodejs nodejs-legacy
	   curl -sL https://deb.nodesource.com/setup_0.12 | bash -
	   sudo apt-get install bc nodejs bluetooth bluez libbluetooth-dev libudev-dev
	   sudo npm install bleno

* Create any accounts you like on the Raspberry Pi, and change passwords for security; decide where you intend to store the Qubie sources and other required sources. Note that as of now, Qubie must be run as root.

* Check out the Qubie repository somewhere; the result will become your Qubie directory for later use:

       git clone <url goes here>

* If using the recommended WiFi dongle (D-Link DWA-171), build its drivers (if using a different WiFi dongle or built-in WiFi, be sure that it supports monitor mode): 
  * First, install the current Raspbian kernel headers:

	     # Get rpi-source and make it executable
	     sudo wget https://raw.githubusercontent.com/notro/rpi-source/master/rpi-source -O /usr/local/bin/rpi-source
	     sudo chmod +x /usr/local/bin/rpi-source

	     # Tell the update mechanism that this is the latest version of the script, and get the kernel headers
	     sudo rpi-source -q --tag-update
	     sudo rpi-source
	     sudo chmod og+rx /root
	     
  * Next, get, patch and install the D-Link DWA-171 drivers:
         
         git clone -b 4.3.22_beta --single-branch https://github.com/Grawp/rtl8812au_rtl8821au 
         cd rtl8812au_rtl8821au
         patch < (qubie-directory)/prototype/rtl8812au_rtl8821au.patch
         make
         sudo make install
         
  * Reboot, or manually load the new kernel module with `insmod 8812au.ko`

* If using Bluetooth Low Energy for status indications, disable the Bluetooth daemon on the Raspberry Pi:

        sudo service bluetooth stop
        sudo update-rc.d bluetooth remove
        
* Clean up installed packages (some will have been obsoleted):
        
      sudo apt-get autoremove

* Modify the Qubie init script `qubie.init` with your desired configuration and Qubie directory, and install it so Qubie runs on boot:

      cd (qubie-directory)
      cp qubie.init qubie
      (edit qubie with your editor of choice)
      sudo cp qubie.init /etc/init.d/qubie
      sudo update-rc.d qubie add
      
* Reboot your Raspberry Pi. Qubie should start on boot and log information (depending on how you've modified the init script) to the `log` and `data` directories in your Qubie directory.
      