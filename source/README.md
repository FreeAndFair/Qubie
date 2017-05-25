Compiling the source code
===

To compile the source code with the provided make file you will need to perform the following actions:

* install libsodium
* install libpcap
* create a folder named "include" inside the source directory
* run: make main

for example on linux ubuntu:

	```
       sudo apt-get update 
       sudo apt-get upgrade
       sudo apt-get install libsodium-dev
       sudo apt-get install libpcap-dev
       cd <qubie_repo_path>/source
       mkdir install
       make main
	```
	
* Instead of installing the libraries you may copy the source files into the install directory.

* The result of a successful make with be an executable named qubie_main 

Formal proof
===

To formally prove the code with frama-c you will need to perform the following actions:

* install frama-c 

note: You will need a release that supports -c11 e.g. silicon. 
In May 2017 the latest version available via apt-get was magnesium which does not support -c11 so I had to install via OPAM as recommended in the frama-c manual. 

* copy or link files from libsodium and libpcap packages to the include directory
frama-c compiles the source code with -nostdinc to use its own header files and so it will not locate pcap.h and sodium.h in the regular install directory

* modify frama-c header files as needed
for example I had to add a typedef for u_short to ~/.opam/system/share/frama-c/libc/sys/types.h for compatibility with libsodium.

* run: make wp
