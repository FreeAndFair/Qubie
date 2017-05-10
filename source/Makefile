CC=gcc
CFLAGS=$(pkg-config --cflags libsodium)  -Wall 
LDFLAGS=$(pkg-config --libs libsodium) -lsodium -lpcap
SYSTEM = qubie
NFORMAL_BON_FILES = $(SYSTEM)-domain-model.bon
STATIC_MODEL_FILES = $(SYSTEM)_static_model.bon
DYNAMIC_MODEL_FILES = $(SYSTEM)_dynamic_model.bon
FORMAL_BON_FILES = $(SYSTEM)_formal.bon
SOURCE_FILES = qubie_bt_communicator.c qubie_bt_communicator.h qubie.c \
				qubie_defaults.h qubie.h qubie_keyed_hash.c qubie_keyed_hash.h \
				qubie_log.c qubie_log.h qubie_main.c qubie_main.h qubie_observations.c \
				qubie_observations.h qubie_t.h qubie_wifi_monitor.c qubie_wifi_monitor.h
STUB_FILES = qubie_bt_client.c qubie_bt_client.h wifi_stub.h wifi_stub.c
REQUIREMENTS = 
BON_FILES =  $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES) $(REQUIREMENTS)

.PHONY: all clean  \
	typecheck typecheck-consistency \
	typecheck-informal typecheck-formal \
	typecheck-static typecheck-dynamic

all: main typecheck typecheck-bonc 

main: $(SOURCE_FILES) $(STUB_FILES)
	$(CC) $(CFLAGS) -o $(SYSTEM)_main  $(SOURCE_FILES) $(STUB_FILES)  $(LDFLAGS) 

typecheck:
	frama-c -lib-entry -c11 -cpp-extra-args="$(CFLAGS) $(LDFLAGS)"  $(SOURCE_FILES) $(STUB_FILES) 

wp:
	frama-c -lib-entry -c11 -wp -wp-rte $(SOURCE_FILES) $(STUB_FILES)

wp-verbose-report:
	frama-c -lib-entry -c11 -wp-verbose 0 $(SOURCE_FILES) $(STUB_FILES) -then -report 

wp-all-provers:
	frama-c -lib-entry -c11 -wp -wp-rte -wp-prover cvc4,z3,yices,alt-ergo $(SOURCE_FILES) $(STUB_FILES)

aorai:
	frama-c -lib-entry -c11 software.c -aorai-automata ../specs/software.ya

metrics:
	frama-c -lib-entry -c11 -metrics $(SOURCE_FILES) $(STUB_FILES)

value:
	frama-c -c11 -val $(SOURCE_FILES) $(STUB_FILES)

gui:
	frama-c-gui -lib-entry -c11 $(SOURCE_FILES) $(STUB_FILES)

typecheck-bonc: typecheck-informal typecheck-formal \
	typecheck-static typecheck-dynamic typecheck-consistency

typecheck-consistency:
	bonc -cc -tc  $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES)

typecheck-informal:
	bonc -tc -i -ci  $(INFORMAL_BON_FILES)

typecheck-formal:
	bonc -tc -f -cf  $(FORMAL_BON_FILES)

typecheck-static:
	bonc -tc -i -ci  $(INFORMAL_BON_FILES) $(STATIC_MODEL_FILES)

typecheck-dynamic:
	bonc -tc -i -ci  $(INFORMAL_BON_FILES) $(DYNAMIC_MODEL_FILES)

clean:
	rm -f *.o


