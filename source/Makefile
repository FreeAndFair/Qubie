CC=gcc
CFLAGS=$(pkg-config --cflags libsodium)  -Wall 
LDFLAGS=$(pkg-config --libs libsodium) -lsodium
SYSTEM = qubie
NFORMAL_BON_FILES = $(SYSTEM)-domain-model.bon
STATIC_MODEL_FILES = $(SYSTEM)_static_model.bon
DYNAMIC_MODEL_FILES = $(SYSTEM)_dynamic_model.bon
FORMAL_BON_FILES = $(SYSTEM)_formal.bon
SOURCE_FILES = qubie_bt_communicator.c qubie_bt_communicator.h qubie.c \
				qubie_defaults.h qubie.h qubie_keyed_hash.c qubie_keyed_hash.h \
				qubie_log.c qubie_log.h qubie_main.c qubie_main.h qubie_observations.c \
				qubie_observations.h qubie_t.h qubie_wifi_monitor.c qubie_wifi_monitor.h
STUB_FILES = qubie_bt_client.c qubie_bt_client.h
REQUIREMENTS = 
BON_FILES =  $(INFORMAL_BON_FILES) $(FORMAL_BON_FILES) $(REQUIREMENTS)

.PHONY: all clean  \
	typecheck typecheck-consistency \
	typecheck-informal typecheck-formal \
	typecheck-static typecheck-dynamic

all: main typecheck $(SYSTEM)-iig.dot index.txt index.html html/index.html
	
main: $(SOURCE_FILES) $(STUB_FILES)
	$(CC) $(CFLAGS) -o $(SYSTEM)_main  $(SOURCE_FILES) $(STUB_FILES)  $(LDFLAGS) 
	 

typecheck: typecheck-informal typecheck-formal \
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

$(SYSTEM)-icg.dot: $(BON_FILES)
	bonc -g ICG $(BON_FILES) > $(SYSTEM)-icg.dot

$(SYSTEM)-iig.dot: $(BON_FILES)
	bonc -p IIG -po $(SYSTEM)-iig.dot $(BON_FILES)

index.txt: $(BON_FILES)
	bonc -po index.txt -p TXT $(BON_FILES)

index.html: $(BON_FILES)
	bonc -po index.html -p HTML $(BON_FILES)

html/index.html: $(BON_FILES)
	mkdir -p html
	bonc -p NEWHTML -po html $(BON_FILES)
