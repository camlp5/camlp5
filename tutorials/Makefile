
DIRS=streams calc calc+ocamllex calc+functorial calc+pa_lexer protobuf2

all:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) clean all; cd ..; done

clean:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) clean; cd ..; done

