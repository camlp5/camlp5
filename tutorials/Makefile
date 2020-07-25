
DIRS=streams-original streams calc calc+ocamllex calc+functorial \
	calc+pa_lexer calc+pa_lexer-original protobuf2

all:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) all; cd ..; done

test: all
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) test; cd ..; done

clean:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) clean; cd ..; done

