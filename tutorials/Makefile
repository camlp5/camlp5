
DIRS=streams streams-revised calc calc+ocamllex calc+functorial calc+pa_lexer protobuf2

all:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) all; cd ..; done

test: all
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) test; cd ..; done

clean:
	set -e; for i in $(DIRS); do cd $$i; $(MAKE) clean; cd ..; done

