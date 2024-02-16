.PHONY: all debs watch
BUILD_DIR=_build

all:
	sphinx-build . $(BUILD_DIR)

watch:
	sphinx-autobuild . $(BUILD_DIR) -p 8005

debs:
	sudo apt-get install python3-sphinx-rtd-theme python3-sphinx-autobuild

fromhtml:
	cd ../htmlp && find . -name '*.html' -exec sh -c 'for f; do pandoc -f html -t rst "$f" -o "../rst/${f%.html}.rst"; done' sh {} +
