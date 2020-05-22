all:
	sphinx-build . _build

fromhtml:
	cd ../htmlp && find . -name '*.html' -exec sh -c 'for f; do pandoc -f html -t rst "$f" -o "../rst/${f%.html}.rst"; done' sh {} +
