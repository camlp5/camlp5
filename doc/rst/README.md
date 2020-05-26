to convert HTML files to RST do install `pandoc` and

    cd ../htmlp && find . -name '*.html' -exec sh -c 'for f; do pandoc -f html -t rst "" -o "../rst/.rst"; done' sh {} +

