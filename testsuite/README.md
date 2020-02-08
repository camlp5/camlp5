
This directory contains a testsuite for camlp5.

1. OUnit-based unit-tests

2. A ruond-trip-based test that checks that Camlp5's various parsers
and printers are the identity function on as much source code as
possible.

EXAMPLES

tools/TEST-PASSES --tool1 cp --tool2 lexer-passthru camlp5.7.11
tools/TEST-PASSES --tool1 cp --tool2 lexer-pa-pr camlp5.7.11

tools/TEST-PASSES --packages-file ROUNDTRIP-PACKAGES --tool1 cp --tool2 lexer-passthru --continue-on-error camlp5.7.11
tools/TEST-PASSES --packages-file ROUNDTRIP-PACKAGES --tool1 cp --tool2 lexer-pa-pr --continue-on-error camlp5.7.11
tools/TEST-PASSES --packages-file ROUNDTRIP-PACKAGES --tool1 ifdef-eval --tool2 roundtrip-revised --continue-on-error camlp5.7.11