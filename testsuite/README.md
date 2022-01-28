
This directory contains a testsuite for camlp5.

1. OUnit-based unit-tests

2. A ruond-trip-based test that checks that Camlp5's various parsers
and printers are the identity function on as much source code as
possible.

EXAMPLES

== Revised Syntax

tools/TEST-PASSES --profile-file profiles/lexer-passthru.yaml --packages-file packages/camlp5.yaml run-full camlp5.7.11
tools/TEST-PASSES --profile-file profiles/lexer-pa-pr.yaml --packages-file packages/camlp5.yaml run-full camlp5.7.11
tools/TEST-PASSES --profile-file profiles/pa_r-pr_r.yaml --packages-file packages/camlp5.yaml run-full camlp5.7.11
tools/TEST-PASSES --profile-file profiles/pa_r-pr_r.yaml --packages-file packages/maquette.yaml run-full maquette


== Original syntax

tools/TEST-PASSES --profile-file profiles/lexer-pa-pr.yaml --packages-file packages/camlp5.yaml run-full camlp5.7.11-ORIGINAL
tools/TEST-PASSES --profile-file profiles/pa_o-pr_o.yaml --packages-file packages/camlp5.yaml run-full camlp5.7.11-ORIGINAL

tools/TEST-PASSES --profile-file profiles/pa_o-pr_o.opt.yaml --packages-file packages/ocaml.yaml run-full ocaml-4.10.0 --continue-on-error --quiet

tools/TEST-PASSES --profile-file profiles/pa_o-pr_o.opt.yaml --packages-file packages/maquette.yaml run-full maquette-original

== To override a file (for patching)

tools/TEST-PASSES --profile-file profiles/pa_o-pr_o.opt.yaml --packages-file packages/ocaml.yaml --tool ALL --package ocaml-4.10.0 override-file file-name-to-override
