A model of an attestation architecture, expressed as a high-level state transition system. The transition system is then analyzed using computation tree logic (CTL).

# Cloning

After cloning this repo, one needs to invoke `git submodule init`, followed by `git submodule update` in order to fetch to the CTL submodule.

# Building

One should be able to build by running `make`. If not, you may try regenerating the makefile with the command: `coq_makefile -f _CoqProject -o Makefile`.
