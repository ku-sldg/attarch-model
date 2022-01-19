A model of an attestation architecture, expressed as a high-level state transition system. The transition system is then analyzed using computation tree logic (CTL).

# Structure

CTL is a submodule containing the CTL library. See [here](https://github.com/ku-sldg/CTL/) for more information.

Within the `src` directory:
- `Privilege.v` defines access controls.
- `Env.v` defines access-controlled heterogeneous environments.
- `AttarchTrans.v` defines the transition relation which models the attestation architecture.
- `AttarchProperties.v` is a collection of proven CTL properties proven over the attestation architecture model.

# Cloning

After cloning this repo, one needs to invoke `git submodule init`, followed by `git submodule update` in order to fetch to the CTL submodule.

# Building

One should be able to build by running `make`. If not, you may try regenerating the makefile with the command: `coq_makefile -f _CoqProject -o Makefile`.
