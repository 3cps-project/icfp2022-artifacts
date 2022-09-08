
Paper name: Analyzing Binding Extent in 3CPS

This artifact contains a Coq proof of correctness of simulation, i.e. the abstract semantics is a sound approximation of the concrete/collecting semantics. These semantics are in Sections 5 and 6 of the paper.

We rely on the coqutil library (https://github.com/mit-plv/coqutil)
This code should be added in this directory in the folder coqutil/
We compiled using commit 6a5a8ec5dfd0a41bec327e981fa790eb92f04ba4.

We compiled with Coq version `8.13.2` and OCaml `4.12.0`.

See the below instructions for how to build the proofs, assuming the current directory is at the top level of the proofs folder.

Ensure Coq is on the machine.
```
sudo apt-get install gcc make g++ opam libgmp3-dev
opam init
eval $(opam env)        
opam pin add ocaml 4.12.0
opam pin add coq 8.13.2
```
Build the proofs.
```
git clone https://github.com/mit-plv/coqutil
(cd coqutil; git checkout 6a5a8ec5dfd0a41bec327e981fa790eb92f04ba4; make)
coq_makefile -f _CoqProject -o Makefile
make
```


The files in src/common/ are utility definitions and tactics and are not directly related to the proof.
The file src/common/CPS.v contains the definition of the CPS datatypes.
The file src/common/SemanticsCommon.v contains definitions common to both the concrete and abstract semantics.
The file src/common/ConcreteSemantics.v contains all the definitions for the concrete semantics, including the concrete transition relation.
The file src/common/AbstractSemantics.v contains all the definitions for the abstract semantics, including the abstract transition relation.
The file src/common/SimulationRelation.v contains the definitions associated with relating the concrete states with abstract states.
The file src/common/Lemmas.v contains lemmas used to prove the simulation result.
The file src/common/Simulation.v contains the actual simulation result:
- the initial states of the semantics are related, and
- simulation can preserved via state transition.
