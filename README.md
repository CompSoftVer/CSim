# README #
# David Sanan 2019 #


### What is this repository for? ###

* Quick summary
Models, tools, and proofs for the formal verification of: a partitioning/separation hypervisor abstract specification, XtratuM hypervisor for LEON3, SPARC V8 ISA semantic models.


### How do I get set up? ###

* Summary of set up
ROOTS file in the main contains the target session to be built in Isabelle/HOL:

Possible targets up to now:
CSimpl: a rely-guarantee verification framework for CSimpl, a rich expressive concurrent language in Isabelle/HOL. 
CSim: a rely-guarantee simulation framework for Rely-Guarantee property preservation between Isabelle/HOL specifications.
Arinc653-Multicore: MultiCore specification of ARINC-653
SPARCv8: SparcV8 Model and proof of information flow.
SPARCWM: A weak memory model for the SparcV8. It currently does not provide an execution semantics for code from the memory, but I am working on it.

Coming: VCG for CSimpl, and SparcV8

To build a target, from the root directory call:

isabelle build -d . -b TARGET 

To load a target in interactive mode, from the root directory call:

isabelle jedit -d . -l TARGET 

This can be useful for the inspection of the models.

* Dependencies

Many of the libraries depends on tools and libraries developed by Data61 that are included in the lib and tools directories. By buidling the Lib model

isabelle build -d . -b Lib

and loading it 

isabelle jedit -d . -l Lib

It will be possible to load any theory included in this project just dragging and drop it in the Isabelle/HOL GUI.
