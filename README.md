# README #


### What is this repository for? ###

* Quick summary
Models, tools, and proofs for CSim^2 a compositional verification framework.


### How do I get set up? ###

* Summary of set up
ROOTS file in the main contains the target session to be built in Isabelle/HOL:

Possible targets up to now:
CSimpl: a Rely-Guarantee verification framework for CSimpl, a rich expressive concurrent language in Isabelle/HOL. The proof system and its soundness is proven in the file LocalRG_HoaredDef.thy. The CSimpl language is defined in LanguageCon.thy and its small step semantics in file SmallStepCon.thy. VcgCon.thy and XVcgCon.thy provides the concrete syntax. 

CSim: a Rely-Guarantee simulation framework for Rely-Guarantee property preservation between Isabelle/HOL specifications. 
  CRef.thy defines the Rely-Guarantee preservation framework and the definition of the rely-guarantee simulation. 
  CSim.thy provides the rely-guarantee based simulation reasoning system. 

ARincRef: A case study for the preservation using CSim^2 of a complex invariant between a specification and lower abstraction model. 
          ARincRef/ArincMulticoreState.thy contains state definitions and related lemmas
          Communication/Spec/ArincQueuing.thy defines the rely guarantee relations and invariant
          Communication/Spec/ArincSpec_com_queue_insert.thy models the insert service and proves correctness of the invariant on the service model
          Communication/Spec/ArincSpecQueue.thy models the Gamma function and proves the invariant on the parallel system.
          Communication/Impl/ArincImp.thy defines the lower abstraction level and proves stability related lemmas
          Refinement/ArincRefinement.thy defines the simulation relation between the two specification levels and proofs the Invariant over the lower abstraction level.


To build a target, from the root directory call:

isabelle build -d . -b TARGET 

To load a target in interactive mode, from the root directory call:

isabelle jedit -d . -l TARGET 

This can be useful for the inspection of the models.


