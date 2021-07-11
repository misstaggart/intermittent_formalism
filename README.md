This development proves results from *Towards a Formal Foundation of Intermittent Computing* -- OOPSLA 2020

In particular, I verify that the undo-logging state restoration algorithm (DINO) does indeed guarantee correct execution of any intermittently executed program, where 'correct execution' is formalized in definition 1 of the paper. 

The files are as follows:

- Important:

  * proofs.v: essential proofs and invariants culminating in the proof of correctness for an arbitrary intermittently executed program, provided that the DINO checkpointing scheme is followed.

  * semantics.v: embedding of the DSL and various evaluation relations. much of the ssreflect employment is in this file.

  * programs.v: types defining continuous and intermittent program traces. 

  * algorithms.v: types defining the DINO algorithm and the checkpointed variables it collects

- Less important:

  * proofs_w.v: smaller proofs regarding the WARok relation

  * proofs_d.v: lemmas proving correspondence between the DINO algorithm definition and the WARok relation

  * proofs_n.v: proof of functional extensionality of nonvolatile memory maps

  * proofs_0.v: helper lemmas referring to program traces and associated data invariants, the most notable being determinism of continuous execution

- Trivial:

  * lemmas_1.v

  * lemmas_0.v

