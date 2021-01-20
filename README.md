# intermittent_formalism
Formal verification of some of the results of 'Towards a Formal Foundation of Intermittent Computing' -- OOPSLA 2020

In particular, I verify that the undo-logging state restoration algorithm (DINO) does indeed guarantee correct execution of any intermittently executed program, where 'correct execution' is formalized in definition 1 of the paper. 

The files are as follows:

Important:

proofs.v: essential proofs and invariants culminating in the proof of correctness for an arbitrary intermittently executed program, provided that the DINO checkpointing scheme is followed. notably, my novel memory invariant (all_diff_in_fw) is defined and used here. for reference, my encodings of the memory invariants used in (the paper proofs as written during my employment) are included here also, even though they are not used in any of my proofs.

semantics.v: embedding of the DSL and various evaluation relations. my novel implementation of NV memory makes determining the domain of these finite maps (over an infinite type) decidable while also maintaining functional extensionality. much of the ssreflect employment is in this file.
programs.v: types defining continuous and intermittent program traces. 

algorithms.v: types defining the DINO algorithm and the checkpointed variables it collects


Less important:

proofs_w.v: proofs regarding a weaker version of the crucial memory invariant defined in proofs.v. most crucial of these proofs is war_works, which transitions from the DINO algorithm and associated invariants to my invariants designed for easy inductive reasoning about intermittent programs. after this transition is made, other facts about the WARok relation can be proved. the most crucial of these is same_comi, which shows that, if a checkpointed set w is deemed ok, and an intermittent program executes with arbitrary reboots while checkpointing w, a continuous program will be able to execute to the "same point" (where 'same' is formalized in more detail in the theorem statement).

proofs_d.v: lemmas proving correspondence between the DINO algorithm definition and the WARok data invariant. 

proofs_n.v: proof of functional extensionality of nonvolatile memory maps

proofs_0.v: helper lemmas referring to program traces and associated data invariants


Trivial:

lemmas_1.v

lemmas_0.v

