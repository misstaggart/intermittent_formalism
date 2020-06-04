Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Semantics Require Import algorithms.

Open Scope list_scope.
(************* program traces*****************)

(*trace helpers*)
(*first three get on my nerves; coq insists that whenever I want to access elements of the_write_stuff
I need to pass in all elements as separate arguments

 Without these helpers in CTrace_App,
when I try to use the CTrace_App constructor inside another function,
it'll complain that I'm passing in a trace defined with
 the_write_stuff when I should actually be passing in
a trace defined with a triple...
 *)
Definition getwt (W: the_write_stuff) := match W with (out, _, _ )=> out end.

Definition getrd (W: the_write_stuff) := match W with (_, out , _ )=> out end.

Definition getfstwt (W: the_write_stuff) := match W with (_, _, out )=> out end.


(*Notes:*)
(*do I keep track of volatile writes as well...I don't think so
 cuz the writes don't last and they all have to be checkpointed anyways*)
(*concern:*)
(*actually there's no reason for us to be checkpointing volatiles that are
 written to before they're ever read from along any path*)
(*at first inspection it doesn't seem like it would be all that hard to keep track of this
 since we're already doing MFstWt for novolatiles.*)

(*concern: cconf and context are functionally the same but cconf has an annoying constructor
 which can't be coerced bc context exists, consider combining into one type?*)

(*The trace type contains
1. starting configuration
2. execution observations
3. ending configuration
3. a list of warvars which have been written to
4. a list of warvars which have been read from
5. a list of warvars which have been written to before they have been read from
 *)
(*Ordering: start -> observations -> end -> the_write_stuff*)
(*steps to termination, accumulates write data*)

(*continuous traces*)
Inductive trace_c: context -> context -> obseq -> the_write_stuff -> Prop :=
  CTrace_Empty: forall(C: context),
                 trace_c C C nil (nil, nil, nil)
  | CTrace_Single: forall {C1 C2: context} {O: obseq} {W: the_write_stuff},
                  single_com C1 -> (*checks program cannot be stepped more than once*)
                  cceval_w C1 O C2 W -> (*command in C2 is skip by def single_com, cceval_w*)
                  trace_c C1 C2 O W
| CTrace_App: forall{C1 C2 Cmid: context} {O1 O2: obseq}
               {W1 W2: the_write_stuff},
    (*not (single_com C1) -> unclear if this is necessary as implied by
     the fact that c1 can be stepped at least twice...
     will try and prove without it and if it gets messy I'll add it*)
    trace_c C1 Cmid O1 W1 -> (*steps first section*)
    trace_c Cmid C2 O2 W2 -> (*steps rest of program*)
    trace_c C1 C2 (O1 ++ O2) ((getwt W1) ++ (getwt W2), (getrd W1) ++ (getrd W2), (getfstwt W1) ++
                                                                                                (remove in_loc_b (getrd W1)
                                                                                                        (getfstwt W2))).
 (*App makes for easy subtraces by allowing command in C2 not to be skip*)

(*intermittent traces*)
 (*the same as trace_c bar types as differences between
  intermittent and continuous execution have been implemented in evals*)
Inductive trace_i : iconf -> iconf -> obseq -> the_write_stuff -> Prop :=
iTrace_Empty: forall{C: iconf},
                 trace_i C C nil (nil, nil, nil)
|iTrace_Single: forall{C1 C2: iconf} {O: obseq} {W: the_write_stuff},
                  single_com_i C1 -> (*checks program cannot be stepped more than once*)
                  iceval_w C1 O C2 W -> (*command in C2 is skip by def single_com, iceval_w*)
                  trace_i C1 C2 O W
| iTrace_App: forall{C1 C2 Cmid: iconf} {O1 O2: obseq}
         {W1 W2: the_write_stuff},
    trace_i C1 Cmid O1 W1 -> (*steps first section*)
    trace_i Cmid C2 O2 W2 -> (*steps rest of program*)
    trace_i C1 C2 (O1 ++ O2) ((getwt W1) ++ (getwt W2), (getrd W1) ++ (getrd W2), (getfstwt W1) ++
                                                                                                (remove in_loc_b (getrd W1)
                                                                                                        (getfstwt W2))).

(*more trace helpers*)


Definition Wt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) := getwt W.

Definition FstWt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) := getfstwt W.


(**********************************************************************************)


(*relations between continuous and intermittent memory*)


(*Definition 4*)
(*concern: not yet clear to me why we need the vmem parameter; pending further inspection of
 proofs*)
(*idea: helpers for determining if valid subtraces instead of taking in extra Vs*)
(*concern: liberal use of intensional equality with nvmem*)
(*N0, V0 is starting state for both executions
 N1, V1 and Ncomp are middle states of intermittent, continuous respectively
 V1 isn't used anywhere it's just to fill out the type
 N2, V2 is final state for intermittent, once again solely to fill out the type*)
Inductive same_pt: nvmem -> vmem -> command -> command -> nvmem -> nvmem -> Prop:=
same_mem: forall {N0 N1 N2 Ncomp: nvmem}
                  {V0 V1 V2: vmem}
                  {c0 c1: command}
                  {W1 W2: the_write_stuff}
                  {O1 O2: obseq}
                  {w: warvars}
                  (T1: trace_c (N0, V0, c0) (N1, V1, c1) O1 W1)
                  (T2: trace_c (N1, V1, c1) (N2, V2, Ins (incheckpoint w)) O2 W2),
                  (getdomain N1) = (getdomain Ncomp) 
                  -> not (In checkpoint O1)
                  -> not (In checkpoint O2) (*checks checkpoint T2 ends on is nearest checkpoint*)
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap Ncomp) l)
                      -> ((In l (Wt T2)) /\ (In l (FstWt (CTrace_App T1 T2))) /\ not (In l (Wt T1))))
                  -> same_pt N0 V0 c0 c1 N1 Ncomp.
(*Definition 5*)
(*N0, V0 is starting state for both executions
 N1 V1 is middle state for intermittent
N is state of checkpoint at N1
 V1 isn't used anywhere it's just to fill out the type
 N2, V2 is final state for intermittent, once again solely to fill out the type*)
Inductive current_init_pt: nvmem -> vmem -> command -> nvmem -> nvmem -> Prop:=
valid_mem: forall {N N0 N1 N2: nvmem}
                  {V0 V1 V2: vmem}
                  {c: command}
                  {W : the_write_stuff}
                  {O: obseq}
                  {w: warvars}
                  (T: trace_c (N1, V1, c) (N2, V2, Ins (incheckpoint w)) O W),
                  (getdomain N1) = (getdomain N0) 
                  -> not (In checkpoint O) (*checks checkpoint T ends on is nearest checkpoint*)
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap N0) l)
                      -> (In l (FstWt T)) \/ (In (loc_warvar l) (getdomain N)))
                 -> current_init_pt N V1 c N1 N0.

(*Definition 6*)
(*concern: Typo in paper, N0, V0 is left out of invocation of Def 4*)
(*(N0, V0, c0) is checkpoint state at time c1
N1 V c is intermittent state
N2 V c is continuous state starting from same state as checkpoint
concern: using context instead of cconf
 *)
(*took out equality premises and built them into the types*)
Check same_pt.
Inductive same_config: iconf -> context -> Prop :=
  SameConfig: forall(N0 N1 N2: nvmem)
                (V0 V: vmem)
                (c0 c: command),
                same_pt N0 V0 c0 c N1 N2 -> (*nvms are extensionally the same by same_pt
                                          vms and cs are intensionally the same by types*)
                same_config ((N0, V0, c0), N1, V, c) (N2, V, c).
Close Scope list_scope.


