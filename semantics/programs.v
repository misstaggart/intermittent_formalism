Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Semantics Require Import semantics cceval2.

(************* program traces*****************)

(*trace helpers*)

Definition el_arrayexp_eq (e: el) (a: array) (eindex: exp) (N: nvmem) (V: vmem) := (*transitions from el type to a[exp] representation*)
  (samearray e a) /\
  exists(r: readobs) (vindex: value), eeval N V eindex r vindex /\
                                 (eq_value (getindexel e) vindex).

Program Definition single_com (C: context) :=
  match C with (_, _, c) =>
  (match c with
    Ins _ => True
   | _ => False end) end.

(*start here*)

Program Definition single_com_i (C: iconf) :=
  match C with (_, _, c) =>
  (match c with
    Ins _ => True
  | _ => False end) end.
(*Notes:*)
(*do I keep track of volatile writes as well...I don't think so
 cuz the writes don't last and they all have to be checkpointed anyways*)
(*concern:*)
(*actually there's no reason for us to be checkpointing volatiles that are
 written to before they're ever read from along any path*)
(*at first inspection it doesn't seem like it would be all that hard to keep track of this
 since we're already doing MFstWt for novolatiles.*)

(* Concern:
DO need one step evaluation in order to stop at a checkpoint...nvm lol
 *)

(*using context instead of cconf cuz they're exactly the same
 but cconf has an annoying constructor*)




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
  CTrace_Single: forall {C1 C2: context} {O: obseq} {W: the_write_stuff},
                  single_com C1 -> (*checks program cannot be stepped more than once*)
                  cceval_w C1 O C2 W -> (*command in C2 is skip by def single_com, cceval_w*)
                  trace_c C1 C2 O W
| CTrace_App: forall{C1 C2 Cmid: context} {O1 O2: obseq}
                {WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc},
    (*not (single_com C1) -> unclear if this is necessary as implied by
     the fact that c1 can be stepped at least twice...
     will try and prove without it and if it gets messy I'll add it*)
    trace_c C1 Cmid O1 (WT1, RD1, FstWt1)-> (*steps first section*)
    trace_c Cmid C2 O2 (WT2, RD2, FstWt2) -> (*steps rest of program*)
    trace_c C1 C2 (O1 ++ O2)((WT1 ++ WT2), (RD1 ++ RD2), (FstWt1 ++ (remove in_loc_b RD1 FstWt2))).
 (*App makes for easy subtraces by allowing the trace to be partitioned anywhere*)

(*intermittent traces*)
 (*the same as trace_c bar types as differences between
  intermittent and continuous execution have been implemented in evals*)
Inductive trace_i (C1 C2: iconf): obseq -> the_write_stuff -> Prop :=
  iTrace_Single: forall(O: obseq) (W: the_write_stuff),
                  single_com_i C1 -> (*checks program cannot be stepped more than once*)
                  iceval_w C1 O C2 W -> (*command in C2 is skip by def single_com, iceval_w*)
                  trace_i C1 C2 O W
| iTrace_App: forall{Cmid: iconf} {O1 O2: obseq}
         {Wt1 RD1 FstWt1 Wt2 RD2 FstWt2: list loc},
    trace_i C1 Cmid O1 (Wt1, RD1, FstWt1)-> (*steps first section*)
    trace_i Cmid C2 O2 (Wt2, RD2, FstWt2)-> (*steps rest of program*)
    trace_i C1 C2 (O1 ++ O2)((Wt1 ++ Wt2), (RD1 ++ RD2), (FstWt1 ++ (remove in_loc_b RD1 FstWt2))).

(*more trace helpers*)

Check iTrace_App.

Definition Wt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) :=
  match W with (out, _, _ )=> out end.


Definition FstWt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) :=
  match W with (_, _, out)=> out end.

Check CTrace_App.
(*hacky fix...unbelievable that coq is stupid enough to make me need this...
 when I try to use the CTrace_App constructor straight he complains that I'm passing in
 the_write_stuff when I should actually be giving a triple...doesn't unfold the types??
 Ask Arthur about this*)
(*Program Definition append {C1 C2 Cmid: context} {O1 O2: obseq}
         {W1 W2: the_write_stuff}
    (T1: trace_c C1 Cmid O1 W1)
    (T2: trace_c Cmid C2 O2 W2) :=
       match W1, W2 with (Wt1, Rd1, FstWt1), (Wt2, Rd2, FstWt2) =>
           CTrace_App (trace_c C1 Cmid O1 (Wt1, Rd1, FstWt1)) (trace_c Cmid C2 O2 (Wt2, Rd2, FstWt2)) end. *)
(*Definition append {C1 C2 Cmid: context} {O1 O2: obseq}
         {WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc}
    (T1: trace_c C1 Cmid O1 W1)
    (T2: trace_c Cmid C2 O2 W2) :=
       match T1, T2 with trace_i C1 Cmid O1 (Wt1, Rd1, FstWt1),
                         trace_i Cmid C2 O2 (Wt2, Rd2, FstWt2) =>
           CTrace_App (trace_i C1 Cmid O1 (Wt1, Rd1, FstWt1)) (trace_i Cmid C2 O2 (Wt2, Rd2, FstWt2)) end.*)


(*trace_i C1 Cmid O1 (WT1, RD1, FstWt1)-> (*steps first section*)
    trace_i Cmid C2 O2 (WT2, RD2, FstWt2)-> *)



(*Program Definition append {C1 Cmid C2: context} {O1 O2: obseq} {W1 W2: }
        (T1: trace_c C1 Cmid) (T2: trace_c Cmid C3) :=
  match T1, T2 with*)


(**********************************************************************************)


(*relations between continuous and intermittent memory*)

(*concern: not yet clear to me why we need the vmem parameter; pending further inspection of
 proofs*)
(*idea: helpers for determining if valid subtraces instead of taking in extra Vs*)
(*concern: liberal use of intensional equality with nvmem*)
Inductive same_ex_point: vmem -> command -> command -> nvmem -> nvmem -> Prop:=
same_program: forall {N0 N1 N2: nvmem}
                  {V0 V1 V2: vmem}
                  {c0 c1: command}
                  {W1 W2: the_write_stuff}
                  {O1 O2: obseq}
                  {w: warvars}
                  (Ncomp: nvmem)
                  (T1: trace_c (N0, V0, c0) (N1, V1, c1) O1 W1)
                  (T2: trace_c (N1, V1, c1) (N2, V2, Ins (incheckpoint w)) O2 W2),
                  (getdomain N1) = (getdomain Ncomp) 
                  -> not (In checkpoint O1)
                  -> not (In checkpoint O2) (*checks checkpoint T2 ends on is nearest checkpoint*)
                  (forall(l: loc),
                      not((getmap N1) l = (getmap Ncomp) l)
                      -> ((In l (Wt T1)) /\ (In l (FstWt (CTrace_App T1 T2))) /\ not (In l (Wt T1))))
                  -> same_ex_point V0 c0 c1 N1 Ncomp.
(*need to check for NEAREST checkpoint
well, the checkpoint T2 ends on hasn't been executed yet, so shouldn't so up in observation sequence
 *)

