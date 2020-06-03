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
Inductive trace_c: context -> obseq -> context -> the_write_stuff -> Prop :=
  CTrace_Single: forall(C1 C2: context) (O: obseq) (W: the_write_stuff),
                  single_com C1 -> (*checks program cannot be stepped more than once*)
                  cceval_w C1 O C2 W -> (*command in C2 is skip by def single_com, cceval_w*)
                  trace_c C1 O C2 W
| CTrace_Step: forall(C1 C2 C3: context) (O1 O2: obseq) 
                (WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc),
    (*not (single_com C1) -> unclear if this is necessary as implied by
     the fact that c1 can be stepped at least twice...
     will try and prove without it and if it gets messy I'll add it*)
    cceval_w C1 O1 C2 (WT1, RD1, FstWt1)-> (*diff between C1 and C2 is 1 step by def cceval_w*)
    trace_c C2 O2 C3 (WT2, RD2, FstWt2) -> (*steps rest of program*)
    trace_c C1 (O1 ++ O2) C3 ((WT1 ++ WT2), (RD1 ++ RD2), (FstWt1 ++ (remove in_loc_b RD1 FstWt2))).
 (*makes for easy subtraces by allowing the command in C3 to not be skip*)

(*intermittent traces*)
 (*the same as trace_c bar types as differences between
  intermittent and continuous execution have been implemented in evals*)
Inductive trace_i: iconf -> obseq -> iconf -> the_write_stuff -> Prop :=
  CTrace_Single: forall(C1 C2: iconf) (O: obseq) (W: the_write_stuff),
                  single_com_i C1 -> (*checks program cannot be stepped more than once*)
                  iceval_w C1 C2 O W -> (*command in C2 is skip by def single_com, iceval_w*)
                  trace_i C1 O C2 W
| CTrace_Step: forall(C1 C2 C3: context) (O1 O2: obseq) 
         (WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc),
    iceval_w C1 O1 C2 (WT1, RD1, FstWt1)-> (*diff between C1 and C2 is 1 step by def iceval_w*)
    trace_i C2 O2 C3 (WT2, RD2, FstWt2)-> (*steps rest of program*)
    trace_i C1 (O1 ++ O2) C3 ((WT1 ++ WT2), (RD1 ++ RD2), (FstWt1 ++ (remove in_loc_b RD1 FstWt2))).

(*relations between continuous and intermittent memory
Inductive same_ex_point: forall(N1 N2 N: nvmem) (V V': vmem) (c c': command),
    same_program: forall(T1 T2: trace_i),
      (getdomain N1) = (getdomain N2) -> (*putting equals for now, if this bites me later on I can define an                                        extensional equality relation with eqtype*)
      (get_start T1) = (N, V, c) ->
      (get_end T1) = (N1, V', c') ->
      (get_start T2) = (N1, V', c') ->
      get_command (get_end T2) = inscheckpoint ->
      no_checkpts T1 ->
      forall(l: loc), not((N1 l) = (N2 loc)) -> ((In l (Wt T1)) /\ (In l (FstWt (T1 @ T2))) /\ not (In l (Wt T1))).
                                          (*same here with equality*)
*)
