Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Semantics Require Import semantics cceval2.

Program Definition single_com (C: context) :=
  match C with (_, _, c) =>
  (match c with
    Ins _ => True
  | _ => False end) end.

(*steps to termination, accumulates write data*)
Inductive trace_c: context -> obseq -> context -> the_write_stuff -> Prop :=
  CTrace_Single: forall(C1 C2: context) (O: obseq) (W: the_write_stuff)
                  cceval_w C1 C2 O W -> (*command in C2 is skip by def single_com, cceval_w*)
                  trace_c C1 O C2 W
| CTrace_Step: forall(C1 C2 C3: context) (O1 O2: obseq) 
         (WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc),
    cceval_w C1 O1 C2 WT1 RD1 FstWt1-> (*diff between C1 and C2 is 1 step by def cceval_w*)
    trace_c C2 C3 WT2 RD2 FstWt2 O2-> (*steps rest of program*)
    trace_c C1 (O1 ++ O2) C3 (WT1 ++ WT2) (RD1 ++ RD2) (FstWt1 ++ (remove in_loc_b RD1 FstWt2)).
 (*makes for easy subtraces by allowing the command in C3 to not be skip*)

(*trace_i*)
(*start -> end -> written -> read -> written before reading -> obseq*)
(*chose to include context in start and end values to ensure consistency with iceval
 in reboot case*)
(*Inductive trace_i: iconf -> iconf -> (list loc) -> (list loc) -> (list loc) -> obseq -> Prop :=
  iTrace_PowerFail: forall(k: context) (N: nvmem) (V: vmem) (c: command),
    iceval k N V c
    trace_i (k, N, V, c) (k, N, (reset V), Ins inreboot) nil nil nil nil 
 | iTrace_CheckPoint: forall(k: context) (N: nvmem) (V: vmem) (c: command) (w: warvars),
     trace_i (k, N, V, (incheckpoint w);;c) (((N |! w), V, c), N, V, c)
             nil nil nil [checkpoint].
 | CP_Reboot: forall(N: nvmem) (N': nvmem)(*see below*) (*N is the checkpointed one*)
               (V: vmem) (V': vmem)
               (c: command), 
     trace_i ((N, V, c), N', V', Ins inreboot) ((N, V, c), N U! )
     iceval (N, V, c) N' V' inreboot
            [reboot]
            (N, V, c) (N U! N') V c
  CTrace_Assign_nv: forall(x: smallvar) (N N': nvmem) (V V': vmem) (e: exp) (r: readobs),
    isNV(x) -> (*checks x is in NV memory*)
    cceval N V (asgn_sv x e) [Obs r] N' V' skip ->
    trace_c (N, V, Ins (asgn_sv x e)) (N', V', Ins skip)
            [inl x]  (readobs_loc r) [inl x] [Obs r]
| CTrace_Assign_v: forall(x: smallvar) (N N': nvmem) (V V': vmem) (e: exp) (r: readobs),
    isV(x) -> (*checks x is in volatile memory*)
    cceval N V (asgn_sv x e) [Obs r] N' V' skip ->
    trace_c (N, V, Ins (asgn_sv x e)) (N', V', Ins skip)
            nil  (readobs_loc r) nil [Obs r]
| CTrace_Assign_Arr: forall (N N': nvmem) (V V': vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (e: exp)
               (r: readobs)
               (element: el),
    (el_arrayexp_eq element a ei N V) -> (*extra premise to check that inr element
                                        is actually a[ei] *)
    cceval N V (asgn_arr a ei e) [Obs (ri++r)] N' V' skip ->
    trace_c (N, V, Ins (asgn_arr a ei e)) (N', V', Ins skip)
            [inr element] (readobs_loc (ri ++ r)) [inr element] [Obs (ri ++ r)]
| CTrace_CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
    trace_c (N, V, (incheckpoint w);; c) (N, V, c)
            nil nil nil [checkpoint]
| CTrace_Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    trace_c (N, V, skip;; c) (N, V, c)
            nil nil nil [Obs NoObs]
| CTrace_Seq: forall (N N' N'': nvmem)
         (V V' V'': vmem)
         (WT1 RD1 FstWt1 WT2 RD2 FstWt2: list loc)
         (O1 O2: obseq)
         (l: instruction)
         (c: command)
         (r: readobs),
    trace_c (N, V, Ins l) (N', V', Ins skip) WT1 RD1 FstWt1 O1 ->
    trace_c (N', V', c) (N'', V'', Ins skip) WT2 RD2 FstWt2 O2->
    trace_c (N, V, l;;c) (N'', V'', Ins skip) (WT1 ++ WT2) (RD1 ++ RD2) (FstWt1 ++ (remove in_loc_b RD1 FstWt2))
            (O1 ++ O2)
| CTrace_If_T: forall(N N': nvmem)
                (V V': vmem)
                (WT RD FstWt: list loc)
                (e: exp)
                (r: readobs)
                (c1 c2: command)
                (O1: obseq)
  ,
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c1 ->
    trace_c (N, V, c1) (N', V', Ins skip) WT RD FstWt O1 ->
    trace_c (N, V, TEST e THEN c1 ELSE c2) (N', V', Ins skip) WT ((readobs_loc r) ++ RD) FstWt ((Obs r)::O1) 
| CTrace_If_F: forall(N N': nvmem)
                (V V': vmem)
                (WT RD FstWt: list loc)
                (e: exp)
                (r: readobs)
                (c1 c2: command)
                (O2: obseq),
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c2 ->
    trace_c (N, V, c2) (N', V', Ins skip) WT RD FstWt O2->
    trace_c (N, V, TEST e THEN c1 ELSE c2) (N', V', Ins skip) WT ((readobs_loc r) ++ RD) FstWt ((Obs r)::O2).
(*last one necessary to compute nearest checkpoint*)

(*relations between continuous and intermittent memory*)
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
