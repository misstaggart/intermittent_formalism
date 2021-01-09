Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Import ListNotations.
From Semantics Require Import semantics.
(*basic list functions that I couldn't find in a library*)
Open Scope list_scope.
Open Scope type_scope.

(*written, read, written before reading*)
Notation the_write_stuff := ((list loc) * (list loc) * (list loc)).

(*Single steps, accumulates write data*)
(*warning: OLD version below, most updated one in semantics*)
Inductive cceval_w: context -> obseq -> context -> the_write_stuff -> Prop :=
CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
    cceval_w (N, V, ((incheckpoint w);; c))
             [checkpoint]
             (N, V, c)
             (nil, nil, nil)
| NV_Assign: forall(x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, V, Ins (asgn_sv x e))
             [Obs r]
             ((updateNV N (inl x) v), V, Ins skip)
             ([inl x],  (readobs_loc r), (remove in_loc_b (readobs_loc r) [inl x]))
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, (Vol mapV), Ins (asgn_sv x e)) [Obs r]
             (N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
             (nil,  (readobs_loc r), nil)
| Assign_Arr: forall (N: nvmem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (el_arrayind_eq element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, V, Ins (asgn_arr a ei e))
           [Obs (ri++r)]
           ((updateNV N (inr element) v), V, Ins skip)
           ([inr element], (readobs_loc (ri ++ r)), (remove in_loc_b (readobs_loc (ri ++ r)) [inr element]))
(*valuability and inboundedness of vindex are checked in sameindex*)
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval_w (N, V, (skip;;c)) [Obs NoObs] (N, V, c) (nil, nil, nil)
| Seq: forall (N N': nvmem)
         (V V': vmem)
         (l: instruction)
         (c: command)
         (o: obs)
         (WT1 RD1 FstWt1: list loc),
    cceval_w (N, V, Ins l) [o] (N', V', Ins skip) (WT1, RD1, FstWt1) ->
    cceval_w (N, V, (l;;c)) [o] (N', V', c) (WT1, RD1, FstWt1)
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> (*yuh doy not writing anything in eeval*)
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c1) (nil, (readobs_loc r), nil)
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c2) (nil, (readobs_loc r), nil).

(*Inductive iceval: iconf -> obseq -> iconf -> Prop :=
  CP_PowerFail: forall(k: context) (N: nvmem) (V: vmem) (c: command),
                 iceval (k, N, V, c)
                        nil
                        (k, N, (reset V), Ins inreboot)
 | CP_CheckPoint: forall(k: context) (N: nvmem) (V: vmem) (c: command) (w: warvars),
                 iceval (k, N, V, ((incheckpoint w);;c))
                        [checkpoint]
                        (((N |! w), V, c), N, V, c) 
 | CP_Reboot: forall(N N': nvmem) (*see below*) (*N is the checkpointed one*)
               (V V': vmem) 
               (c: command), 
     iceval ((N, V, c), N', V', Ins inreboot)
            [reboot]
            ((N, V, c), (N U! N'), V, c)
 | CP_NV_Assign: forall(k: context) (x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval (k, N, V, Ins (asgn_sv x e))
           [Obs r]
           (k, (updateNV N (inl x) v), V, Ins skip)
| CP_V_Assign: forall(k: context) (x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval (k, N, (Vol mapV), Ins (asgn_sv x e))
           [Obs r]
           (k, N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
| CP_Assign_Arr: forall (k: context) (N: nvmem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (el_arrayind_eq element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval (k, N, V, Ins (asgn_arr a ei e))
           [Obs (ri++r)]
           (k, (updateNV N (inr element) v), V, Ins skip)
| CP_Skip: forall(k: context) (N: nvmem)
         (V: vmem)
         (c: command),
    iceval (k, N, V, (skip;;c)) [Obs NoObs] (k, N, V, c)
|CP_Seq: forall (k: context)
         (N: nvmem) (N': nvmem)
         (V: vmem) (V': vmem)
         (l: instruction)
         (c: command)
         (o: obs),
    iceval (k, N, V, Ins l) [o] (k, N', V', Ins skip) ->
    iceval (k, N, V, (l;;c)) [o] (k, N', V', c)
|CP_If_T: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> 
    iceval (k, N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (k, N, V, c1)
|CP_If_F: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    iceval (k, N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (k, N, V, c2).*)
