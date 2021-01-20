Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Init.Logic.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
From Coq_intermittent Require Import algorithms lemmas_1.

Implicit Types N: nvmem. Implicit Types V: vmem.
Implicit Types O: obseq.
Implicit Types c: command.
Implicit Types W: the_write_stuff.
Implicit Types x: smallvar.

Open Scope type_scope.
(************* program traces*****************)

(*continuous traces*)
Inductive trace_cs: context -> context -> obseq -> the_write_stuff -> Prop :=
  CsTrace_Empty: forall(C: context),
                 trace_cs C C [::] ([::], [::], [::])
  | CsTrace_Single: forall {C1 C2: context} {O: obseq} {W: the_write_stuff},
      cceval_w C1 O C2 W ->
      trace_cs C1 C2 O W
| CsTrace_Cons: forall{C1 Cmid C2: context} {O1 O2: obseq}
               {W1 W2: the_write_stuff},
    trace_cs Cmid C2 O2 W2 -> 
    O2 <> [::] -> 
    cceval_w C1 O1 Cmid W1 ->
    trace_cs C1 C2 (O1 ++ O2) (append_write W1 W2).

(*intermittent traces*)
Inductive trace_i1: iconf -> iconf -> obseq -> the_write_stuff -> Prop :=
  iTrace_Cont: forall(N0: nvmem) (V0: vmem) (c0: command)
    {N N1: nvmem} {V V1: vmem} {c c1: command}
                 {O: obseq} {W: the_write_stuff},
    trace_cs (N, V, c) (N1, V1, c1) O W ->
    checkpoint \notin O ->
    trace_i1 ((N0, V0, c0), N, V, c) ((N0, V0, c0), N1, V1, c1) O W
 | iTrace_RB: forall{N0 N Nmid Nend: nvmem} {V Vmid Vend: vmem} {c cstart cmid cend: command}
                 {O1 O2: obseq} {W1 W2: the_write_stuff},
    trace_cs (N, V, cstart) (Nmid, Vmid, cmid) O1 W1 -> (*first section of trace w
                                                       no reboots*)
    trace_i1 ((N0, V, c), N0 U! Nmid, V, c) ((N0, V, c), Nend, Vend, cend) O2 W2 ->
    (*last section of trace with reboots*)
    checkpoint \notin O1 ->
    checkpoint \notin O2 ->
    trace_i1 ((N0, V, c), N, V, cstart) ((N0, V, c), Nend, Vend, cend)
             (O1 ++ [::reboot] ++ O2)
             (append_write W1 W2)
 | iTrace_CP: forall{Nc0 N0 Nmid Nc1 Nend: nvmem} {Vc0 V0 Vmid Vc1 Vend: vmem}
                         {cc0 c0 crem cc1 cend: command}
                         {O1 O2: obseq} {W1 W2: the_write_stuff}
      {w: warvars} (Hw: wf_dom w (getmap Nmid)),
      trace_i1 ((Nc0, Vc0, cc0), N0, V0, c0) ((Nc0, Vc0, cc0), Nmid, Vmid,
                                                               (incheckpoint w);;crem) O1 W1 (*1st
                                                                                               checkpointed section*)
                        -> checkpoint \notin O1
                        -> trace_i1 (((restrict Nmid w Hw), Vmid, crem), Nmid, Vmid, crem)
                                   ((Nc1, Vc1, cc1), Nend, Vend, cend) O2 W2 (*remainder of trace*)
                        -> trace_i1 ((Nc0, Vc0, cc0), N0, V0, c0)
                                   ((Nc1, Vc1, cc1), Nend, Vend, cend)
                                   (O1 ++ [::checkpoint] ++ O2)
                                   (append_write W1 W2).

Definition end_com c := c = Ins skip \/ exists(crem: command)(w: warvars), c= (incheckpoint w);; crem.
