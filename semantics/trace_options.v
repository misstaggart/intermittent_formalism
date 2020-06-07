(*One big evaluation, pointers*)


 Inductive step_term : (list step) -> Prop :=
   Step_Single : forall{C1: context} {N2: nvmem} {V2: vmem} {O: obseq} {W: the_write_stuff},
     cceval_w C1 O (N2, V2, (Ins skip)) W ->
     step_term ((C1, O, W)::[((N2, V2, (Ins skip)), [], emptysets)])
 | Step_Many: forall{L: list step}
     {C1 C2: context} {O1: obseq} {W1: the_write_stuff} (*makes program bigger*)
      (H: L <> nil), 
     step_term L ->
     cceval_w C1 O1 (gethead L H) W1 ->
     step_term ((C1, O1, W1) :: L).

 Inductive trace_c (CL: list step): nat -> nat -> Prop :=
   Trace_C: forall
             (s e: nat)
             (H1: is_true (s <? (List.length CL)))
             (H2: is_true (e <? (List.length CL))),
             step_term CL ->
             trace_c CL s e.
Theorem trace_append : forall {CL: list step} {s1 mid e2: nat}
                                          (T1: trace_c CL s1 mid) (T2: trace_c CL mid e2),
     trace_c CL s1 e2.
  intros. inversion T1. inversion T2. subst.
  apply (Trace_C CL s1 e2 H1 H5 H6). Qed.

(*can step foward or backwards; problem with useless induction principle
 in backwards case*)
Inductive trace_c: context -> context -> obseq -> the_write_stuff -> Type :=
  CTrace_Empty: forall(C: context),
                 trace_c C C nil (nil, nil, nil)
  | CTrace_Single: forall {C1 C2: context} {O: obseq} {WT FW: option loc} {R: list (option loc)},
      cceval_w C1 O C2 WT R FW ->
      trace_c C1 C2 O ([WT], R, [FW])
  | CTrace_Step2: forall{C1 C2 C3: context} {O1 O2 : obseq} {W: the_write_stuff}
                      {WT FW: option loc} {R: list (option loc)},
     trace_c C1 C2 O1 W-> (*steps C2 foward*)
     cceval_w C2 O2 C3 WT R FW->
     trace_c C1 C3 (O1 ++ O2) (append_write W ([WT], R, [FW])) (*W first, then extra step*)
 | CTrace_Step1: forall{C1 C2 Cend: context} {O1 O2 : obseq} {W: the_write_stuff}
                      {WT FW: option loc} {R: list (option loc)},
     trace_c C1 Cend O2 W->
     cceval_w C1 O1 C2 WT R FW-> (*steps C1 foward*)
     C1 <> Cend -> (*has to step at least once*)
     trace_c C2 Cend (tl O2) (step_write W).

(*can step foward or append; problem again with useless induction principle*)
Inductive trace_c: context -> context -> obseq -> the_write_stuff -> Type :=
  CTrace_Empty: forall(C: context),
                 trace_c C C nil (nil, nil, nil)
  | CTrace_Single: forall {C1 C2: context} {O: obseq} {WT FW: option loc} {R: list (option loc)},
      cceval_w C1 O C2 WT R FW ->
      trace_c C1 C2 O ([WT], R, [FW])
  | CTrace_App: forall{C1 Cmid C3: context} {O1 O2 : obseq} {W1 W2: the_write_stuff},
     trace_c C1 Cmid O1 W1-> (*steps C2 foward arbitrary amount*)
     trace_c Cmid C3 O2 W2 ->
     trace_c C1 C3 (O1 ++ O2) (append_write W1 W2) (*W1 first, then extra steps*)
 | CTrace_Step1: forall{C1 C2 Cend: context} {O1 O2 : obseq} {W: the_write_stuff}
                      {WT FW: option loc} {R: list (option loc)},
     trace_c C1 Cend O2 W->
     cceval_w C1 O1 C2 WT R FW-> (*steps C1 foward*)
     C1 <> Cend -> (*has to step at least once*)
     trace_c C2 Cend (tl O2) (step_write W).

(*In general, if you have a type where one constructor makes it smaller
 and another constructor makes it bigger, you get
 a useless induction principle*)
