Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program Init.Logic.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
From Semantics Require Import algorithms lemmas_1.

Open Scope list_scope.

Open Scope type_scope.
(************* program traces*****************)

(*trace helpers*)

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
2. ending configuration
3. execution observations
4. a list of warvars which have been written to
5. a list of warvars which have been read from
6. a list of warvars which have been written to before they have been read from
 *)
(*Ordering: start -> end -> observations -> the_write_stuff*)
(*steps to termination, accumulates write data*)

(*continuous traces*)
Inductive trace_c: context -> context -> obseq -> the_write_stuff -> Type :=
  CTrace_Empty: forall(C: context),
                 trace_c C C nil (nil, nil, nil)
  | CTrace_Single: forall {C1 C2: context} {O: obseq} {W: the_write_stuff},
      cceval_w C1 O C2 W ->
      trace_c C1 C2 O W
| CTrace_App: forall{C1 C2 Cmid: context} {O1 O2: obseq}
               {W1 W2: the_write_stuff},
    trace_c C1 Cmid O1 W1 -> (*steps first section*)
    O1 <> [] -> (* forces empty step to use other constructors*)
    O2 <> []  ->
    trace_c Cmid C2 O2 W2 -> (*steps rest of program*)
    trace_c C1 C2 (O1 ++ O2) (append_write W1 W2).
(*App makes for easy subtraces by allowing command in C2 not to be skip*)
(*never actually need to append traces now that I have the write datatype
 consider a simpler type?*)

(*tracks write data accumulated when executing from first command to second command
 prevents me from having to prove the existence of traces every five seconds
 bool keeps track of whether we've passed a checkpoint in which case, in all the proofs,
 you want to wipe the write data*)
Inductive write_right: command -> command -> bool -> the_write_stuff -> Prop :=
  Empty_Writes : forall(c: command),
                 write_right c c false (nil, nil, nil)
|  Single_Writes : forall (c1 c2: command) (W: the_write_stuff),
      (exists (N1 N2: nvmem) (V1 V2: vmem) (O: obseq),
        cceval_w (N1, V1, c1) O (N2, V2, c2) W /\ (*doesn't matter that every time this
                                                   constructor is used
                                                   you can pick random mems bc
                                                   writes are determined solely
                                                   by commands*)
      not (In checkpoint O)) -> (*makes CP use the other constructor*)
      write_right c1 c2 false W (*have not passed a CP*)
|  Single_Writes_CP : forall (c1 c2: command) (W: the_write_stuff),
      (exists (N1 N2: nvmem) (V1 V2: vmem) (O: obseq),
          cceval_w (N1, V1, c1) O (N2, V2, c2) W ->
      (In checkpoint O)) -> (*makes other commands use the other constructor*)
      write_right c1 c2 true W
| Write_App: forall{c1 c2 cmid: command}
              {W1 W2: the_write_stuff}
              {b1 b2: bool},
    c1 <> cmid -> (* forces empty step to use other constructors*)
    c2 <> cmid  ->
    write_right c1 cmid b1 W1 -> (*steps first section*)
    write_right cmid c2 b2 W1 -> (*steps second section*)
    write_right c1 c2 (orb b1 b2) (append_write W1 W2).

(*proofs for trace append*)

Lemma empty_trace: forall{C1 C2: context} {O: obseq} {W: the_write_stuff},
    trace_c C1 C2 O W -> O = [] -> C1 = C2 /\ W = emptysets.
Proof. intros. inversion X; subst.
       + split; reflexivity.
       + inversion H0.
       + exfalso. apply app_eq_nil in H4. destruct H4. apply H0. assumption.
Qed.

Lemma append_write_empty: forall{W: the_write_stuff},
    append_write W emptysets = W.
Proof. intros. simpl. unfold append_write. simpl.
       repeat rewrite app_nil_r.
       apply undo_gets.
Qed.


Lemma append_write_empty_l: forall{W: the_write_stuff},
    append_write emptysets W = W.
Proof. intros. simpl. unfold append_write. simpl.
       unfold remove. unfold in_loc_b.
       rewrite filter_false.
       apply undo_gets.
Qed.

Program Definition trace_append {C1 Cmid C2: context }
                  {O1 O2: obseq}
                  {W1 W2: the_write_stuff}
                  (T1: trace_c C1 Cmid O1 W1)
                  (T2: trace_c Cmid C2 O2 W2) : trace_c C1 C2 (O1 ++ O2) (append_write W1 W2)
  :=
  match O1, O2 with
    [], [] => T1 (*C1 = Cmid = C2*)
  | [], _ => T2 (*C1 = Cmid*)
  | _, [] => T1 (**)
  | (x::xs), (y::ys) => CTrace_App T1 _ _ T2 end.

(*clean up this ltac*)
Ltac empty T2 :=apply empty_trace in T2; [destruct T2 as [f g ]; inversion f; subst; try reflexivity |
                                           reflexivity].
Ltac empty2 T1 T2 := apply empty_trace in T1; [destruct T1 as [f g]; inversion g;
                 subst; apply empty_trace in T2; [ destruct T2 as [h i]; inversion i;
                 rewrite append_write_empty; reflexivity | reflexivity] | reflexivity].

Ltac emptyl T2 :=apply empty_trace in T2; [destruct T2 as [f g ]; inversion g; subst; try reflexivity |
                                           reflexivity].

Next Obligation. empty T2. Qed. 
Next Obligation. empty2 T1 T2. Qed.           
Next Obligation. empty T1. Qed.
Next Obligation. emptyl T1. rewrite append_write_empty_l. reflexivity. Qed. 
Next Obligation. empty T2. Qed.
Next Obligation. symmetry. apply app_nil_r. Qed.
Next Obligation. emptyl T2. rewrite append_write_empty. reflexivity. Qed.
Next Obligation. split. intros wildcard contra. destruct contra. inversion H1.
                 intros contra. destruct contra. inversion H1. Qed.


(*intermittent traces*)
 (*the same as trace_c bar types as differences between
  intermittent and continuous execution have been implemented in evals*)
Inductive trace_i : iconf -> iconf -> obseq -> the_write_stuff -> Prop :=
iTrace_Empty: forall{C: iconf},
                 trace_i C C nil (nil, nil, nil)
|iTrace_Single: forall{C1 C2: iconf} {O: obseq} {W: the_write_stuff},
    iceval_w C1 O C2 W ->
    trace_i C1 C2 O W
| iTrace_App: forall{C1 C2 Cmid: iconf} {O1 O2: obseq}
         {W1 W2: the_write_stuff},
    trace_i C1 Cmid O1 W1 -> (*steps first section*)
    trace_i Cmid C2 O2 W2 -> (*steps rest of program*)
    O1 <> [] -> (* forces empty step to use other constructors*)
    O2 <> []  ->
    trace_i C1 C2 (O1 ++ O2) (append_write W1 W2).
Definition multi_step_c (C1 C2: context) (O: obseq) :=
    exists W: the_write_stuff, inhabited (trace_c C1 C2 O W).
          

Definition multi_step_i (C1 C2: iconf) (O: obseq) :=
    exists W: the_write_stuff, trace_i C1 C2 O W.
(*more trace helpers*)

Definition Wt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) := getwt W.

Definition Rd {C1 C2: context} {O: obseq} {W: the_write_stuff}
           (T: trace_c C1 C2 O W) := getrd W.

Definition FstWt {C1 C2: context} {O: obseq} {W: the_write_stuff}
  (T: trace_c C1 C2 O W) := getfstwt W.


(**********************************************************************************)


(*relations between continuous and intermittent memory*)


(*Definition 4*)
(*concern: not yet clear to me why we need the vmem parameter; pending further inspection of
 proofs*)
(*concern: liberal use of intensional equality with nvmem*)
(*N0, V0 c0 is starting state for both executions
 N1, V1 and Ncomp are middle states of intermittent, continuous respectively
 V1 isn't used anywhere it's just to fill out the type
 N2, V2 is final state for intermittent, once again solely to fill out the type*)
Inductive same_pt: nvmem -> vmem -> command -> command -> nvmem -> nvmem -> Prop:=
same_mem: forall (N0 N1 Ncomp: nvmem)
                  (V0: vmem)
                  {c0 c1 crem: command}
                  {W1 W2: the_write_stuff}
                  {w: warvars}
                  {b1 b2: bool}
                  (H1: write_right c0 c1 b1 W1) (*proof W1 is the right stuff*)
                  (H2: write_right c1 ((incheckpoint w);; crem) b2 W2), (*proof W2 is the right stuff*)
                  (getdomain N1) = (getdomain Ncomp) 
                  -> (b1 = false)
                  -> (b2 = false) (*checks checkpoint T2 ends on is nearest checkpoint*)
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap Ncomp) l)
                      -> ((In l (getwt W2)) /\ (In l (getfstwt (append_write W1 W2))) /\ not (In l (getwt W1))))
                  -> same_pt N0 V0 c0 c1 N1 Ncomp.
(*Definition 5*)
(*N0 is starting, reference nvm
 N1 V1 is middle state for intermittent
N, V, c is checkpoint at middle state of intermittent
 N2, V2 is final state for intermittent, not used, solely to fill out the type*)
Inductive current_init_pt: nvmem -> vmem -> command -> nvmem -> nvmem -> Prop:=
  valid_mem: forall {N N0 N1: nvmem}
                  {V: vmem}
                  {c crem: command}
                  {W : the_write_stuff}
                  {w: warvars}
                  {b: bool}
                  (H: write_right c ((incheckpoint w);; crem) b W), (*proof W1 is the right stuff*)
                  (getdomain N1) = (getdomain N0) 
                  -> b = false (*checks checkpoint T ends on is nearest checkpoint*)
                 -> (forall(l: loc),
                      not((getmap N1) l = (getmap N0) l)
                      -> (In l (getfstwt W)) \/ (In (loc_warvar l) (getdomain N)))
                 -> current_init_pt N V c N1 N0.

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
Close Scope type_scope.
