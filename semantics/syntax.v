Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Import ListNotations.
Open Scope string_scope.
(*setting up naturals equality type*)
Lemma eqnat: Equality.axiom Init.Nat.eqb.
Proof.
  unfold Equality.axiom. intros.
  destruct (Init.Nat.eqb (x) (y)) eqn:beq.
  - constructor. apply beq_nat_true in beq. assumption.
  -  constructor. apply beq_nat_false in beq. assumption.
Qed.
Canonical nat_eqMixin := EqMixin eqnat.
Canonical nat_eqtype := Eval hnf in EqType nat nat_eqMixin.
(*---*)

(*setting up strings equality type*)
(* eqb_string and
eqb_string_true_iff taken from software foundations*)
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Lemma eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [H |Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs *. destruct Hs. reflexivity.
Qed.
(*what the hell is the star*)
Lemma eqstring: Equality.axiom eqb_string.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_string x y) eqn:beq.
  - constructor. apply eqb_string_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_string_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical string_eqMixin := EqMixin eqstring.
Canonical string_eqtype := Eval hnf in EqType string string_eqMixin.
(***)


(*Now, to business! Below is syntax*)

Inductive value :=
    Nat (n: nat)
| Bool (b: bool)
| vBop (v1: value) (v2: value).
Coercion Bool : bool >-> value.

Inductive value1 :=
  Nat1 (n: nat)
| Bool1 (b: bool)
| vBop1 (v1: value) (v2: value) (out: nat + bool)
.

(*val was already taken by a subtype method*)
(*setting up equality type for value*)

Definition eq_valueop (x y : option value) :=
  match x, y with
    None, None => True
  | Some x1, Some y1 =>
    (match x1, y1 with
    Nat nx, Nat ny => is_true(nx == ny)
  | Bool bx, Bool byy => is_true(eqb bx byy)
  | vBop _ _, vBop _ _ => True
  | _, _ => False
  end)
  | _, _ => False
  end.
(*as you can see, the vBop case is fake*)

(*I don't think I NEED to show that it's
 an equality relation but I could*)

Definition map (A: Type) (eqba: A -> A -> bool):= A -> (option value).
Definition emptymap {A} {eqba} :(map A eqba) := (fun _ => None).
Definition updatemap {A} {eqba} (m: map A eqba) (i: A) (v: value) : map A eqba := (fun j =>
                                                               if (eqba j i) then Some v
                                                               else (m j)).

Definition updatemaps {A} {eqba} (m1: map A eqba) (m2: map A eqba): map A eqba :=
  (fun j =>
     match m1 j with
       Some out => Some out
     | None => m2 j
     end
  ).

Definition indomain {A} {eqba} (m: map A eqba) (x: A) :=
  match m x with
    Some _ => True
  | None => False
  end.

Close Scope string_scope.
 (*I'll leave the equality types for now just in case*)
(*only other map necessary is for tasks at first inspection*)
(****)

Inductive array :=
  Array (s: string) (l: nat).

Open Scope type_scope.
Inductive exp :=
  Var (s: string) (*variable*)
| Val (v: value)
| Bop (e1: exp) (e2: exp)
| El (a: array) (e: exp).    (*variable*)

Notation "a '[[' e ']]'" := (El (a) (e))
                            (at level 100, right associativity).


Definition smallvarpred := (fun x=> match x with
                                        Var _ => true
                                        | _ => false
                                 end).
Definition elpred  := (fun x=> match x with
                                        El _ (Val _) => true
                                        | _ => false
                                 end).

(*Definition smallvar := subType smallvarpred.*)
Notation smallvar := {x: exp | smallvarpred x}.
(*how does this work??*)
Notation el := {x: exp| elpred x}.
(*annoying parens here but it complained when I made the level
 higher *)
Definition loc := smallvar + el.
Definition warvar := smallvar + array.
Definition warvars := list warvar.
(*Coercion (inl smallvar el): smallvar >-> loc.*)
(*Coercion inl: smallvar >-> loc.*)

Definition isarrayindex (e: el) (a: array) (ve: value) :=
  match (val e) with
    El a ve  => True
  | _ => False
  end.

Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp)
| asgn_ar (a: array) (i: exp) (e: exp) (*i is index, e is new value of a[i]*)
| incheckpoint (w: warvars)
| inreboot.
(*added the in prefixes to distinguish from the observation reboots
 and checkpoints*)

Inductive command :=
  Instruct (l: instruction)
| Seqcom (l: instruction) (c: command)
| ite (e: exp) (c1: command) (c2: command).

Notation "l ';;' c" := (Seqcom (l) (c))
                         (at level 100).

Notation "'TEST' e 'THEN' c1 'ELSE' c2 " := (ite e c1 c2)
                                                (at level 100).

(*don't need the annoying parens around each arg*)
(***)

(*should the memory map check to see if the expression is actually
 a natural somehow
 i'd have to add some details keeping track of the return type
 of the binary operations*)
(*what is the difference between sub_sort and subType?*)


(*do i need to use fixpoint here or is there another
 keyword for things that aren't recursive..i tried to use
 definition but it didn't let me use proof tactics*)

(*all the strings are the eqtype strings now*)

Fixpoint getstringsv1 (x: smallvar): option string :=
  match val x with
    Var s => Some s
  | _ => None
  end. 

Theorem sv1notnone: forall (x: smallvar), getstringsv1 x <> None.
Proof.
  intros.
  destruct x as [value proof].
    destruct (value) as [s| | |];
  try (simpl in proof; discriminate proof).
  intros contra. discriminate contra.
Qed.

(*fix this lol*)
Theorem stupid: (None: option string) = (None: option string).
Proof.
  reflexivity.
Qed.

Fixpoint getstringsv (x: smallvar): string :=
  (match (getstringsv1 x) as out return (out <> None -> string) with
    Some s => fun _ => s
   | None => fun H => match
                H stupid
              with end
   end) (sv1notnone x).

  (*destruct x as [value proof].
  destruct (value) as [s| | |];
  try (simpl in proof; discriminate proof); return s.*)

Fixpoint getstringel1 (x: el): option string :=
  match val x with
    El (Array s _) _ => Some s
  | _ => None
  end. 

Theorem el1notnone: forall (x: el), getstringel1 x <> None.
Proof.
  intros.
  destruct x as [value proof].
    destruct (value) as [s| | |];
  try (simpl in proof; discriminate proof).
    intros contra. simpl in contra.
    destruct a eqn: H.
    discriminate contra.
Qed.

(*fix this lol*)
Theorem stupid1: (None: option string) = (None: option string).
Proof.
  reflexivity.
Qed.


Fixpoint getstringel (x: el): string :=
  (match (getstringel1 x) as out return (out <> None -> string) with
    Some s => fun _ => s
   | None => fun H => match
                H stupid1
              with end
   end) (el1notnone x).


Definition eqb_loc (l1: loc) (l2: loc) :=
  match l1, l2 with
    inl _, inr _ => false
  | inr _, inl _ => false
  | inl x, inl y => (getstringsv x)==(getstringsv y)
  | inr x, inr y => (getstringel x)==(getstringel y)
  end.

(*do I even need that eqb_loc is equality?
cuz it's becoming a pain to prove
I say table this part till Thursday cuz it's not the
most essential thing you could be doing
Could always set it up later
 *)

(*the subtypes are making things a lot
 more difficult actually because if you didn't have the subtypes
 then you wouldn't have to worry about the match case and
 could prove the equality relation*)

(***)

(*memory syntax*)

(*memory locations defined above warvars*)
Notation mem := (map loc eqb_loc). (*memory mapping*)
Inductive nvmem := (*nonvolatile memory*)
  NonVol (m : mem).
Inductive vmem := (*volatile memory*)
  Vol (m : mem).
Inductive cconf := (*continuous configuration*)
  ContinuousConf (triple: nvmem * vmem * command).
Inductive context :=
  Con (triple: nvmem * vmem * command).
(*do you distinction between context and continuous configuration?
I put one
 *)
Inductive iconf := (*intermittent configuration*)
  IntermittentConf (qple: context * nvmem * vmem * command).
Inductive readobs := (*read observation*)
  NoObs
| rd (l: loc) (v: value)
| Seqrd (r1: readobs) (r2: readobs).
(*I made the checkpoint and reboots different than those
 for instructions but I could make them the same with a subtype*)
Inductive obs := (*observation*)
  Obs (r: readobs)
| reboot
| checkpoint.
Coercion Obs : readobs >-> obs.
Notation obsseq := (list obs). (*observation sequence*)
(*technically I could do subtypes here for obs vs readobs but I don't think it's
 necessary
as we never use the readobs type outside of the obs wrapper
 *)
(*the above is conditional on her being ok with me moving NoObs
 into the readobs type
 otherwise I'll have to do subtypes*)
(***)

(*continuously powered operational semantics*)

Reserved Notation "N';;' V '=[' e ']=>_'r'_' v" (at level 40).
(*don't put the args in front cuz then they;ll be
 indexes not paramaters or whichever way*)
(*Inductive eeval (N: nvmem) (V : vmem) (e: exp) (r: obs) v :=*)
Coercion Val : value >-> exp.
(**why don't these work?**)
(*would be really nice if I could have these so the constructors
 for eeval
 could have consistent arguments wrt nvmem vs mem and similar*)
Coercion NonVol : mem >-> nvmem.
Coercion Vol : mem >-> vmem.
(****)
Inductive eeval: nvmem -> vmem -> exp -> readobs -> value -> Prop :=
VAL: forall(N: nvmem) (V: vmem) (v: value), 
    eeval N V v NoObs v
| BINOP: forall(N: nvmem) (V: vmem) (e1: exp) (e2: exp) (r1: readobs)
      (r2: readobs) (v1: value) (v2: value),
    eeval N V e1 r1 v1 ->
    eeval N V e2 r2 v2 ->
    eeval N V (Bop e1 e2) (Seqrd r1 r2) (vBop v1 v2)
| RD_VAR: forall(mapN: mem)
           (mapV: mem) (e: smallvar) (v: value),
    eq_valueop ((updatemaps mapN mapV) (inl e)) (Some v) ->
    eeval (NonVol mapN) (Vol mapV) (val e) (rd (inl e) v) v
| RD_ARR: forall(a: array)
           (element: el)
           (mapN: mem)
           (mapV: mem)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (v: value),
    eeval (NonVol mapN) (Vol mapV) (index) rindex vindex ->
    eq_valueop ((updatemaps mapN mapV) (inr element)) (Some v) ->
    (isarrayindex element a vindex) -> (*extra premise to check that inr element is actually a[ve] *)
    eeval (NonVol mapN) (Vol mapV) (a[[index]]) (Seqrd rindex (rd (inr element) v) ) v
 (*would be easier to take in an element of loc or just take in evidence that the index that you have is right*)
.
(*would be nice to have a coercion to get the Nonvolatile volatile
 wrapper off*)
 (*need a coercion for the sum type loc*)
(*add notation for infix bop*)

(*
maybe it's cuz ;; was already defined...try this again
ask him why this notation doesn't work
Inductive eeval: nvmem -> vmem -> exp -> obs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value), 
    N;; V =[ v ]=>_reboot_ v
  where "N;; V =[ e ]=>_r_ v" := (eeval N V e r v).
*)

(***)

(*continuous execution semantics*)

(*Not clear where the m|w notation is used*)
(*add notations for the maps on top of page 2*)

Coercion Instruct : instruction >-> command.
Inductive cceval: nvmem -> vmem -> command -> obs -> nvmem -> vmem -> command -> Prop :=
  NV_Assign: forall(x: smallvar) (mapN: mem) (V: vmem) (e: exp) (r: readobs) (v: value),
    indomain mapN (inl x) ->
    eeval (NonVol mapN) V e r v ->
    cceval (NonVol mapN) V (asgn_sv x e) r (NonVol (updatemap mapN (inl x) v)) V skip
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    indomain mapV (inl x) ->
    eeval N (Vol mapV) e r v ->
    cceval N (Vol mapV) (asgn_sv x e) r N (Vol (updatemap mapV (inl x) v)) skip
| Assign_Arr: forall(a: array)
               (element: el)
               (mapN: mem)
               (V: vmem)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value),
    eeval (NonVol mapN) (V) (ei) ri vi ->
    eeval (NonVol mapN) (V) (e) r v ->
    (isarrayindex element a vi) -> (*extra premise to check that element is actually a[vi] *)
    cceval (NonVol mapN) (V) (asgn_ar a ei e) (Seqrd ri r)
           (NonVol (updatemap mapN (inr element) v)) V skip
| CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
               cceval N V ((incheckpoint w);; c) checkpoint
               N V c
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval N V (skip;;c) NoObs N V c
| Seq: forall (N: nvmem)
         (N': nvmem)
         (V: vmem)
         (V': vmem)
         (l: instruction)
         (c: command)
         (o: obs),
    cceval N V l o N' V' skip ->
    cceval N V (l;;c) o N' V' c
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r true ->
    cceval N V (TEST e THEN c1 ELSE c2) r N V c1
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r false ->
    cceval N V (TEST e THEN c1 ELSE c2) r N V c2.
        
Close Scope type_scope.
