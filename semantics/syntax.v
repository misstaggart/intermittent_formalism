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


Inductive value1 :=
  Nat1 (n: nat)
| Bool1 (b: bool)
| vBop1 (v1: value) (v2: value) (out: nat + bool)
.

(*val was already taken by a subtype method*)
(*setting up equality type for value*)

Definition eqb_valueop (x y : option value) : bool :=
  match x, y with
    None, None => true
  | Some x1, Some y1 =>
    (match x1, y1 with
    Nat nx, Nat ny => nx == ny
  | Bool bx, Bool byy => eqb bx byy
  | vBop _ _, vBop _ _ => true
  | _, _ => false
  end)
  | _, _ => false
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
                                        El _ _ => true
                                        | _ => false
                                 end).

(*Definition smallvar := subType smallvarpred.*)
Notation smallvar := {x: exp | smallvarpred x}.
(*how does this work??*)
Notation el := {x: exp| elpred x}.
(*annoying parens here but it complained when I made the level
 higher *)
Definition loc := smallvar + el.
Definition warvars := list loc.
Print sum.
(*Coercion (inl smallvar el): smallvar >-> loc.*)
(*Coercion inl: smallvar >-> loc.*)



Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp)
| asgn_ar (y : el) (e': exp) (*where y has the form a[[e]],
                      pretty sure I'm not allowed to write it like that
                      in here
                     *)
| incheckpoint (omega: warvars)
| inreboot.
(*added the in prefixes to distinguish from the observation reboots
 and checkpoints*)

Inductive command :=
  Instruct (l: instruction)
| Seq (l: instruction) (c: command)
| ite (e: exp) (c1: command) (c2: command).

Notation "l ';;' c" := (Seq (l) (c))
                         (at level 100).

Notation "'TEST' e ''THEN' c1 'ELSE' c2 " := (ite e c1 c2)
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

Reserved Notation "N';;' V '=[' e ']=>_'r'_' v" (at level 0).
(*don't put the args in front cuz then they;ll be
 indexes not paramaters or whichever way*)
(*Inductive cceval (N: nvmem) (V : vmem) (e: exp) (r: obs) v :=*)
Coercion Val : value >-> exp.

Inductive cceval: nvmem -> vmem -> exp -> readobs -> value -> Prop :=
VAL: forall(N: nvmem) (V: vmem) (v: value), 
    cceval N V v NoObs v
| BOP: forall(N: nvmem) (V: vmem) (e1: exp) (e2: exp) (r1: readobs)
      (r2: readobs) (v1: value) (v2: value),
    cceval N V e1 r1 v1 ->
    cceval N V e2 r2 v2 ->
    cceval N V (Bop e1 e2) (Seqrd r1 r2) (vBop v1 v2)
| RD_VAR: forall(mapN: mem)
           (mapV: mem) (e: smallvar) (v: value),
    is_true(eqb_valueop ((updatemaps mapN mapV) (inl e)) (Some v)) ->
    cceval (NonVol mapN) (Vol mapV) (val e) (rd (inl e) v) v
| RD_ARR: forall(mapN: mem)
           (mapV: mem) (e: el) (r: readobs) (re: readobs)  (v: value) (ve: value),
    cceval N V (val e) re ve ->
    is_true(eqb_valueop ((updatemaps mapN mapV) (inr (a[ve]))) (Some v)) ->
    is_true(isindex e)
    cceval (NonVol mapN) (Vol mapV) (a[ve]) (rd (inr e) v) v
 (*would be easier to take in an element of loc or just take in evidence that the index that you have is right*)
 .
(*would be nice to have a coercion to get the Nonvolatile volatile
 wrapper off*)
 (*need a coercion for the sum type loc*)
(*add notation for infix bop*)

(*
ask him why this notation doesn't work
Inductive cceval: nvmem -> vmem -> exp -> obs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value), 
    N;; V =[ v ]=>_reboot_ v
  where "N;; V =[ e ]=>_r_ v" := (cceval N V e r v).
*)


Close Scope type_scope.
