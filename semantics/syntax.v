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
| Yes
| No
| Error
.
(*val was already taken by a subtype method*)
(*just have map take the equality function in as an argument*)
Definition map (A: Type) (eqba: A -> A -> bool):= A -> value.
Definition emptymap {A} {eqba} :(map A eqba) := (fun _ => Error).
Definition updatemap {A} {eqba} (m: map A eqba) (i: A) (v: value) : map A eqba := (fun j =>
                                                               if (eqba j i) then v
                                                               else (m j)).
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
                                        Var s => true
                                        | _ => false
                                 end).

(*Definition smallvar := subType smallvarpred.*)
Notation smallvar := {x: exp | smallvarpred x}.
(*how does this work??*)
Definition el := {x: exp|  exists(a: array) (e: exp), x = (a[[e]])}.
(*annoying parens here but it complained when I made the level
 higher *)
Definition loc := smallvar + array.
Definition warvars := list loc.

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

(*setting up equality type for locations*)

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


Fixpoint getstringsarr (a:array): string :=
  match a with
    Array s _ => s
  (*destruct (a) as [s ]. exact s. *)
end.


Definition eqb_loc (l1: loc) (l2: loc) :=
  match l1, l2 with
    inl _, inr _ => false
  | inr _, inl _ => false
  | inl x, inl y => (getstringsv x)==(getstringsv y)
  | inr x, inr y => (getstringsarr x)==(getstringsarr y)
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
  Nonvolatile (m : mem).
Inductive vmem := (*volatile memory*)
  Volatile (m : mem).
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
  rd (l: loc) (v: value)
| Seqrd (r1: readobs) (r2: readobs).
(*I made the checkpoint and reboots different than those
 for instructions but I could make them the same with a subtype*)
Inductive obs := (*observation*)
  Empty
| Obs (r: readobs)
| reboot
| checkpoint.
Notation obsseq := (list obs). (*observation sequence*)
(***)
(*technically I could do subtypes here for obs vs readobs but I don't think it's
 necessary*)
(*continuously powered operational semantics*)
Reserved Notation "N ',' V '|-' e '==>_'r v" (at level 90, left associativity).
Inductive cceval (N: nvmem) (V : vmem) (e: exp) (r: readobs) v :=
  VAL: N ',' V '|-' e '==>_'r v

Close Scope type_scope.
