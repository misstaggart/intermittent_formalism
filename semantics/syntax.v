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
Check string_eqtype.

(***)
(*syntax *)
Inductive val :=
  Nat (n: nat)
| Yes
| No
| Error
.

Definition map (A: eqType):= A -> val.
(*A need always be an equality type*)
Definition emptymap {A: eqType} :map A := (fun _ => Error).

Definition updatemap {A: eqType} (m: map A) (i: A) (v: val) : map A := (fun j =>
                                                               if (j == i) then v
                                                               else (m j)).
Inductive array :=
  Array (s: string) (l: nat).
(*I don't think you actually need to get stuff out of the arrays lol*)
(*map nat will be for arrays and map string will be for memory*)
Close Scope string_scope.

Open Scope type_scope.

(*what I really want is subtypes*)

Inductive smallvar :=
  SmallVar (s: string).

Inductive el :=
  Elem (a: array) (e: exp).

(*Check nat + nat.
Definition stupid := (nat + nat).*)
(*consider replacing smallvar with arrays of length 1*)
Definition warvar := (smallvar + array).

Close Scope type_scope.

Inductive exp :=
  Var (v: smallvar) (*variable*)
(*it's kind of gross that I have 3 nested constructors here*)
| Val (v: val)
| Bop (e1: exp) (e2: exp)
| El (e: el).    (*variable*)

Notation "L '[' e ']'" := El(Elem (L) (e))
         (at level 100, right associativity).

Definition warvars := list warvar.

Inductive instructions :=
  skip
 | Asgn ()

 (*the ... mean empty yes?*)

(*can't make e a Nat cuz it could be a bop*)
(*is there a method to change the nth element of a list
actually would be easier to do arrays as states as well
because updating is easier
 *)
