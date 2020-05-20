Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.Subset.
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

(*Now, to business! Below is syntax*)
Inductive val :=
  Nat (n: nat)
| Yes
| No
| Error
.

Definition map (A: eqType):= A -> val.
Definition emptymap {A: eqType} :map A := (fun _ => Error).
Definition updatemap {A: eqType} (m: map A) (i: A) (v: val) : map A := (fun j =>
                                                               if (j == i) then v
                                                               else (m j)).
Close Scope string_scope.
(*map nat will be for arrays and map string will be for memory*)
(*except you don't actually need to get stuff out of the
 arrays but I'll leave the equality types for now just in case*)
(****)

Inductive array :=
  Array (s: string) (l: nat).

Open Scope type_scope.
Inductive exp :=
  Var (s: string) (*variable*)
| Val (v: val)
| Bop (e1: exp) (e2: exp)
| El (a: array) (e: exp).    (*variable*)

Notation "a '[[' e ']]'" := (El (a) (e))
                            (at level 100, right associativity).

Definition smallvar := {x: exp|  exists(s: string), x = Var s}.
Definition el := {x: exp|  exists(a: array) (e: exp), x = (a[[e]])}.
(*annoying parens here but it complained when I made the level
 higher *)
Definition warvar := smallvar + array.
Definition warvars := list warvar.

Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp)
| asgn_ar (y : el) (e': exp) (*where y has the form a[[e]],
                      pretty sure I'm not allowed to write it like that
                      in here
                     *)
| checkpoint (omega: warvars)
| reboot.


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

(***)

Close Scope type_scope.
