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
Definition map (A: eqType):= A -> value.
Definition emptymap {A: eqType} :map A := (fun _ => Error).
Definition updatemap {A: eqType} (m: map A) (i: A) (v: value) : map A := (fun j =>
                                                               if (j == i) then v
                                                               else (m j)).
Close Scope string_scope.
(*map nat will be for arrays and map string will be for memory*)
(*except you don't actually need to get stuff out of the
 arrays but I'll leave the equality types for now just in case*)
(*also memory maps locations to values so....*)
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

Check smallvar.
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

(*memory syntax*)
(*memory locations defined above warvars*)

(*setting up equality type for locations*)
(*should the memory map check to see if the expression is actually
 a natural somehow
 i'd have to add some details keeping track of the return type
 of the binary operations*)

Print sum.


(*there must be an easier way of doing this involving ssreflect*)
Check subType.
Check is_true.

Check Sub.

Lemma whatissmallvar: forall(s: string), (is_true (smallvarpred (Var s))).
Proof.
  intros. reflexivity.
Qed.

Check (whatissmallvar "f").

Check valP (Sub (Var "f") (whatissmallvar "f")).

(*what is the difference between sub_sort and subType?
...I think sub_sort is the thing where the actual values
are?
but then what's the point of the subType function?
 *)

(*Lemma whatisnotsv: forall(e: exp)(not (is_true (match e )))*)

(*this is hacky but idk what to do abt it*)
Check insub. (*NICE*)
Check insub.
Definition getstring (x: smallvar) :=
   match val x with
    Var sx => sx
  | _  => "problem"%string
              end.

Definition eqb_loc (l1: loc) (l2: loc) :=
  match l1, l2 with
    inl _, inr _ => false
  | inr _, inl _ => false
  | inl x, inl y =>
    (*bassically I want to do inversion here
      and then intros S
     *)
    eqb_string (getstring x) (getstring y)
  | inr x, inr y => true
  end.

Lemma eqloc: Equality.axiom eqb_loc.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_string x y) eqn:beq.
  - constructor. apply eqb_string_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_string_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical string_eqMixin := EqMixin eqstring.
Canonical string_eqtype := Eval hnf in EqType string string_eqMixin.


Close Scope type_scope.
