Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Import ListNotations.
From Semantics Require Export semantics.
Open Scope list_scope.
(*relation determining what variables are read when evaluating exp e
 *)
(*N, V are dummy values*)
Inductive rd: exp -> readobs -> Prop :=
    RD (e: exp) (N: nvmem) (V: vmem) (rs: readobs) (v: value):
    eeval N V e rs v -> rd e rs.

Check samearray_b.

(*checks if w was recorded as read in R*)
Fixpoint isread_b (w: warvar) (R: readobs):=
  match R with
   nil => false
  | (r::rs) => (match r with
               (location, _) => (*get the location r has recorded reading from*)
               (match w with
                 inl xw => (*w is a smallvar*)
                 (
                   orb (eqb_loc (inl xw) location (*w can thus be treated as location*)) (isread_b w rs)
                 )
               | inr a => (*w is an array*)
                     (match location with
                       inr el => orb (samearray_b el a) (isread_b w rs)
                     (*r is a memory location in an array; check if it is same array as w*)
                     | inl _ => (isread_b w rs) (*r is not a memory loc in an array*)
                    end)
                 end) end)
  end.

Definition isread (w: warvar) (R: readobs) := is_true( isread_b w R).

Inductive warcheck: nvmem -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop := 
  WAR_Skip: forall(N: nvmem) (W: warvars) (R: warvars),
    warcheck N W R skip W R
| WAR_NoRd: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not(isread x (R ++ Re)) (*define me!*)
             -> warcheck N W R (asgn_sv x e) ((inl x)::W) R.


    (N: nvmem) (W: list loc) (R: list loc) (l: instruction) (W': loc_set) (R': loc_set):=

