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
Inductive rd: exp -> warvars -> Prop :=
    RD (e: exp) (N: nvmem) (V: vmem) (rs: readobs) (v: value):
      eeval N V e rs v -> rd e (readobs_warvars rs).

(*checks if w was recorded as read/written to in warvar list W*)
Fixpoint isin_wv_b (w: warvar) (W: warvars):=
  match W with
   nil => false
  | (r::rs) => match w, r with
               inl wx, inl rx => orb (eqb_loc (inl wx) (inl rx)) (isin_wv_b w rs)
             | inr wa, inr ra => orb (eqarray_b wa ra) (isin_wv_b w rs)
             | _, _ => isin_wv_b w rs
             end
end.


Definition isin_wv (w: warvar) (W: warvars) := is_true(isin_wv_b w W).

Inductive warcheck: nvmem -> warvars -> warvars -> instruction -> warvars -> warvars -> Prop := 
  WAR_Skip: forall(N: nvmem) (W: warvars) (R: warvars),
    warcheck N W R skip W R
| WAR_NoRd: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             not(isin_wv (inl x) (R ++ Re)) 
             -> warcheck N W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_Checkpointed: forall(mapN: mem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isin_wv (inl x) (R ++ Re) ->
             not(isin_wv (inl x) W) ->
             (indomain mapN (inl x)) ->
             warcheck (NonVol mapN) W R (asgn_sv x e) ((inl x)::W) (R ++ Re)
| WAR_WT: forall(N: nvmem) (W: warvars) (R: warvars)
             (x: smallvar) (e: exp)
             (Re: warvars),
             (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
             isin_wv (inl x) (R ++ Re) ->
             (isin_wv (inl x) W) ->
             warcheck N W R (asgn_sv x e) W (R ++ Re)
| WAR_NoRd_Arr: forall(N: nvmem) (W: warvars) (R: warvars)
                 (a: array) (index: exp) (Rindex: warvars)
                 (e: exp) (Re: warvars),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    not(isin_wv (inr a) (R ++ Re ++ Rindex)) ->
    warcheck N W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
| WAR_Checkpointed_Arr: forall(mapN: mem) (W: warvars) (R: warvars)
                 (a: array) (index: exp) (Rindex: warvars)
                 (e: exp) (Re: warvars),
    (rd e Re) -> (*extra premise checking that Re is the list of values read when e is evaluated*)
    (rd index Rindex) -> (*extra premise checking that Rindex is the list of values read when index is evaluated*)
    (isin_wv (inr a) (R ++ Re ++ Rindex)) ->
    (indomain_arr mapN a) ->
    warcheck (NonVol mapN) W R (asgn_arr a index e) ((inr a)::W) (R ++ Re ++ Rindex)
.


    (N: nvmem) (W: list loc) (R: list loc) (l: instruction) (W': loc_set) (R': loc_set):=

