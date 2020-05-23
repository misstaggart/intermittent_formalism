Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
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
(*what is the star*)
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
Close Scope string_scope.
(***)


(*Now, to business! Below is syntax*)
Open Scope type_scope.

Inductive boptype :=
  Plus
| Sub
| Mult
| Div
| Mod
| Or
| And.

(*shortcut!*)
Inductive value :=
    Nat (n: nat)
  | Bool (b: bool)
  | error. 
Coercion Bool : bool >-> value.
Coercion Nat : nat >-> value.

(*evaluation rules for binary operations*)

Fixpoint bopeval (bop: boptype) (v1 v2 :value): (value) :=
  match bop with
   Plus => 
    (
      match v1, v2 with
        (Nat n1), (Nat n2) => Nat (add n1 n2)
        | _, _ => error
        end
    )
  | Sub => 
    (
      match v1, v2 with
       (Nat n1), (Nat n2) => Nat (n1 - n2)
        | _, _ => error
        end
    )
  | Mult => 
    (
      match v1, v2 with
       (Nat n1), (Nat n2) => Nat (mul n1 n2)
        | _, _ => error
        end
    )
  | Div =>
    (
      match v1, v2 with
       (Nat n1), (Nat n2) =>
                    ( if (n2 == 0) then error
                      else Nat (n1 / n2))
        | _, _ => error
        end
    )
  | Mod =>
    (
      match v1, v2 with
       (Nat n1), (Nat n2) =>
                    ( if (n2 == 0) then error
                     else Nat (n1 mod n2))
        | _, _ => error
        end
    )
  | Or =>
  (
      match v1, v2 with
        (Bool b1), (Bool b2) => Bool (orb b1 b2)
        | _, _ => error
        end
    )
  | And =>
  (
      match v1, v2 with
        (Bool b1), (Bool b2) => Bool (andb b1 b2)
        | _, _ => error
        end
  )
  end.

Definition isvaluable (v: value) :=
  match v with
    error => False
  | _ => True
  end.

Definition isvalidbop (bop: boptype) (v1 v2 : value) :=
  match (bopeval bop v1 v2) with
    error => False
  | _ => True
   end.

(*setting up equality type for value*)
(*whether or not things are valuable is actually covered in eqb_value*)
Definition eqb_value (x y: value) :=
  match x, y with
    Nat nx, Nat ny => nx == ny
  | Bool bx, Bool byy => eqb bx byy
  | _, _ => false
  end.
Definition eq_value (x y: value) := is_true(eqb_value x y).

(*shouldn't need this*)
Definition eq_valueop (x y : option value) :=
  match x, y with
    Error, None => True
  | Some x1, Some y1 => eq_value x1 y1
  | _, _ => False
  end.

(*memory maps*)
Definition map (A: Type) (eqba: A -> A -> bool):= A -> value.
Definition emptymap A eqba :(map A eqba) := (fun _ => error).
Definition updatemap {A} {eqba} (m: map A eqba) (i: A) (v: value) : map A eqba := (fun j =>
                                                               if (eqba j i) then v
                                                               else (m j)).

Definition unionmaps {A} {eqba} (m1: map A eqba) (m2: map A eqba): map A eqba :=
  (fun j =>
     match m1 j with
     error => m2 j
     | _ => m1 j
     end
  ).
Notation "m1 'U' m2" := (unionmaps m1 m2) (at level 100).
Notation "i '|->' v ';' m" := (updatemap m i v)
  (at level 100, v at next level, right associativity).

Definition indomain {A} {eqba} (m: map A eqba) (x: A) :=
  match m x with
    error => False
  | _ => True
  end.
(******************************************************************************************)

(*******************************more syntax**********************************************)
Inductive array :=
  Array (s: string) (l: nat).

Inductive location :=
  nonvol
 | vol.

Inductive exp :=
  Var (s: string) (l: location) 
| Val (v: value)
| Bop (bop: boptype) (e1: exp) (e2: exp) 
| El (a: array) (e: exp).
Coercion Val : value >-> exp.
Notation "a '[[' e ']]'" := (El (a) (e))
                            (at level 100, right associativity).

(*used subtypes to enforce the fact that only some expressions are
 memory locations*)
(*also made the write after read type easier*)
Definition smallvarpred := (fun x=> match x with
                                        Var _ _ => true
                                        | _ => false
                                 end).
Definition elpred  := (fun x=> match x with
                                        El (Array _ length) (Val (Nat i)) => (i <? length)
                                        | _ => false
                                 end).
(*note elpred checks if index is a natural in bounds*)
Notation smallvar := {x: exp | smallvarpred x}.
(*how does this work??*)
Notation el := {x: exp| elpred x}.
Definition loc := smallvar + el. (*memory location type*)

Definition warvar := smallvar + array. (*write after read variable type*)
Definition warvars := list warvar.
(*Coercion (inl smallvar el): smallvar >-> loc.*)
(*Coercion inl: smallvar >-> loc.*)

(**helper functions for expressions*)
Definition isarrayindex (e: el) (a: array) (vindex: value) := (*transitions from el type
                                                          to a[i] representation*)
  match (vindex) with
    Nat i =>
  (match (val e) with
     El a (Nat i)  => True
   | _ => False end) (*know that i is within the bounds by elpred*)
  | _ => False
  end.
Definition isNV_b (x: smallvar) :=
  match (val x) with
    Var _ nonvol => true
  | _ => false
  end.

Definition isV_b (x: smallvar) :=
  match (val x) with
    Var _ vol => true
  | _ => false
  end.

Definition isNV x := is_true(isNV_b x).

Definition isV x := is_true(isV_b x).

Definition sameloc_b (x y: smallvar) :=
  match isNV_b(x), isNV_b(y) with
    true, true => true
  | false, false => true
  | _, _ => false
  end.

(*****)

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
| Seqcom (l: instruction) (c: command) (*added suffix to distinguish from Seq ceval
                                         constructor*)
| ite (e: exp) (c1: command) (c2: command).

Notation "l ';;' c" := (Seqcom l c)
                         (at level 100).

Notation "'TEST' e 'THEN' c1 'ELSE' c2 " := (ite e c1 c2)
                                                (at level 100).
(*******************************************************************)

(******setting up location equality relation for memory maps******************)
Program Definition getstringsv (x: smallvar): string :=
  match val x with
    Var s _ => s
  | _ => !
  end. 
Next Obligation.
    destruct x as [s| | |];
      try (simpl in H0; discriminate H0). apply (H s l). reflexivity.
Qed.

Program Definition getarrayel (x: el): string :=
  match val x with
    El (Array s _) _ => s
  | _ => !
  end.
Next Obligation. destruct (x) as [s| | |];
                 try (simpl in H0; discriminate H0).
    destruct a eqn: adestruct. apply (H s l e). reflexivity.
Qed.


Program Definition getindexel (x: el): value  :=
  match val x with
    El _ (Val v) => v
  | _ => !
  end.
Next Obligation. destruct (x) as [s| | |];
                 try (simpl in H0; discriminate H0).
                 destruct a eqn: adestruct.
                 destruct e;
                 try (simpl in H0; discriminate H0).
                 apply (H a v). subst. reflexivity.
Qed.

Definition eqb_loc (l1: loc) (l2: loc) :=
  match l1, l2 with
    inl _, inr _ => false
  | inr _, inl _ => false
  | inl x, inl y => andb ((getstringsv x)==(getstringsv y)) (sameloc_b x y)
  | inr x, inr y => andb ((getarrayel x)==(getarrayel y))
                       (eqb_value (getindexel x) (getindexel y))
  end. (*might be nice to have values as an equality type here*)
(****************************************************************)

(****************************memory syntax*************************************)

(*memory locations defined above warvars*)
Notation mem := (map loc eqb_loc). (*memory mapping*)

Inductive nvmem := (*nonvolatile memory*)
  NonVol (m : mem).

Inductive vmem := (*volatile memory*)
  Vol (m : mem).


Definition reset (V: vmem) := Vol (emptymap loc eqb_loc).

Inductive cconf := (*continuous configuration*)
  ContinuousConf (triple: nvmem * vmem * command).

Inductive context :=
  Con (triple: nvmem * vmem * command).

Inductive iconf := (*intermittent configuration*)
  IntermittentConf (qple: context * nvmem * vmem * command).

Definition ro := loc * value. (*read observation*)
Definition readobs := list ro.

Notation NoObs := ([]: readobs).

Inductive obs := (*observation*)
  Obs (r: readobs)
| reboot
| checkpoint.
Coercion Obs : readobs >-> obs.

Notation obsseq := (list obs). (*observation sequence*)
(***************************************************************)

(****************continuous operational semantics***********************)

(**why don't these work?**)
(*would be really nice if I could have these so the constructors
 for eeval could have consistent arguments wrt nvmem vs mem and similar*)


(*I could change these to enforce that they only take in smallvars
 of the correct type but it's already checked in my evaluation rules*)
Coercion NonVol : mem >-> nvmem.
Coercion Vol : mem >-> vmem.
(****)
(*veval should return one of the primitive values*)
Inductive eeval: nvmem -> vmem -> exp -> readobs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value),
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N V v NoObs v
| BINOP: forall(N: nvmem) (V: vmem)
          (e1: exp) (e2: exp)
          (r1: readobs) (r2: readobs)
          (v1: value) (v2: value) (bop: boptype),
    eeval N V e1 r1 v1 ->
    eeval N V e2 r2 v2 -> 
    (isvalidbop bop v1 v2) -> (*extra premise to check if v1, v2, bop v1 v2 valuable*)
    eeval N V (Bop bop e1 e2) (r1++ r2) (bopeval bop v1 v2)
| RD_VAR_NV: forall(mapN: mem) (mapV: mem) (x: smallvar) (v: value),
    eq_value (mapN (inl x)) v ->
    isNV(x) -> (*extra premise to make sure x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval (NonVol mapN) (Vol mapV) (val x) [((inl x), v)] v
| RD_VAR_V: forall(mapN: mem) (mapV: mem) (x: smallvar) (v: value),
    eq_value (mapV (inl x)) v ->
    isV(x) -> (*extra premise to make sure x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval (NonVol mapN) (Vol mapV) (val x) [((inl x), v)] v
| RD_ARR: forall(mapN: mem) (mapV: mem)
           (a: array)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (element: el)
           (v: value),
    eeval (NonVol mapN) (Vol mapV) (index) rindex vindex ->
    eq_value ((mapN U mapV) (inr element)) v ->
    (isarrayindex element a vindex) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval (NonVol mapN) (Vol mapV) (a[[index]]) (rindex++[((inr element), v)]) v
.
(*ask Arthur why this notation doesn't work *)

(*Reserved Notation "'{'N V'}=[' e ']=> <'r'>' v" (at level 40).
Inductive eevaltest: nvmem -> vmem -> exp -> obs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value), 
    {N V} =[ v ]=> <reboot> v
  where "{N V}=[ e ]=> <r> v" := (eevaltest N V e r v).*)

(****************************************************************************)

(**********continuous execution semantics*************************)

Coercion Instruct : instruction >-> command.

Inductive cceval: nvmem -> vmem -> command -> obsseq -> nvmem -> vmem -> command -> Prop :=
  NV_Assign: forall(x: smallvar) (mapN: mem) (V: vmem) (e: exp) (r: readobs) (v: value),
    indomain mapN (inl x) ->
    eeval (NonVol mapN) V e r v ->
    isNV(x) -> (*extra premise to make sure x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval (NonVol mapN) V (asgn_sv x e) [Obs r]
           (NonVol ( (inl x) |-> v; mapN)) V skip
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    indomain mapV (inl x) ->
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*extra premise to make sure x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval N (Vol mapV) (asgn_sv x e) [Obs r] N (Vol ((inl x) |-> v ; mapV)) skip
| Assign_Arr: forall (mapN: mem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval (NonVol mapN) (V) (ei) ri vi ->
    eeval (NonVol mapN) (V) (e) r v ->
    (isarrayindex element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval (NonVol mapN) (V) (asgn_ar a ei e) [Obs (ri++r)]
           (NonVol ( (inr element)|-> v; mapN)) V skip
    (*valuability and inboundedness of vindex are checked in isarrayindex*)
| CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
               cceval N V ((incheckpoint w);; c) [checkpoint]
               N V c
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval N V (skip;;c) [Obs NoObs] N V c
| Seq: forall (N: nvmem)
         (N': nvmem)
         (V: vmem)
         (V': vmem)
         (l: instruction)
         (c: command)
         (o: obs),
    cceval N V l [o] N' V' skip ->
    cceval N V (l;;c) [o] N' V' c
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r true -> 
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c1
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r false ->
    cceval N V (TEST e THEN c1 ELSE c2) [Obs r] N V c2.
(*if you can't
get the coercisons to work make two functions to update the nonvol and vol maps
instead of typing the
 constructors every time*)

Inductive iceval: context-> nvmem -> vmem -> command -> obs -> context -> nvmem -> vmem -> command -> Prop :=
  CP-PowerFail: forall(k: context) (N: nvmem) (V: vmem) (c: command)
                 iceval k N V c
                        NoObs
                        k N (*empty map*) inreboot
|  NV_Assign: forall(x: smallvar) (mapN: mem) (V: vmem) (e: exp) (r: readobs) (v: value),
    indomain mapN (inl x) ->
    eeval (NonVol mapN) V e r v ->
    cceval (NonVol mapN) V (asgn_sv x e) r (NonVol ( (inl x) |-> v ; mapN)) V skip
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    indomain mapV (inl x) ->
    eeval N (Vol mapV) e r v ->
    cceval N (Vol mapV) (asgn_sv x e) r N (Vol ((inl x) |-> v ; mapV)) skip
| Assign_Arr: forall (mapN: mem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval (NonVol mapN) (V) (ei) ri vi ->
    eeval (NonVol mapN) (V) (e) r v ->
    (isarrayindex element a vi) -> (*extra premise to check that element is actually a[vi] *)
    cceval (NonVol mapN) (V) (asgn_ar a ei e) (Seqrd ri r)
           (NonVol ( (inr element)|-> v; mapN)) V skip
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
