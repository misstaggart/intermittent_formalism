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
(***)


(*Now, to business! Below is syntax*)

Inductive value :=
    Nat (n: nat)
| Bool (b: bool)
| vBop (v1: value) (v2: value).
Coercion Bool : bool >-> value.
Notation "'{{' v1 '**' v2 '}}'" := (vBop v1 v2) (at level 100).

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

(*memory maps*)
Definition map (A: Type) (eqba: A -> A -> bool):= A -> (option value).
Definition emptymap {A} {eqba} :(map A eqba) := (fun _ => None).
Definition updatemap {A} {eqba} (m: map A eqba) (i: A) (v: value) : map A eqba := (fun j =>
                                                               if (eqba j i) then Some v
                                                               else (m j)).

Definition unionmaps {A} {eqba} (m1: map A eqba) (m2: map A eqba): map A eqba :=
  (fun j =>
     match m1 j with
       Some out => Some out
     | None => m2 j
     end
  ).
Notation "m1 'U' m2" := (unionmaps m1 m2) (at level 100).
Notation "i '|->' v ';' m" := (updatemap m i v)
  (at level 100, v at next level, right associativity).

Definition indomain {A} {eqba} (m: map A eqba) (x: A) :=
  match m x with
    Some _ => True
  | None => False
  end.
Close Scope string_scope.
(******************************************************************************************)

(*******************************more syntax**********************************************)
Inductive array :=
  Array (s: string) (l: nat).

Open Scope type_scope.
Inductive exp :=
  Var (s: string) 
| Val (v: value)
| Bop (e1: exp) (e2: exp)
| El (a: array) (e: exp).
Coercion Val : value >-> exp.
Notation "a '[[' e ']]'" := (El (a) (e))
                            (at level 100, right associativity).

Notation "e1 '**' e2" := (Bop e1 e2) (at level 100).
(*used subtypes to enforce the fact that only some expressions are
 memory locations*)
(*also made the write after read type easier*)
Definition smallvarpred := (fun x=> match x with
                                        Var _ => true
                                        | _ => false
                                 end).
Definition elpred  := (fun x=> match x with
                                        El _ (Val _) => true
                                        | _ => false
                                 end).

Notation smallvar := {x: exp | smallvarpred x}.
(*how does this work??*)
Notation el := {x: exp| elpred x}.
Definition loc := smallvar + el. (*memory location type*)

Definition warvar := smallvar + array. (*write after read variable type*)
Definition warvars := list warvar.
(*Coercion (inl smallvar el): smallvar >-> loc.*)
(*Coercion inl: smallvar >-> loc.*)

Definition isarrayindex (e: el) (a: array) (i: value) := (*transitions from el type
                                                          to a[i] representation*)
  match (val e) with
    El a i  => True
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
| Seqcom (l: instruction) (c: command) (*added suffix to distinguish from Seq ceval
                                         constructor*)
| ite (e: exp) (c1: command) (c2: command).

Notation "l ';;' c" := (Seqcom l c)
                         (at level 100).

Notation "'TEST' e 'THEN' c1 'ELSE' c2 " := (ite e c1 c2)
                                                (at level 100).
(*******************************************************************)

(******setting up location equality relation for memory maps******************)
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

Program Definition getstringsv (x: smallvar): string :=
  match (getstringsv1 x) with 
    Some s => s
   | None => !
   end. 
Next Obligation. apply (sv1notnone (exist
       (fun
        x : exp
        =>
        smallvarpred
        x) x
       H)). symmetry. apply Heq_anonymous.
Qed.

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

(*fix this using the program module*)
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
(****************************************************************)

(****************************memory syntax*************************************)

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

Inductive iconf := (*intermittent configuration*)
  IntermittentConf (qple: context * nvmem * vmem * command).

Inductive readobs := (*read observation*)
  NoObs (*moved the empty observation here to make eeval easier*)
| rd (l: loc) (v: value)
| Seqrd (r1: readobs) (r2: readobs).

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
Coercion NonVol : mem >-> nvmem.
Coercion Vol : mem >-> vmem.
(****)

Inductive eeval: nvmem -> vmem -> exp -> readobs -> value -> Prop :=
VAL: forall(N: nvmem) (V: vmem) (v: value), 
    eeval N V v NoObs v
| BINOP: forall(N: nvmem) (V: vmem)
          (e1: exp) (e2: exp)
          (r1: readobs) (r2: readobs)
          (v1: value) (v2: value),
    eeval N V e1 r1 v1 ->
    eeval N V e2 r2 v2 ->
    eeval N V (e1 ** e2) (Seqrd r1 r2) (vBop v1 v2)
    (*eeval N V (e1 ** e2) (Seqrd r1 r2) {{ v1 ** v2 }}*)
| RD_VAR: forall(mapN: mem) (mapV: mem) (x: smallvar) (v: value),
    eq_valueop ((mapN U mapV) (inl x)) (Some v) ->
    eeval (NonVol mapN) (Vol mapV) (val x) (rd (inl x) v) v
| RD_ARR: forall(mapN: mem) (mapV: mem)
           (a: array)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (element: el)
           (v: value),
    eeval (NonVol mapN) (Vol mapV) (index) rindex vindex ->
    eq_valueop ((mapN U mapV) (inr element)) (Some v) ->
    (isarrayindex element a vindex) -> (*extra premise to check that inr element is actually a[vindex] *)
    eeval (NonVol mapN) (Vol mapV) (a[[index]]) (Seqrd rindex (rd (inr element) v) ) v
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
Inductive cceval: nvmem -> vmem -> command -> obs -> nvmem -> vmem -> command -> Prop :=
  NV_Assign: forall(x: smallvar) (mapN: mem) (V: vmem) (e: exp) (r: readobs) (v: value),
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
(*if you can't
get the coercisons to work make two functions to update the nonvol and vol maps
instead of typing the
 constructors every time*)
(*Inductive iceval: context-> nvmem -> vmem -> command -> obs -> context -> nvmem -> vmem -> command -> Prop :=
  NV_Assign: forall(x: smallvar) (mapN: mem) (V: vmem) (e: exp) (r: readobs) (v: value),
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
    cceval N V (TEST e THEN c1 ELSE c2) r N V c2. *)
Close Scope type_scope.
