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

(*m1 is checked first, then m2*)
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

Definition eqb_array (a1 a2: array) :=
  match a1, a2 with
    Array s1 l1, Array s2 l2 => andb (s1 == s2) (l1 == l2)
    end.

Inductive volatility :=
  nonvol
 | vol.

Inductive exp :=
  Var (s: string) (q: volatility) 
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

(**smallvar, el, and warvar helper functions*)
(**no need to work directly with the subtypes or sumtypes, just use these**)

Definition sameindex (e: el) (a: array) (vindex: value) := (*transitions from el type
                                                          to a[i] representation*)
  match (vindex) with
    Nat i =>
  (match (val e) with
     El a (Nat i)  => True
   | _ => False end) (*know that i is within the bounds by elpred*)
  | _ => False
  end.

Definition samearray_b (element: el) (a: array) := (*checks if el indexes into a*)
  match (val element) with
    El element_arr _ =>
    eqb_array element_arr a (*know that el's index is within bounds of a by elpred*)
  | _ => false
  end.

Definition samearray (element: el) (a: array) := is_true(samearray_b element a).

Definition isNV_b (x: smallvar) := (*checks if x is stored in nonvolatile memory*)
  match (val x) with
    Var _ nonvol => true
  | _ => false
  end.

Definition isV_b (x: smallvar) :=(*checks if x is stored in volatile memory*)
  match (val x) with
    Var _ vol => true
  | _ => false
  end.

Definition isNV x := is_true(isNV_b x). (*prop version of isNV_b*)

Definition isV x := is_true(isV_b x). (*prop version of isV_b*)

Definition samevolatility_b (x y: smallvar) := (*used for defining equality of memory locations*)
  match isNV_b(x), isNV_b(y) with
    true, true => true
  | false, false => true
  | _, _ => false
  end.

(*****)

Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp) (*could distinguish between NV and V assignments as well here*)
| asgn_arr (a: array) (i: exp) (e: exp) (*i is index, e is new value of a[i]*)
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
Coercion Instruct : instruction >-> command.
(*******************************************************************)

(******setting up location equality relation for memory maps******************)
Program Definition getstringsv (x: smallvar): string :=
  match val x with
    Var s _ => s
  | _ => !
  end. 
Next Obligation.
    destruct x as [s| | |];
      try (simpl in H0; discriminate H0). apply (H s q). reflexivity.
Qed.

Definition eqb_smallvar (x y: smallvar): bool :=
  andb ((getstringsv x)==(getstringsv y)) (samevolatility_b x y).


Program Definition getarray (x: el): array :=
  match val x with
    El (arr) _ => arr
  | _ => !
  end.
Next Obligation. destruct (x) as [s| | |];
                 try (simpl in H0; discriminate H0).
     apply (H a e). reflexivity.
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
    inl x, inl y => eqb_smallvar x y
  | inr x, inr y => andb (eqb_array (getarray x) (getarray y))
                        (eqb_value (getindexel x) (getindexel y))
  | _, _ => false 
  end. (*might be nice to have values as an equality type here*)

(*move me to a logical location*)
(*start here*)
(*convert loc to warvar*)
Fixpoint loc_warvars (l: loc) : warvar := 
  match l with
    inl x => inl x
  | inr el => inr (getarray el)
  end.
(****************************************************************)

(****************************memory*************************************)

(*memory locations defined above warvars*)
Notation mem := (map loc eqb_loc). (*memory mapping*)

Inductive nvmem := (*nonvolatile memory*)
  NonVol (m : mem) (D: warvars). (*extra argument to keep track of domain because
                                  I reuse this type for checkpoint map*)

Inductive vmem := (*volatile memory*)
  Vol (m : mem).

(**why don't these coercions work?**)
(*would be really nice if I could have these so the constructors
 for eeval could have consistent arguments wrt nvmem vs mem and similar*)
(*I could change these to enforce that they only take in smallvars
 of the correct type but it's already checked in my evaluation rules*)
Coercion Vol : mem >-> vmem.
(**************************helpers for the memory maps*********************************************)
  Definition getvalue (N: nvmem) (i: loc) :=
  match N with NonVol m D => m i end.
  Notation "v '<-' N" := (getvalue N v)
    (at level 40).

  (*updates domain and mapping function*)
Definition updateNV (N: nvmem) (i: loc) (v: value) :=
  match N with NonVol m D =>
               NonVol (updatemap m i v) (
                        match i with 
                          inl x => ((inl x) :: D) (*i is a smallvar*)
                         | inr el => ((inr (getarray el))::D) (*i is an array element*)
                        end
                      )
  end.

(*used to update NV memory with checkpoint*)
Definition updatemaps (N: nvmem) (N': nvmem): nvmem :=
  match N, N' with
    NonVol m D, NonVol m' D' => NonVol
  (fun j =>
     match m j with
     error => m' j
     | _ => m j
     end
  )
  (D' ++ D) (*shocking inclusion of duplicates*)
  end.
Notation "m1 'U!' m2" := (updatemaps m1 m2) (at level 100).
Definition reset (V: vmem) := Vol (emptymap loc eqb_loc).

Definition eqb_warvar (w1 w2: warvar) :=
  match w1, w2 with
               inl x, inl y => eqb_smallvar x y
             | inr x, inr y => eqb_array x y
             | _, _ => false
  end.

Definition eq_warvar (w1 w2: warvar) :=
  is_true (eqb_warvar w1 w2).

(*checks if w was recorded as read/written to in warvar list W*)
Fixpoint memberwv_wv_b (input: warvar) (w: warvars) :=
  match w with
    [] => false
  | wv::wvs => orb (eqb_warvar input wv) (memberwv_wv_b input wvs) 
end.
Definition memberwv_wv (w: warvar) (W: warvars) := is_true(memberwv_wv_b w W).

(*checks if a location input has been stored as a WAR location in w*)
Definition memberloc_wv (input: loc) (w: warvars) :=
  memberwv_wv_b (loc_warvars input) w.

(*restricts memory map m to domain w*)
(*doesn't actually clean the unnecessary variables out of m*)
Definition restrict (N: nvmem) (w: warvars): nvmem :=
  match N with NonVol m D => NonVol
    (fun input => if (memberloc_wv input w) then m input else error) w (*in predicate for lists
                                                                 wouldn't work bc warvar                                                                  is not an equality type...unless you want it to be*)
  end.

Notation "N '|!' w" := (restrict N w) 
  (at level 40, left associativity).

(*prop determining if every location in array a is in the domain of m*)
Definition indomain_nvm (N: nvmem) (w: warvar) :=
  match N with NonVol m D => memberwv_wv_b w D end.

(*start here put me somewhere reasonable*)
Fixpoint eq_lists {A: Type} (L1: list A) (L2: list A) (eq: A -> A -> Prop) :=
        match L1, L2 with
          nil, nil => True
        | (w::ws), (d::ds) => (eq w d) /\ (eq_lists ws ds eq)
        | _ , _ => False end.

Definition isdomain_nvm (N: nvmem) (w: warvars) := (*no zip library function?*)
  match N with NonVol m D => eq_lists D w eq_warvar end.

(********************************************)
Inductive cconf := (*continuous configuration*)
  ContinuousConf (triple: nvmem * vmem * command).

Notation context := (nvmem * vmem * command). 

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
Close Scope type_scope.

Open Scope list_scope.
(*converts from list of read locations to list of
WAR variables
 *)
Fixpoint readobs_warvars (R: readobs) : warvars := 
  match R with
    nil => nil
| (r::rs) => match r with
              (location, _) => (*get the location r has recorded reading from*)
              (match location with
                inl x => (inl x)::(readobs_warvars rs) (*location is a smallvar*)
              | inr el => (inr (getarray el))::(readobs_warvars rs)
              end)
           end
  end.
(***************************************************************)

(****************continuous operational semantics***********************)
(*evaluation relation for expressions*)
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
| RD_VAR_NV: forall(N: nvmem) (mapV: vmem) (x: smallvar) (v: value),
    eq_value ((inl x) <-N) v ->
    isNV(x) -> (*extra premise to make sure x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N mapV (val x) [((inl x), v)] v
| RD_VAR_V: forall(N: nvmem) (mapV: mem) (x: smallvar) (v: value),
    eq_value (mapV (inl x)) v ->
    isV(x) -> (*extra premise to make sure x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N (Vol mapV) (val x) [((inl x), v)] v
| RD_ARR: forall(N: nvmem) (V: vmem)
           (a: array)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (element: el)
           (v: value),
    eeval N V (index) rindex vindex ->
    eq_value ((inr element) <-N) v ->
    (sameindex element a vindex) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N V (a[[index]]) (rindex++[((inr element), v)]) v
.
(*ask Arthur why this notation doesn't work *)

(*Reserved Notation "'{'N V'}=[' e ']=> <'r'>' v" (at level 40).
Inductive eevaltest: nvmem -> vmem -> exp -> obs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value), 
    {N V} =[ v ]=> <reboot> v
  where "{N V}=[ e ]=> <r> v" := (eevaltest N V e r v).*)

(****************************************************************************)

(**********continuous execution semantics*************************)


(*evaluation relation for commands*)
(*UPDATE DOMAIN WHEN YOU WRITE*)
Inductive cceval: nvmem -> vmem -> command -> obsseq -> nvmem -> vmem -> command -> Prop :=
  NV_Assign: forall(x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval N V (asgn_sv x e) [Obs r]
           (updateNV N (inl x) v) V skip
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval N (Vol mapV) (asgn_sv x e) [Obs r] N (Vol ((inl x) |-> v ; mapV)) skip
| Assign_Arr: forall (N: nvmem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (sameindex element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval N V (asgn_arr a ei e) [Obs (ri++r)]
           (updateNV N (inr element) v) V skip
    (*valuability and inboundedness of vindex are checked in sameindex*)
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
(*if I can't
get the coercisons to work I could make two functions to update the nonvol and vol maps
instead of typing the
 constructors every time*)

(************************************************************)

(**********intermittent execution semantics*************************)
(*evaluation relation for commands*)
Inductive iceval: context-> nvmem -> vmem -> command -> obsseq -> context -> nvmem -> vmem -> command -> Prop :=
  CP_PowerFail: forall(k: context) (N: nvmem) (V: vmem) (c: command),
                 iceval k N V c
                        [Obs NoObs]
                        k N (reset V) inreboot
 | CP_CheckPoint: forall(k: context) (N: nvmem) (V: vmem) (c: command) (w: warvars),
                 iceval k N V ((incheckpoint w);;c)
                        [checkpoint]
                        ((N |! w), V, c) N V c (*where presumably N |! w is checkpoint*)
 | CP_Reboot: forall(N: nvmem) (N': nvmem)(*see below*) (*N is the checkpointed one*)
               (V: vmem) (V': vmem)
               (c: command), 
     iceval (N, V, c) N' V' inreboot
            [reboot]
            (N, V, c) (N U! N') V c
 | CP_NV_Assign: forall(k: context) (x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval k N V (asgn_sv x e)
           [Obs r]
           k (updateNV N (inl x) v) V skip
| CP_V_Assign: forall(k: context) (x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval k N (Vol mapV) (asgn_sv x e)
           [Obs r]
           k N (Vol ((inl x) |-> v ; mapV)) skip
| CP_Assign_Arr: forall (k: context) (N: nvmem) (V: vmem)
               (a: array)
               (ei: exp)
               (ri: readobs)
               (vi: value)
               (e: exp)
               (r: readobs)
               (v: value)
               (element: el),
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (sameindex element a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval k N V (asgn_arr a ei e)
           [Obs (ri++r)]
           k (updateNV N (inr element) v) V skip
| CP_Skip: forall(k: context) (N: nvmem)
         (V: vmem)
         (c: command),
    iceval k N V (skip;;c) [Obs NoObs] k N V c
|CP_Seq: forall (k: context)
         (N: nvmem) (N': nvmem)
         (V: vmem) (V': vmem)
         (l: instruction)
         (c: command)
         (o: obs),
    iceval k N V l [o] k N' V' skip ->
    iceval k N V (l;;c) [o] k N' V' c
|CP_If_T: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r true -> 
    iceval k N V (TEST e THEN c1 ELSE c2) [Obs r] k N V c1
|CP_If_F: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1: command)
         (c2: command),
    eeval N V e r false ->
    iceval k N V (TEST e THEN c1 ELSE c2) [Obs r] k N V c2.
(*CP_Reboot: I took out the equals premise and instead built it
into the types because I didn't want to define a context equality function*)

Close Scope list_scope.
