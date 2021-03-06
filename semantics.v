Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Program Sumbool
     Ascii String Logic.ProofIrrelevance.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool eqtype fintype seq
     choice bigop finset generic_quotient tuple path.
From Coq_intermittent Require Import lemmas_0.

From deriving Require Import deriving.


(*To business! Below is the DSL embedding and ssreflect infrastructure*)
Open Scope type_scope.

Inductive boptype :=
  Plus
| Sub
| Mult
| Div
| Mod
| Or
| And.

Inductive value :=
    Nat (n: nat)
  | Bool (b: bool)
  | error. 
Coercion Bool : bool >-> value.
Coercion Nat : nat >-> value.

Definition eqb_value (x y: value) :=
  match x, y with
    Nat nx, Nat ny => nx == ny
  | Bool bx, Bool byy => bx == byy
  | error, error => true
  | _, _ => false
  end.

Lemma eqb_value_true_iff : forall x y : value,
    is_true(eqb_value x y) <-> x = y.
Proof.
  intros. destruct x, y; split; simpl; 
            try (move/eqP ->); try (intros H; inversion H); auto.
Qed.


Lemma eqvalue: Equality.axiom eqb_value.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_value x y) eqn:beq.
  - constructor. apply eqb_value_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_value_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical value_eqMixin := EqMixin eqvalue.
Canonical value_eqtype := Eval hnf in EqType value value_eqMixin.

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

Inductive array :=
  Array (n: nat) (l: nat).

Definition array_indMixin := Eval simpl in [indMixin for array_rect].

Canonical array_indType := IndType _ array array_indMixin.

Definition array_eqMixin := Eval simpl in [derive eqMixin for array].

Canonical array_eqType := EqType array array_eqMixin.

Definition array_choiceMixin := Eval simpl in [derive choiceMixin for array].

Canonical array_choiceType := ChoiceType array array_choiceMixin.

Definition get_length (a: array) :=
  match a with
    Array _ length => length end.

Inductive volatility :=
  nonvol
 | vol.

Inductive smallvar :=
  SV (s: nat) (q: volatility).

Inductive el_loc :=
  El (a: array) (i: ('I_(get_length a))).

Definition tagged_of_el_loc (l: el_loc) : {a: array & 'I_(get_length a)} :=
  match l with
    El a i => @Tagged _ a _ i end.

Definition el_loc_of_tagged  (x: {a: array & 'I_(get_length a)}): el_loc :=
  El (tag x) (tagged x).

Lemma tagged_of_el_locK: cancel tagged_of_el_loc el_loc_of_tagged.
    by case. Qed.

Definition el_loc_eqMixin := CanEqMixin tagged_of_el_locK.

Inductive myOrdinal (n: nat) :=
  MyOrdinal {f1: nat; _: f1 < n}. 

Canonical myOrdinal_subType n := [subType for @f1 n]. 

Definition myOrdinal_eqMixin n := [eqMixin of myOrdinal n by <:].


Definition equal_index (e: el_loc) (a2: array) (v: value) :=
  match e with
    El a1 i =>
  match v with
    Nat j => ((nat_of_ord i) = j) /\ (a1 = a2)
  | _ => False end
  end.

Inductive exp :=
  Var (x: smallvar) 
| Val (v: value)
| Bop (bop: boptype) (e1: exp) (e2: exp) 
| El_loc (e: el_loc)
| Element (a: array) (e: exp).

Coercion Val : value >-> exp.
Coercion Var : smallvar >-> exp.
Notation "a '[[' e ']]'" := (Element (a) (e))
                              (at level 40, right associativity).

Coercion El_loc : el_loc >-> exp.

Definition loc := smallvar + el_loc. (*memory location type*)

Definition index_loc (a: array) (i: ('I_(get_length a))) : loc :=
  inr (El a i).

Definition generate_locs (a: array): seq loc :=
  map (index_loc a) (enum ('I_(get_length a))).
Notation warvars := (seq loc).

Definition leqvol (q: volatility) :=
  (fun r =>
     match q, r with
       vol, nonvol => false
     | _, _ => true
                end
  ).

Definition leqloc (w: loc) :=
  (fun v: loc =>
     match w, v with
       (inl (SV s1 q1)), (inl (SV s2 q2)) =>
       if (s1 == s2) then (leqvol q1 q2) else
       s1 <= s2
     | (inr (El a1 i1)), (inr (El a2 i2)) =>
       match a1, a2 with Array n1 l1, Array n2 l2 =>
       if (n1 == n2) then
         (
           if (l1 == l2) then
             (i1 <= i2)
           else
             (l1 <= l2)
         )
       else n1 <= n2 end
     | inl _, inr _ => true
     | inr _, inl _ => false
     end ).


(*equality type for arrays*)


Open Scope seq_scope.
Definition eqb_array (a1 a2: array) :=
  match a1, a2 with
    Array s1 l1, Array s2 l2 => andb (s1 == s2) (l1 == l2)
  end.

Lemma eqb_array_true_iff : forall x y : array,
    is_true(eqb_array x y) <-> x = y.
Proof.
  intros. destruct x, y; split; simpl.
  - move/(reflect_conj eqP eqP).
    case => H0 H1. subst. reflexivity.
  - intros H. inversion H. apply/andP; by split.
Qed.

Lemma eqarray: Equality.axiom eqb_array.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_array x y) eqn:beq.
  - constructor. apply eqb_array_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_array_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.

(*equality type for elements of arrays*)

Definition eqb_el_d (x y:el_loc) :=
  match x, y with
    El ax ix, El ay iy => (ax==ay) && ((nat_of_ord ix) == (nat_of_ord iy)) end.

Lemma annoying: forall(a1 a2: array),
    a1 == a2 -> 'I_(get_length a1) = 'I_(get_length a2).
by move => a1 a2 / eqP ->. Qed.


Set Printing All.
Lemma eqb_eld_iff : forall x y : el_loc,
    is_true(eqb_el_d x y) <-> x = y.
Proof.
  case => [ax ix] [ay iy]. simpl.
  split.   case / (reflect_conj eqP eqP) => [H1 H2]. subst.
  cut (ix = iy).
  intros. by subst.
    by apply val_inj.
 Unset Printing All.
 move => [H1 H2].
 apply andb_true_iff. split.
   by move / eqP : H1.
  inversion H2. 
  by apply (introT eqP).
Qed.



Lemma eq_eld_iff: Equality.axiom eqb_el_d.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_el_d x y) eqn:beq.
  - constructor. apply eqb_eld_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_eld_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical eld_eqMixin := EqMixin eq_eld_iff.
Canonical eld_eqtype := Eval hnf in EqType el_loc eld_eqMixin.


(*non-array variable helpers*)
Definition isNV_b (x: smallvar) := 
  match x with
    SV _ nonvol => true
  | _ => false
  end.

Definition isV_b (x: smallvar) :=
  match x with
    SV _ vol => true
  | _ => false
  end.

Definition isNV x := is_true(isNV_b x). 

Definition isV x := is_true(isV_b x).

(*equality type*)

Definition eqb_smallvar (x y: smallvar): bool :=
  match x, y with
    SV sx vol, SV sy vol => sx== sy
  | SV sx nonvol, SV sy nonvol => sx== sy
  | _, _ => false end.                                     

Lemma eqb_smallvar_iff : forall x y : smallvar,
    is_true(eqb_smallvar x y) <-> x = y.
Proof.
  intros. destruct x, y, q, q0; simpl;
     try (split; [move/ eqP ->; reflexivity |
                  intros H; inversion H; auto]);
  try (split; [case => H; discriminate H | case => H H1; inversion H1]).
Qed.

Lemma eqsmallvar: Equality.axiom eqb_smallvar.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_smallvar x y) eqn:beq.
  - constructor. apply eqb_smallvar_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_smallvar_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.

Canonical smallvar_eqMixin := EqMixin eqsmallvar.
Canonical smallvar_eqtype := Eval hnf in EqType smallvar smallvar_eqMixin.

(*memory location helpers*)

Definition eqb_loc (l1: loc) (l2: loc) :=
  match l1, l2 with
    inl x, inl y => x == y
  | inr x, inr y => x == y
  | _, _ => false 
  end.

(*equality type for locations*)

Lemma eqb_loc_true_iff : forall x y : loc,
    is_true(eqb_loc x y) <-> x = y.
Proof.
  case => [x1 | x2] [y1 | y2]; simpl; split; try (by move/ eqP ->);
      try (by move => [] ->); intros H; inversion H.
Qed.

Lemma eqloc: Equality.axiom eqb_loc.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_loc x y) eqn:beq.
  - constructor. apply eqb_loc_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_loc_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical loc_eqMixin := EqMixin eqloc.
Canonical loc_eqtype := Eval hnf in EqType loc loc_eqMixin.

Definition getstring_sv (x1: smallvar) :=
  match x1 with
    SV s _ => s end.

Definition loc_choiceMixin := choiceMixin loc.

(*ordering for locations*)

Lemma loctotal: total leqloc.
  intros x y.
  destruct x as [x | x]; destruct y as [y | y];
    destruct x as [x1 x2]; destruct y as [y1 y2]; unfold leqloc; try by []; simpl.
  destruct (x1 == y1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. 
  rewrite ifT; try by []. destruct x2; destruct y2; simpl; by [].
  move/ eqP : Hbool => Hneq. rewrite ifF. apply leq_total.
  apply not_eq_sym in Hneq.   apply negbTE.
    by move/ eqP: Hneq => Hneq.
    destruct x1 as [n1 l1].
    destruct y1 as [m1 j1].
  destruct (n1 == m1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. assert (m1 == m1). by [].
  rewrite H.
  destruct (l1 == j1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. assert (j1 == j1). by [].
  rewrite H0. apply leq_total.
  move/ eqP : Hbool => Hneq. rewrite ifF. apply leq_total.
  apply not_eq_sym in Hneq.   apply negbTE.
    by move/ eqP: Hneq => Hneq.
  move/ eqP : Hbool => Hneq. rewrite ifF. apply leq_total.
  apply not_eq_sym in Hneq.   apply negbTE.
    by move/ eqP: Hneq => Hneq.
Qed.

Lemma transvol: transitive leqvol.
  intros x y z.
  destruct x; destruct y; destruct z; try by [].
  Qed.

Lemma asyloc: antisymmetric leqloc.
intros x y. move/ andP => [Hxy Hyx].
  destruct x as [x | x]; destruct y as [y | y];
    destruct x as [x1 x2]; destruct y as [y1 y2]; unfold leqloc in Hxy;
      unfold leqloc in Hyx;
      try by []; simpl.
  destruct (x1 == y1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. 
  rewrite ifT in Hyx; try by []. destruct x2; destruct y2; simpl; by [].
 rewrite ifF in Hyx; try by [].
  assert (x1 <= y1 /\ y1 <= x1). by [].
  move/andP : H => H.
  move: (anti_leq H) => one. subst. exfalso. by move/ negbT /eqP: Hbool.
  move/ negbT / eqP : Hbool => Hbool. apply not_eq_sym in Hbool.
  apply negbTE. by move / eqP : Hbool.
    destruct x1 as [n1 l1].
    destruct y1 as [m1 j1].
  destruct (n1 == m1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. assert (m1 == m1). by [].
  rewrite H in Hyx.
  destruct (l1 == j1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. assert (j1 == j1). by [].
  rewrite H0 in Hyx.
  assert (x2 <= y2 /\ y2 <= x2). by [].
  move/andP : H1 => H1.
  move: (anti_leq H1) => one.
  assert (x2 = y2). by apply ord_inj. by subst.
  rewrite ifF in Hyx.
  assert (l1 <= j1 /\ j1 <= l1). by [].
  move/andP : H0 => H0.
  move: (anti_leq H0) => one. subst.
  exfalso. by move/negbT /eqP: Hbool.
  move/ negbT / eqP : Hbool => Hbool. apply not_eq_sym in Hbool.
  apply negbTE. by move / eqP : Hbool.
  rewrite ifF in Hyx.
  assert (n1 <= m1 /\ m1 <= n1). by [].
  move/andP : H => H.
  move: (anti_leq H) => one. subst.
  exfalso. by move/ negbT /eqP : Hbool.
  move/ negbT / eqP : Hbool => Hbool. apply not_eq_sym in Hbool.
  apply negbTE. by move / eqP : Hbool.
Qed.

Lemma loctrans: transitive leqloc.
  intros y x z Hxy Hyz.
  destruct x as [x | x]; destruct y as [y | y]; destruct z as [z | z];
    destruct x as [x1 x2]; destruct y as [y1 y2];
      destruct z as [z1 z2];
      unfold leqloc; unfold leqloc in Hxy; unfold leqloc in Hyz;
                            try by []; simpl.
  destruct (x1 == z1) eqn: Hboolxz; destruct (x1 == y1) eqn: Hboolxy. 
  move/ eqP: Hboolxy => one. subst.
  move/ eqP: Hboolxz => one. subst. rewrite ifT in Hyz.
  apply (transvol y2 x2 z2); try assumption. by [].
  move/ eqP: Hboolxz => one. subst. rewrite ifF in Hyz.
  assert (z1 <= y1 /\ y1 <= z1). by [].
  move/andP : H => H.
  move: (anti_leq H) => one. subst. exfalso. move/ negbT /eqP: Hboolxy.
  by apply. apply negbTE.
  move/ negbT /eqP : Hboolxy => contra. apply not_eq_sym in contra.
    by apply/ eqP.
    move/ eqP : Hboolxy => one. subst. by rewrite ifF in Hyz.
  destruct (y1 == z1) eqn: Hboolyz. 
  move/ eqP : Hboolyz => one. by subst.
  apply (leq_trans Hxy Hyz).
  destruct x1 as [n1 l1]. destruct y1 as [m1 j1]. destruct z1 as [o1 k1].
  destruct (n1 == m1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst. assert (m1 == m1). by [].
  destruct (m1 == o1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst.
  destruct (j1 == k1) eqn: Hbool.
  move/ eqP : Hbool => Heq. subst.
  destruct (l1 == k1) eqn: Hbool; try by [].
  apply (leq_trans Hxy Hyz).
  destruct (l1 == j1) eqn: Hbool1; try by [].
  move/ eqP : Hbool1 => one. subst. rewrite ifF; try by [].
  destruct (l1 == k1) eqn: Hbool2; try by [].
  move/ eqP: Hbool2 => two. subst.
  assert (j1 <= k1 /\ k1 <= j1). by [].
  move/andP : H0 => H0.
  move: (anti_leq H0) => one. subst. exfalso. by move/ negbT /eqP: Hbool.
  apply (leq_trans Hxy Hyz). by [].
  destruct (m1 == o1) eqn: Hbool1.
  move/ eqP : Hbool1 => Heq. subst. rewrite ifF; try by []. 
  destruct (n1 == o1) eqn: Hbool2.
  move/ eqP: Hbool2 => Heq. subst.
  assert (m1 <= o1 /\ o1 <= m1). by [].
  move/andP : H => H.
  move: (anti_leq H) => one. subst. exfalso. by move/ negbT /eqP: Hbool.
  apply (leq_trans Hxy Hyz).
Qed.
Definition leqlocP := perm_sortP loctotal loctrans asyloc.

Definition remove (L1 L2 : seq loc) :=
  filter (fun x =>  negb (x \in L1)) L2.

Definition get_smallvars (w: warvars) :=
  filter (fun v =>
          match v with
            (inl _) => true
          | (inr _) => false
          end) w.

(*locations in arrays*)
 Lemma genloc_contents: forall(l: loc) (a: array),
              l \in generate_locs a ->
                    exists (el: el_loc), inr el = l.
   intros. unfold generate_locs in H.
   move/ mapP: H => [x Hx1 Hx2]. unfold index_loc in Hx2.
   exists (El a x). auto. Qed.

Definition get_array (i: el_loc) :=
match i with El a _ => a end.

 Lemma genloc_getarr: forall(i: el_loc) (a: array),
           (inr i \in (generate_locs a)) =
           ((get_array i) == a).
   intros. destruct (get_array i == a) eqn: Hbool.
   destruct i as [i1 i2]. simpl in Hbool.
   move/ eqP: Hbool => Heq. subst. apply/ mapP. exists i2; try by [].
   rewrite mem_enum. by []. 

   destruct i as [i1 i2]. simpl in Hbool.
   apply/ negbTE/ mapP.
   intros contra. move: contra => [x Hx1 Hx2].
   inversion Hx2. move / negbT / eqP : Hbool. by apply.
Qed.

 Lemma genloc_int: forall(a a1: array),
  ( intersect (generate_locs a)
              (generate_locs a1)) -> (a = a1).
   intros. move: H => [z [Hel1 Hel2 ] ].
   move: (genloc_contents z a Hel1) => [el Heq]. subst.
   destruct el as [a0 i].
   move/mapP: Hel2 => [i1 [Hi1 Hi2] ].
   unfold index_loc in Hi2. inversion Hi2.
   move/mapP: Hel1 => [j1 [Hj1 Hj2] ].
   unfold index_loc in Hj2. inversion Hj2.
   by [].
Qed.

(*further DSL constructs*)
Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp)
| asgn_arr (a: array) (i: exp) (e: exp) (*i is index, e is new value of a[i]*)
| incheckpoint (w: warvars)
| inreboot.

Inductive command :=
  Ins (l: instruction)
| Seqcom (l: instruction) (c: command)
| ITE (e: exp) (c1: command) (c2: command).

(*useful when considering traces and subtraces*)
Open Scope nat_scope.
Fixpoint size_com (c : command) :=
  match c with
    Ins l => match l with
              skip => 0
             | _ => 1 end
| Seqcom _ c1 => 1 + (size_com c1)
| ITE _ c1 c2 => 1 + (size_com c1) + (size_com c2) end.
Close Scope nat_scope.

Notation "l ';;' c" := (Seqcom l c)
  (at level 41, right associativity).

Notation "'TEST' e 'THEN' c1 'ELSE' c2 " := (ITE e c1 c2)
                                              (at level 100).
Coercion Ins : instruction >-> command.


(*memory*)
(*the nonvolatile memory*)

Definition map_t (A: eqType) := A -> value.

Definition emptymap A :(map_t A) := (fun _ => error).
Definition updatemap {A} (m: map_t A) (i: A) (v: value) : map_t A :=
  if v == error then m else (fun j =>
                                                               if (j ==i) then v
                                                               else (m j)).
Notation "i '|->' v ';' m" := (updatemap m i v)
  (at level 100, v at next level, right associativity).

Notation mem := (map_t loc_eqtype). 


Definition locsort := sort leqloc.

(*Invariant that keeps domains of NV mems equal for equal maps, ie, that maintains
 functional extentionality.
 A subtlety to be worked around is that, due to assumptions made in the
 paper, array locations may be added uninitialized to the domain.*)
Definition valid_nvm (m: mem) (d: warvars) := (forall(x: smallvar), (m (inl x) != error) <-> (inl x) \in d)
                                                                              /\
       (forall(a: array),
           (( exists(el1: el_loc), (inr el1) \in (generate_locs a) /\ (m (inr el1) != error))
           ->
           subseq_w (generate_locs a) d) /\
           ((intersect (generate_locs a) d) ->
            exists(el1: el_loc), (inr el1) \in (generate_locs a) /\ (m (inr el1) != error)) )
  /\ sorted leqloc d /\ uniq d.


Inductive nvmem := (*nonvolatile memory*)
  NonVol (m : mem) (D: warvars) (WFnvem: valid_nvm m D)
.
Inductive vmem := (*volatile memory*)
  Vol (m : mem).

(*interface allowing reading, writing, and other memory operations
 while maintaining the valid_nvm invariant*)
Definition getmap (N: nvmem) :=
  match N with NonVol m _ _ => m end.

Definition getdomain (N: nvmem) :=
  match N with NonVol _ D _ => D end.

Definition getvalue (N: nvmem) (i: loc) :=
  (getmap N) i.
  Notation "v '<-' N" := (getvalue N v)
                           (at level 40).

Definition wf_dom (w: warvars) (m: mem) :=
    valid_nvm (fun input => if (input \in w) then m input else error) w.

Lemma restrict_wf {N: nvmem} {w: warvars}:
  wf_dom w (getmap N)->
  valid_nvm (fun input => if (input \in w) then (getmap N) input else error) w.
intros. destruct N as [m d Hn]. apply H. Qed.

Definition restrict (N: nvmem) (w: warvars) (Hw: wf_dom w (getmap N)) :=
    NonVol (fun input => if (input \in w) then (getmap N) input else error) w (restrict_wf Hw).


Definition update_dom_sv (i: smallvar) (v: value) (d: warvars) :=
    if (v == error) then d else locsort (undup ((inl i) :: d)).


Lemma updatemap_sv {m: mem} {d: warvars} {i: smallvar} {v: value}:
    valid_nvm m d ->
    valid_nvm (updatemap m (inl i) v) (update_dom_sv i v d).
    unfold valid_nvm. move => [Hsv [Ha [Hsort Huniq] ] ].
   - repeat split; unfold updatemap; unfold update_dom_sv; destruct (v == error) eqn: Hbool; try 
        (move/ eqP : Hbool => Heq; subst); try apply (Hsv x); try assumption.
        remember (inl x) as sv.
        remember (inl i) as sv1.
        destruct (sv == sv1) eqn: Hbool1.
        move/ eqP : Hbool1 => Hbool1. rewrite Hbool1.
        rewrite ifT. intros.
        rewrite mem_sort. rewrite mem_undup.
        apply (mem_head sv1 d). auto.
        rewrite ifF. intros Hm. subst. apply (Hsv x) in Hm.
        rewrite mem_sort. rewrite mem_undup.
        rewrite in_cons. apply/orP. by right. by []. 
        remember (inl x) as sv.
        remember (inl i) as sv1.
        destruct (sv == sv1) eqn: Hbool1.
        move/ eqP : Hbool1 => Hbool1. rewrite Hbool1.
        rewrite ifT. intros. by move/eqP : Heq. auto.
        move => Hin.
        rewrite mem_sort in Hin. rewrite mem_undup in Hin.
        rewrite in_cons in Hin. move/ orP : Hin => [Hin1 | Hin2]. exfalso. move/ eqP : Hin1 => Heq1. subst.
        move/ negbT / eqP : Hbool1. by apply.
        move: (Hsv x) => [Hsv1 Hsv2]. subst.
        apply Hsv2 in Hin2.
        by rewrite ifF.
   - move: (Ha a) => [Hd1 Hd2]. assumption.
     move => [el1 [H1 H2] ].
     assert (inr el1 != inl i). by [].
     move/ eqP : H2 => Herr.
        remember (inl i) as sv1.
   - move: (Ha a) => [Hd1 Hd2].
     suffices: 
       subseq_w (generate_locs a) d.
     move => Hsub1. rewrite - (undup_id Huniq) in Hsub1.
     rewrite - subw_sort.
     remember (sv1 :: d) as S.
     rewrite subw_undup. subst.
     rewrite subw_undup in Hsub1.
     apply (subw_cons Hsub1).
     apply Hd1. exists el1. split; try assumption. apply/ eqP. assumption.
     move: (Ha a) => [Hd1 Hd2]. apply Hd2.
     move: (Ha a) => [Hd1 Hd2].
     move => Hint.
     rewrite intersect_sort in Hint.
     rewrite (intersect_undup (generate_locs a)
                                         (inl i :: d)
                        ) in Hint.
     assert (inl i \notin (generate_locs a)).
     apply/ negP. intros contra.
     apply genloc_contents in contra. move : contra => [elc contra].
     discriminate contra.
     apply (intersect_cons Hint) in H.
     move: (Hd2 H) => [el1 [Hel1 Hel2 ] ]. exists el1.
     split; try rewrite ifF; try assumption.
     apply sort_sorted. apply loctotal. rewrite sort_uniq.
     apply (undup_uniq (inl i :: d)).
Qed.

 Definition update_dom_arr (i: el_loc) (v: value) (d: warvars) :=
    if (v == error) then d else locsort (undup (generate_locs (get_array i) ++ d)).

Lemma updatemap_arr {m: mem} {d: warvars} {i: el_loc} {v: value} 
    :
    valid_nvm m d ->
    valid_nvm (updatemap m (inr i) v) (update_dom_arr i v d). 
    unfold valid_nvm. move => [Hsv [Ha [Hsort Huniq] ] ].
   - repeat split; unfold updatemap; unfold update_dom_arr; destruct (v == error) eqn: Hbool; try 
                                                                                                (move/ eqP : Hbool => Heq; subst); try apply (Hsv x); try assumption.
     intros.
     assert (inl x != inr i). by [].
     move/ eqP /eqP : H => Hneq.
     apply (Hsv x) in Hneq.
     rewrite mem_sort. rewrite mem_undup.
     rewrite mem_cat. apply/ orP. by right.
     rewrite mem_sort mem_undup mem_cat => Hin. move/ orP : Hin => [Hcontra | Hin].
     apply genloc_contents in Hcontra.
     move: Hcontra => [el contra]. discriminate contra.
     move: (Hsv x) => [Hsv1 Hsv2]. apply Hsv2 in Hin.
     by apply/eqP / eqP. 
   - move: (Ha a) => [Ha1 Ha2]. assumption.
     move => [el1 [H1 H2] ].
     remember (inr el1) as z.
     destruct (z == inr i) eqn: Hbool. move/ eqP: Hbool => one.
     subst. inversion one. subst.
     rewrite genloc_getarr in H1. move/ eqP: H1 => H1.
     rewrite H1. rewrite - subw_sort.
     rewrite subw_undup.
     apply subw_prefix. apply subw_refl.
     rewrite ifF in H2; try assumption.
     rewrite - subw_sort. rewrite subw_undup. apply subw_suffix. move: (Ha a) => [Ha1 Ha2].
     apply Ha1. subst. exists el1. split; try assumption.
   - move: (Ha a) => [Hd1 Hd2]. assumption.
     rewrite intersect_sort intersect_undup intersect_cat => Hint.
     destruct Hint as [Hint | Hint].
     apply genloc_int in Hint. 
     exists i. split. rewrite genloc_getarr. by rewrite Hint.
     rewrite ifT; try by []. move/eqP : Heq. by apply.
     move: (Ha a) => [Ha1 Ha2].
     apply Ha2 in Hint.
     move: Hint => [el1 [Hin Herr] ].
     exists el1. split; try by [].
     destruct (el1 == i) eqn: Hbool.
     move/ eqP: Hbool => one. subst.
     rewrite ifT; try by []. by apply/ eqP.
     rewrite ifF; try by [].
     apply sort_sorted. apply loctotal.
     rewrite sort_uniq.
     apply (undup_uniq (generate_locs (get_array i) ++ d)).
Qed.


Definition updateNV_sv (N: nvmem) (i: smallvar) (v: value) :=
  match N with NonVol m D H =>
               NonVol (updatemap m (inl i) v) (update_dom_sv i v D) (updatemap_sv H) end.


Definition updateNV_arr (N: nvmem) (i: el_loc) (a: array) (v: value)
  :=
    match N with NonVol m D H =>
               NonVol (updatemap m (inr i) v) (update_dom_arr i v D)
                      (updatemap_arr H)
  end.

  Lemma updatemaps_wf {m m': mem} {d d': warvars}
    :
    valid_nvm m d ->
    valid_nvm m' d' ->
    valid_nvm (fun j =>
      if (j \in d)
          then (m j)
      else (m' j)) (locsort (undup (d ++ d'))).
    intros. unfold valid_nvm in H. move: H => [Hsv [Ha [Hsort Huniq] ] ].
move: H0 => [Hsv0 [Ha0 [Hsort0 Huniq0] ] ].
repeat split.
destruct ((inl x) \in d) eqn: Hbool. rewrite ifT.
intros Herr.
move: (Hsv x) => [Hsv1 Hsv2]. apply Hsv1 in Herr.
rewrite mem_sort mem_undup mem_cat. apply/orP. by left.
  by rewrite Hbool.
  rewrite ifF; try by [].
move: (Hsv0 x) => [Hsv1 Hsv2] Herr. apply Hsv1 in Herr.
rewrite mem_sort mem_undup mem_cat. apply/orP. by right.
intros Hin. rewrite mem_sort mem_undup mem_cat in Hin.
destruct (inl x \in d) eqn: Hbool.
rewrite ifT; try by [].
move: (Hsv x) => [Hsv1 Hsv2]. by apply Hsv2 in Hbool.
move/ orP : Hin => [contra | Hin]. rewrite Hbool in contra. discriminate contra. rewrite ifF; try by [].
move: (Hsv0 x) => [Hsv1 Hsv2]. by apply Hsv2 in Hin.
intros [el1 [Hel1 Hel2] ]. destruct (inr el1 \in d) eqn: Hbool.
rewrite ifT in Hel2; try by []. rewrite - subw_sort. rewrite subw_undup.
apply subw_prefix.
move:  (Ha a) => [Ha1 Ha2]. apply Ha1. exists el1. split; try assumption.
rewrite ifF in Hel2; try by []. rewrite - subw_sort. rewrite subw_undup.
apply subw_suffix.
move:  (Ha0 a) => [Ha1 Ha2]. apply Ha1. exists el1. split; try assumption.
move => Hint. rewrite intersect_sort intersect_undup intersect_cat in Hint.
destruct Hint.
move:  (Ha a) => [Ha1 Ha2].
move/ Ha2 : H => H.
remember H as Hint. clear HeqHint.
move: H => [el1 [Hel1 Hel2] ].
exists el1; split; try assumption.
apply Ha1 in Hint. apply Hint in Hel1.
rewrite ifT; try by [].

move:  (Ha a) => [Ha1 Ha2].
move:  (Ha0 a) => [Ha1' Ha2'].
move/ Ha2' : H => H.
move: H => [el1 [Hel1 Hel2] ].
destruct ((inr el1) \in d) eqn: Hbool.
suffices: intersect (generate_locs a) d.
move => Hint. 
move/ Ha2 : Hint => Hint.
remember Hint as Hsub. clear HeqHsub. apply Ha1 in Hsub.
move: Hint => [el11 Hel11].
exists el11. rewrite ifT; try by []. apply Hsub.
  by destruct Hel11.
  exists (inr el1). split; try by [].
  exists el1; split; try assumption. rewrite ifF; try by [].
  apply sort_sorted. apply loctotal.
     rewrite sort_uniq.
     apply (undup_uniq (d ++ d')).
     Qed.


  Definition updatemaps (N: nvmem) (N': nvmem): nvmem :=
  match N, N' with
    NonVol m D H, NonVol m' D' H' => NonVol
   (fun j =>
      if (j \in D)
          then (m j)
          else (m' j)) (locsort (undup (D ++ D'))) (updatemaps_wf H H')
  end.
Notation "m1 'U!' m2" := (updatemaps m1 m2) (at level 100).

Definition isdomain_nvm (N: nvmem) (w: warvars) :=
  (getdomain N) == w.
Definition subset_nvm (N1 N2: nvmem) := (forall(l: loc),
                                    l \in (getdomain N1) ->
                                    (getmap N1) l = (getmap N2) l
                                  ).

(*observation and write set infrastructure for single step evaluation
 and program traces*)
Inductive cconf := (*continuous configuration*)
  ContinuousConf (triple: nvmem * vmem * command).

Notation context := (nvmem * vmem * command).

Notation iconf := (context * nvmem * vmem * command).

Definition getcom (C: context) :=
  match C with
    (_, _, out) => out end.

Definition ro := loc * value. (*read observation*)
Definition readobs := seq ro.

Notation NoRdObs := (nil : readobs).

Inductive obs := 
  RdObs (r: readobs)
| reboot
| checkpoint.
Coercion RdObs : readobs >-> obs.

(*equality type for observations*)
Definition eqb_ro (ro1: ro) (ro2: ro) :=
  match ro1, ro2 with
    (l1, v1), (l2, v2) => (l1 == l2) && (v1 == v2)
  end.

Lemma eqb_ro_true_iff : forall x y : ro,
    is_true(eqb_ro x y) <-> x = y.
Proof.
  case => [l1 v1] [l2 v2]. split.
  simpl. case / andP. by repeat move / eqP ->.
  case. repeat move ->. unfold eqb_ro.
apply / andP. by split. 
Qed.

Lemma eqro: Equality.axiom eqb_ro.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_ro x y) eqn:beq.
  - constructor. apply eqb_ro_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_ro_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical ro_eqMixin := EqMixin eqro.
Canonical ro_eqtype := Eval hnf in EqType ro ro_eqMixin.

Definition eqb_obs (o1: obs) (o2: obs) :=
  match o1, o2 with
    reboot, reboot => true
  | checkpoint, checkpoint => true
  | RdObs R1, RdObs R2 => R1 == R2
  | _, _ => false end.

Lemma eqb_obs_true_iff : forall x y : obs,
    is_true(eqb_obs x y) <-> x = y.
Proof.
  case => [ R1 | |] [R2 | | ]; split; simpl; try (intros H; discriminate H);
  try auto.
  + by move/ eqP ->.
  + move => [H]. by rewrite H.
Qed.

Lemma eqobs: Equality.axiom eqb_obs.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_obs x y) eqn:beq.
  - constructor. apply eqb_obs_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_obs_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical obs_eqMixin := EqMixin eqobs.
Canonical obs_eqtype := Eval hnf in EqType obs obs_eqMixin.

Notation obseq := (seq obs). 

(*helpers for observations and warvars*)

(*converts from location to set of locations checkpointed by DINO
if that location is written to after being read from*)
Definition getwvs (l: loc) :=
  match l with
    inl x => [::l]
  | inr (El a _) => (generate_locs a) end.

Fixpoint readobs_wvs (R: readobs): (seq loc) := 
  match R with
    nil => nil
  | (r::rs) => getwvs(fst r) ++ (readobs_wvs rs)
  end. 


(*relations between continuous and intermittent observations.*)

Inductive prefix: obseq -> obseq -> Prop :=
  P_Base: forall(O: obseq), checkpoint \notin O ->
                       reboot \notin O -> prefix O O 
| P_Ind: forall (O1 O2 O3: obseq), prefix O1 O2 ->
                              reboot \notin O3 -> checkpoint \notin O3 ->
                                                prefix O1 (O2 ++ O3).
Notation "S <=p T" := (prefix S T) (at level 100).


(*Where
O1 is a sequence of read observation seqs,
where each continguous read observation seq is separated from those adjacent to it by a reboot,
and O2 is a read observation seq,
prefix_seq determines if each ro seq in O1 is a valid
prefix of O2*)
Inductive prefix_seq: obseq -> obseq -> Prop :=
  RB_Base: forall(O: obseq),
    reboot \notin O -> checkpoint \notin O ->
    prefix_seq O O
| RB_Ind: forall(O1 O2: obseq) (O1': obseq),
    reboot \notin O1 -> checkpoint \notin O1 ->
    reboot \notin O2 -> checkpoint \notin O2 ->
    checkpoint \notin O1' ->
    (O1 <=p O2) -> prefix_seq O1' O2 ->
    prefix_seq (O1 ++ [:: reboot] ++ O1') O2.

Notation "S <=m T" := (prefix_seq S T) (at level 100).


(* Where
O1 is a sequence of ((read observation seq sequences), where
each continguous read observation seq is separated from those adjacent to it
by a reboot), where each sequence is separated from those adjacent to it by a checkpoint.
ie, each read observation seq in a given read observation sequence
occurs within the same checkpointed region as all the other read observation seqs in that sequence,
O2 is a read observation seq,
prefix_frag determines if each ro seq in O1 is a prefix of the corresponding fragment of O2
(where the fragments are separated by the positioning of the checkpoints in O1 and O2)
 *)
Inductive prefix_fragment: obseq -> obseq -> Prop :=
  CP_Base: forall(O1: obseq) (O2: obseq), prefix_seq O1 O2 -> prefix_fragment O1 O2 
| CP_IND: forall(O1 O1': obseq) (O2 O2': obseq),
    prefix_seq O1 O2 -> prefix_fragment O1' O2' ->
   prefix_fragment (O1 ++ [:: checkpoint] ++ O1') (O2 ++ [::checkpoint] ++ O2'). 
Notation "S <=f T" := (prefix_fragment S T) (at level 100).


(*operational semantics*)

(*evaluation relation for expressions*)
Inductive eeval: nvmem -> vmem -> exp -> readobs -> value -> Prop :=
  VAL: forall(N: nvmem) (V: vmem) (v: value),
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N V v [::] v
| BINOP: forall(N: nvmem) (V: vmem)
          (e1: exp) (e2: exp)
          (r1: readobs) (r2: readobs)
          (v1: value) (v2: value) (bop: boptype),
    eeval N V e1 r1 v1 ->
    eeval N V e2 r2 v2 -> 
    (isvalidbop bop v1 v2) ->
    eeval N V (Bop bop e1 e2) (r1++ r2) (bopeval bop v1 v2)
| RD_VAR_NV: forall(N: nvmem) (mapV: vmem) (x: smallvar) (v: value),
    ((inl x) <-N) = v ->
    isNV(x) -> 
    (isvaluable v) -> 
    eeval N mapV x [:: ((inl x), v)] v
| RD_VAR_V: forall(N: nvmem) (mapV: mem) (x: smallvar) (v: value),
    (mapV (inl x)) = v ->
    isV(x) -> 
    (isvaluable v) -> 
    eeval N (Vol mapV) x [:: ((inl x), v)] v
| RD_ARR: forall(N: nvmem) (V: vmem)
           (a: array)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (element: el_loc)
           (v: value),
    eeval N V (index) rindex vindex ->
    ((inr element) <-N) = v ->
    equal_index element a vindex ->
    (isvaluable v) -> 
    eeval N V (a[[index]]) (rindex++[:: ((inr element), v)]) v
.

(*record of variables written to, read from, and first written to*)
Notation the_write_stuff := ((seq loc) * (seq loc) * (seq loc)).


Definition getwt (W: the_write_stuff) := match W with (out, _, _ )=> out end.

Definition getrd (W: the_write_stuff) := match W with (_, out , _ )=> out end.

Definition getfstwt (W: the_write_stuff) := match W with (_, _, out )=> out end.

Notation emptysets := ((nil : (seq loc)), (nil: (seq loc)), (nil: (seq loc))).



(*single step evaluation relation which accumulates which variables are written/read from
 as well as what values are read from which locations*)

Inductive cceval_w: context -> obseq -> context -> the_write_stuff -> Prop :=
CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
    wf_dom w (getmap N) ->
    cceval_w (N, V, ((incheckpoint w);; c))
             (checkpoint:: nil)
             (N, V, c)
             (nil, nil, nil)
| NV_Assign: forall{x: smallvar} {N: nvmem} {V: vmem} {e: exp} {r: readobs} {v: value},
    eeval N V e r v ->
    isNV(x) -> 
    (isvaluable v) -> 
    cceval_w (N, V, Ins (asgn_sv x e))
             (RdObs r :: nil)
             ((updateNV_sv N x v), V, Ins skip)
             ([:: inl x],  (readobs_wvs r), (remove (readobs_wvs r) [:: inl x]))
| V_Assign: forall{x: smallvar} {N: nvmem} {mapV: mem} {e: exp} {r: readobs} {v: value},
    eeval N (Vol mapV) e r v ->
    isV(x) -> 
    (isvaluable v) -> 
    cceval_w (N, (Vol mapV), Ins (asgn_sv x e)) 
             (RdObs r :: nil)
             (N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
             (nil,  (readobs_wvs r), nil)
| Assign_Arr: forall {N: nvmem} {V: vmem}
               {a: array}
               {ei: exp}
               {ri: readobs}
               {vi: value}
               {e: exp}
               {r: readobs}
               {v: value}
               {element: el_loc},
    eeval N V ei ri vi ->
    eeval N V e r v ->
    (isvaluable v) -> 
  (equal_index element a v) ->
    cceval_w (N, V, Ins (asgn_arr a ei e))
           ((RdObs (cat ri r)) :: nil)
           ((updateNV_arr N element a v), V, Ins skip)
           ([:: inr element], (readobs_wvs (cat r ri)), (remove (readobs_wvs (cat r ri)) [:: inr element]))
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval_w (N, V, (skip;;c)) ((RdObs [::])::nil) (N, V, c) (nil, nil, nil)
| Seq: forall (N N': nvmem)
         (V V': vmem)
         (l: instruction)
         (c: command)
         (O: obseq)
         (W: the_write_stuff),
    (forall(w: warvars), l <> (incheckpoint w)) ->
    l <> skip ->
    cceval_w (N, V, Ins l) O (N', V', Ins skip) W ->
    cceval_w (N, V, (l;;c)) O (N', V', c) W
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> 
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) ((RdObs r)::nil) (N, V, c1) (nil, (readobs_wvs r), nil)
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) ((RdObs r)::nil) (N, V, c2) (nil, (readobs_wvs r), nil).

Definition append_write (W1 W2: the_write_stuff) :=
  ((getwt W2) ++ (getwt W1) , (getrd W2) ++ (getrd W1),  (remove (getrd W1) (getfstwt W2))
                                         ++ (getfstwt W1)).

