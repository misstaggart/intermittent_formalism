Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Lists.List Strings.String Program.
Require Export Coq.Strings.String.
From mathcomp Require Import ssrnat ssreflect ssrfun ssrbool eqtype.
From Semantics Require Import lemmas_0.
(*ambiguous coercion error message ask arthur*)

(*basic list functions that I couldn't find in a library*)
Open Scope list_scope.
Fixpoint eq_lists {A: Type} (L1: list A) (L2: list A) (eq: A -> A -> Prop) :=
        match L1, L2 with
          nil, nil => True
        | (w::ws), (d::ds) => (eq w d) /\ (eq_lists ws ds eq) (*considers order*)
        | _ , _ => False end.

Fixpoint member {A: Type} (eq: A -> A -> bool) (a: A)  (L: list A) :=
  match L with
    [] => false
  | x::xs => orb (eq a x) (member eq a xs)
  end.

(*removes L1 from L2*)
Definition remove {A: Type} (in_A: A -> list A -> bool) (L1 L2 : list A) :=
  filter (fun x => negb (in_A x L1)) L2.

Definition prefix {A: Type} (O1: list A) (O2: list A) :=
  exists(l: nat), O1 = firstn l O2.

Close Scope list_scope.

Open Scope string_scope.
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

(*Set Printing Coercions.
Lemma eqb_value_true_iff : forall x y : value,
    is_true(eqb_value x y) <-> x = y.
Proof.
  intros. destruct x, y; split; simpl; try (intros H; discriminate H).
  - move/eqP ->. reflexivity.
  - intros H. inversion H. (*ask arthur..can't this be combined into one thing with move?*) apply eq_refl.
  - move/eqP ->. reflexivity. (*why can the above move/eqP
                                             be done with auto but this onenot*)
  - intros H. inversion H. apply eq_refl.
  - auto.
  - auto.*)


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

(*value helper functions*)
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


(*memory maps...used for both memories and checkpoints*)
Definition map_t (A: eqType) := A -> value.

(*memory helpers*)
Definition emptymap A :(map_t A) := (fun _ => error).
Definition updatemap {A} (m: map_t A) (i: A) (v: value) : map_t A := (fun j =>
                                                               if (j ==i) then v
                                                               else (m j)).
Notation "i '|->' v ';' m" := (updatemap m i v)
  (at level 100, v at next level, right associativity).
(*in (m1 U! m2), m1 is checked first, then m2*)

Definition indomain {A} (m: map_t A) (x: A) :=
  match m x with
    error => False
  | _ => True
  end.
(*this function is NOT used to check the domain of checkpoint maps.
 In particular, because an entire array can be checkpointed even if only
 one element has been assigned to (while the other elements may, in theory, still be unassigned),
(in particular, I refer to D-WAR-CP-Arr)
this function would return that assigned array elements are in the domain of N, while the unassigned array
elements are not, even though both have been checkpointed.
 I resolved this problem by defining indomain_nvm, used for checkpoint maps in algorithms.v, which
checks if a warvar is in the domain, rather than checking a location.
 *)
(******************************************************************************************)

(*******************************more syntax**********************************************)
Inductive array :=
  Array (s: string) (l: nat).

Inductive volatility :=
  nonvol
 | vol.

Inductive smallvar :=
  SV (s: string) (q: volatility).

Inductive dangerous_el :=
  El_d (a: array) (n: nat).

(*used subtypes to enforce the fact that only some expressions are
 memory locations*)
Definition elpred  := (fun x=> match x with
                                        El_d (Array _ length) i => (i <? length)
                                 end).
(*elpred checks if index is a natural in bounds*)

Notation el := {x: dangerous_el | elpred x}.

Check SubType el.

Inductive exp :=
  Var (x: smallvar) 
| Val (v: value)
| Bop (bop: boptype) (e1: exp) (e2: exp) 
| El_loc (e: el)
| Element (a: array) (e: exp). (*good that you let in out of bounds arrays here because it means that
                           war bugs of that kind can still get in at the type level,
                           need the CP system*)
Coercion Val : value >-> exp.
Coercion Var : smallvar >-> exp.
Notation "a '[[' e ']]'" := (Element (a) (e))
                              (at level 100, right associativity).


Definition loc := smallvar + el. (*memory location type*)

Notation warvars := (list loc).
(*Coercion (inl smallvar el): smallvar >-> loc.*)
(*Coercion inl: smallvar >-> loc.*)

(**location and warvar helper functions*)
(**no need to work directly with the subtypes or sumtypes, just use these**)
(**Note: some of these are currently unused due to implementation changes, but I left them
 as they might be useful later*)

(*array and el functions*)

(*equality type for arrays*)
Open Scope list_scope.
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
  - intros H. inversion H.
    apply (introT (reflect_conj eqP eqP)). (*ask arthur is there a
                                            way to do this using ssreflect
                                            rather than the introT
                                            lemma*)
    split; reflexivity.
Qed.

Lemma eqarray: Equality.axiom eqb_array.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_array x y) eqn:beq.
  - constructor. apply eqb_array_true_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_array_true_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Canonical array_eqMixin := EqMixin eqarray.
Canonical array_eqtype := Eval hnf in EqType array array_eqMixin.
(*****)

(*equality type for elements*)

Definition eqb_el_d (x y:dangerous_el) :=
  match x, y with
    El_d ax ix, El_d ay iy => (ax==ay) && (ix == iy) end.


Lemma eqb_eld_iff : forall x y : dangerous_el,
    is_true(eqb_el_d x y) <-> x = y.
Proof.
  case => [ax ix] [ay yP]. simpl.
  split. case / (reflect_conj eqP eqP) => [H1 H2]. by subst.
  move => [H1 H2]. subst. apply/ (reflect_conj eqP eqP). auto.
Qed.

Lemma eq_eld_iff: Equality.axiom eqb_el_d.
Proof.
  unfold Equality.axiom. intros.
  destruct (eqb_el_d x y) eqn:beq.
  - constructor. apply eqb_eld_iff in beq. assumption.
  -  constructor. intros contra. apply eqb_eld_iff in contra.
     rewrite contra in beq. discriminate beq.
Qed.
Check el.
Check val.
Check SubEqMixin.
Check EqMixin.
Check Equality.mixin_of.
Canonical eld_eqMixin := EqMixin eq_eld_iff.
Canonical eld_eqtype := Eval hnf in EqType dangerous_el eld_eqMixin.
(*suggests it wants an equality relation for the big type before it lets
 you have it for the subtype...that's annoying...ask arthur*)
Check SubEqMixin.
Check SubType.

Definition testname := Array "a" 10.
Definition testname1 := El_d testname 0.
Lemma xworks: is_true (elpred testname1).
  unfold elpred. unfold testname1. unfold testname. auto. Qed.

Definition Test: el := eqtype.Sub testname1 xworks. (*ask arthur shouldn't coq be able to infer the subtype type*)

Check Test == Test.

(*smallvar functions*)
Definition isNV_b (x: smallvar) := (*checks if x is stored in nonvolatile memory*)
  match x with
    SV _ nonvol => true
  | _ => false
  end.

Definition isV_b (x: smallvar) :=(*checks if x is stored in volatile memory*)
  match x with
    SV _ vol => true
  | _ => false
  end.

Definition isNV x := is_true(isNV_b x). (*prop version of isNV_b*)

Definition isV x := is_true(isV_b x). (*prop version of isV_b*)

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

(*loc and warvar functions*)

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
(*******************************************************************)

(*more syntax*)
Inductive instruction :=
  skip
| asgn_sv (x: smallvar) (e: exp) (*could distinguish between NV and V assignments as well here*)
| asgn_arr (a: array) (i: exp) (e: exp) (*i is index, e is new value of a[i]*)
| incheckpoint (w: warvars)
| inreboot.
(*added the in prefixes to distinguish from the observation reboots
 and checkpoints*)

Inductive command :=
  Ins (l: instruction)
| Seqcom (l: instruction) (c: command) (*added suffix to distinguish from Seq ceval
                                         constructor*)
| ITE (e: exp) (c1: command) (c2: command).

Notation "l ';;' c" := (Seqcom l c)
                         (at level 100).

Notation "'TEST' e 'THEN' c1 'ELSE' c2 " := (ITE e c1 c2)
                                              (at level 100).
Coercion Ins : instruction >-> command.

(*******************************************************************)

(******setting up location equality relation for memory maps******************)
(****************************************************************)

(****************************memory*************************************)

(*memory locations defined above warvars*)
Notation mem := (map_t loc_eqtype). (*memory mapping*)

Inductive nvmem := (*nonvolatile memory*)
  NonVol (m : mem) (D: warvars). (*extra argument to keep track of checkpointed warvars because
                                  it might be nice to have for when we do checkpoint proofs*)

Inductive vmem := (*volatile memory*)
  Vol (m : mem).

(*I could change nvmem and vmem to enforce that they only take in smallvars
 of the correct type but it's already checked in my evaluation rules*)

(**************************helpers for the memory maps*********************************************)

(*note: a lot of these aren't being used right now because, after I changed the types
 of DINO and WAR, they aren't necessary.
 I won't delete them because having the domain of the checkpoint easily accessible and
 manipulable could be handy in the future*)

Definition getmap (N: nvmem) :=
  match N with NonVol m _ => m end.

Definition getdomain (N: nvmem) :=
  match N with NonVol _ D => D end.

Definition getvalue (N: nvmem) (i: loc) :=
  (getmap N) i.
  Notation "v '<-' N" := (getvalue N v)
                           (at level 40).


  (*updates domain and mapping function*)
Definition updateNV (N: nvmem) (i: loc) (v: value) :=
  match N with NonVol m D =>
               NonVol (updatemap m i v) (
                        match i with 
                          inl x => ((inl x) :: D) (*i is a smallvar*)
                        | inr el => ((inr (getarray el))::D) (*i is an array element*)
                                     (*here I add the entire array to the domain
                                      even though only one element has been assigned to*)
                        end
                      )
  end.

(*used to update NV memory with checkpoint*)
(*checks N first, then N'*)
Definition updatemaps (N: nvmem) (N': nvmem): nvmem :=
  match N, N' with
    NonVol m D, NonVol m' D' => NonVol
  (fun j =>
     match m j with
     error => m' j
     | x => x
     end
  )
  (D ++ D') (*inclusion of duplicates*)
  end.
Notation "m1 'U!' m2" := (updatemaps m1 m2) (at level 100).

Notation emptyNV := (NonVol (emptymap loc eqb_loc) nil).
Definition reset (V: vmem) := Vol (emptymap loc eqb_loc).

(*restricts memory map m to domain w*)
(*doesn't actually clean the unnecessary variables out of m*)
Definition restrict (N: nvmem) (w: warvars): nvmem :=
  match N with NonVol m D => NonVol
    (fun input => if (memberloc_wvs_b input w) then m input else error) w  end.

Notation "N '|!' w" := (restrict N w) 
  (at level 40, left associativity).

(*prop determining if every location in array a is in the domain of m*)
Definition indomain_nvm (N: nvmem) (w: warvar) :=
  memberwv_wv_b w (getdomain N).

Definition isdomain_nvm (N: nvmem) (w: warvars) :=
  eq_lists (getdomain N) w eq_warvar.

Definition subset_nvm (N1 N2: nvmem) :=
  (incl (getdomain N1) (getdomain N2)) /\ (forall(l: loc),
                                    In (loc_warvar l) (getdomain N1) ->
                                    (getmap N1) l = (getmap N2) l
                                  ).
(********************************************)
Inductive cconf := (*continuous configuration*)
  ContinuousConf (triple: nvmem * vmem * command).

Notation context := (nvmem * vmem * command).

(*A coercion for cconf doesn't work because it's the same essential type as context.
 So, in practice, to avoid writing the constructor everywhere, I've been using contexts foralleverything, when conceptually a cconf would make more sense.
 It would be nice to just have one type for this.*)

Notation iconf := (context * nvmem * vmem * command).

Definition getcom (C: context) :=
  match C with
    (_, _, out) => out end.

Definition ro := loc * value. (*read observation*)
Definition readobs := list ro.

Notation NoObs := ([]: readobs).

Inductive obs := (*observation*)
  Obs (r: readobs)
| reboot
| checkpoint.
Coercion Obs : readobs >-> obs.

Notation obseq := (list obs). (*observation sequence*)

Open Scope list_scope.

(*helpers for configs*)
Inductive single_com: context -> Prop :=
  SingleCom: forall(N: nvmem) (V: vmem) (l: instruction),
               single_com (N, V, Ins l).

Definition single_com_i (C: iconf) :=
  match C with (_, _, c) =>
  (match c with
    Ins _ => True
  | _ => False end) end.

(*helpers for observations and warvars*)

(*converts from list of read locations to list of
WAR variables
 *)


Fixpoint readobs_warvars (R: readobs) : warvars := 
  match R with
    nil => nil
  | (r::rs) => match r with
               (location, _) => (loc_warvar location)::(readobs_warvars rs)
             end
  end.

Fixpoint readobs_loc (R: readobs): (list loc) := 
  match R with
    nil => nil
| (r::rs) => match r with
             (location, _) => location :: (readobs_loc rs)
           end
  end.


(*relations between continuous and intermittent observations*)
(*Definition reduces (O1 O2: readobs) :=
  (prefix O1 O2*)
Notation "S <= T" := (prefix S T).

(*Where
O1 is a sequence of read observation lists,
where each continguous read observation list is separated from those adjacent to it by a reboot,
and O2 is a read observation list,
prefix_seq determines if each ro list in O1 is a valid
prefix of O2*)
Inductive prefix_seq: obseq -> readobs -> Prop :=
  RB_Base: forall(O: readobs), prefix_seq [Obs O] O
| RB_Ind: forall(O1 O2: readobs) (O1': obseq),
    O1 <= O2 -> prefix_seq O1' O2 -> prefix_seq ([Obs O1] ++ [reboot] ++ O1') O2.

(* Where
O1 is a sequence of ((read observation list sequences), where
each continguous read observation list is separated from those adjacent to it
by a reboot), where each sequence is separated from those adjacent to it by a checkpoint.
ie, each read observation list in a given read observation sequence
occurs within the same checkpointed region as all the other read observation lists in that sequence,
O2 is a read observation list,
prefix_frag determines if each ro list in O1 is a prefix of some FRAGMENT of O2
(where the fragments are separated by the positioning of the checkpoints in O1)
 *)
Inductive prefix_fragment: obseq -> readobs -> Prop :=
  CP_Base: forall(O1: obseq) (O2: readobs), prefix_seq O1 O2 -> prefix_fragment O1 O2
| CP_IND: forall(O1 O1': obseq) (O2 O2': readobs),
    prefix_seq O1 O2 -> prefix_fragment O1' O2' ->
   prefix_fragment (O1 ++ [checkpoint] ++ O1') (O2 ++ O2'). 

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
    ((inl x) <-N) = v ->
    isNV(x) -> (*extra premise to make sure x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N mapV x [((inl x), v)] v
| RD_VAR_V: forall(N: nvmem) (mapV: mem) (x: smallvar) (v: value),
    (mapV (inl x)) = v ->
    isV(x) -> (*extra premise to make sure x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N (Vol mapV) x [((inl x), v)] v
| RD_ARR: forall(N: nvmem) (V: vmem)
           (a: array)
           (index: exp)
           (rindex: readobs)
           (vindex: value)
           (element: el)
           (v: value),
    eeval N V (index) rindex vindex ->
    ((inr element) <-N) = v ->
    (val element) = (El a vindex) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    eeval N V (a[[index]]) (rindex++[((inr element), v)]) v
.

(****************************************************************************)

(**********continuous execution semantics*************************)


(*evaluation relation for commands*)



(*written, read, written before reading*)
Notation the_write_stuff := ((list loc) * (list loc) * (list loc)).

(*consider using a record type so I don't need so many of these*)

Definition getwt (W: the_write_stuff) := match W with (out, _, _ )=> out end.

Definition getrd (W: the_write_stuff) := match W with (_, out , _ )=> out end.

Definition getfstwt (W: the_write_stuff) := match W with (_, _, out )=> out end.

Notation emptysets := ((nil : (list loc)), (nil: (list loc)), (nil: (list loc))).



(***Below, I define an evaluation relation for continuous programs which accumulates
 read/write data as the program evaluates. This makes the trace type more elegant, while
 also containing the same data as the cceval above.
However, the write data does not influence the evaluation of the program, so, if it were not
for the trace type, it wouldn't be clear I would include this here.
It not included in the evaluation relation in the paper.
 **)
(*Single steps, accumulates write data*)
(*Note: program consisting of just a checkpoint is illegal...huh*)

Inductive cceval_w: context -> obseq -> context -> the_write_stuff -> Prop :=
CheckPoint: forall(N: nvmem)
               (V: vmem)
               (c: command)
               (w: warvars),
    cceval_w (N, V, ((incheckpoint w);; c))
             [checkpoint]
             (N, V, c)
             (nil, nil, nil)
| NV_Assign: forall(x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, V, Ins (asgn_sv x e))
             [Obs r]
             ((updateNV N (inl x) v), V, Ins skip)
             ([inl x],  (readobs_loc r), (remove in_loc_b (readobs_loc r) [inl x]))
| V_Assign: forall(x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, (Vol mapV), Ins (asgn_sv x e)) [Obs r]
             (N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
             (nil,  (readobs_loc r), nil)
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
    (val element) = (El a vi) -> (*extra premise to check that inr element
                                        is actually a[vindex] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    cceval_w (N, V, Ins (asgn_arr a ei e))
           [Obs (ri++r)]
           ((updateNV N (inr element) v), V, Ins skip)
           ([inr element], (readobs_loc (ri ++ r)), (remove in_loc_b (readobs_loc (ri ++ r)) [inr element]))
(*valuability and inboundedness of vindex are checked in sameindex*)
| Skip: forall(N: nvmem)
         (V: vmem)
         (c: command),
    cceval_w (N, V, (skip;;c)) [Obs NoObs] (N, V, c) (nil, nil, nil)
| Seq: forall (N N': nvmem)
         (V V': vmem)
         (l: instruction)
         (c: command)
         (o: obs)
         (W: the_write_stuff),
    (forall(w: warvars), l <> (incheckpoint w)) ->
    l <> skip ->
    cceval_w (N, V, Ins l) [o] (N', V', Ins skip) W ->
    cceval_w (N, V, (l;;c)) [o] (N', V', c) W
   (*IP becomes obnoxious if you let checkpoint into the Seq case so I'm outlawing it
    same with skip*) 
| If_T: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> (*yuh doy not writing anything in eeval*)
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c1) (nil, (readobs_loc r), nil)
| If_F: forall(N: nvmem)
         (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    cceval_w (N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (N, V, c2) (nil, (readobs_loc r), nil).

Definition append_write (W1 W2: the_write_stuff) :=
  ((getwt W1) ++ (getwt W2), (getrd W1) ++ (getrd W2), (getfstwt W1) ++ (remove in_loc_b (getrd W1) (getfstwt W2))).
(************************************************************)

(**********intermittent execution semantics*************************)
(*evaluation relation for commands*)
(*accumlates write data as continuous relation does*)
Inductive iceval_w: iconf -> obseq -> iconf -> the_write_stuff -> Prop :=
  CP_PowerFail: forall(k: context) (N: nvmem) (V: vmem) (c: command),
                 iceval_w (k, N, V, c)
                        nil
                        (k, N, (reset V), Ins inreboot) (nil, nil, nil)
 | CP_Reboot: forall(N N': nvmem) (*see below*) (*N is the checkpointed one*)
               (V V': vmem) 
               (c: command), 
     iceval_w ((N, V, c), N', V', Ins inreboot)
            [reboot]
            ((N, V, c), (N U! N'), V, c) (nil, nil, nil)
 | CP_CheckPoint: forall(k: context) (N: nvmem) (V: vmem) (c: command) (w: warvars),
                 iceval_w (k, N, V, ((incheckpoint w);;c))
                        [checkpoint]
                        (((N |! w), V, c), N, V, c) (nil, nil, nil) 
 | CP_NV_Assign: forall(k: context) (x: smallvar) (N: nvmem) (V: vmem) (e: exp) (r: readobs) (v: value),
    eeval N V e r v ->
    isNV(x) -> (*checks x is correct type for NV memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval_w (k, N, V, Ins (asgn_sv x e))
           [Obs r]
           (k, (updateNV N (inl x) v), V, Ins skip)
           ([inl x],  (readobs_loc r), (remove in_loc_b (readobs_loc r) [inl x]))
| CP_V_Assign: forall(k: context) (x: smallvar) (N: nvmem) (mapV: mem) (e: exp) (r: readobs) (v: value),
    eeval N (Vol mapV) e r v ->
    isV(x) -> (*checks x is correct type for V memory*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval_w (k, N, (Vol mapV), Ins (asgn_sv x e))
           [Obs r]
           (k, N, (Vol ((inl x) |-> v ; mapV)), Ins skip)
             (nil,  (readobs_loc r), nil)
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
    (val element) = (El a vi) -> (*extra premise to check that inr element                                        is actually a[vi] *)
(*well-typedness, valuability, inboundedness of vindex are checked in elpred*)
    (isvaluable v) -> (*extra premise to check if v is valuable*)
    iceval_w (k, N, V, Ins (asgn_arr a ei e))
           [Obs (ri++r)]
           (k, (updateNV N (inr element) v), V, Ins skip)
           ([inr element], (readobs_loc (ri ++ r)), (remove in_loc_b (readobs_loc (ri ++ r)) [inr element]))
| CP_Skip: forall(k: context) (N: nvmem)
         (V: vmem)
         (c: command),
    iceval_w (k, N, V, (skip;;c)) [Obs NoObs] (k, N, V, c) (nil, nil, nil)
|CP_Seq: forall (k: context)
         (N: nvmem) (N': nvmem)
         (V: vmem) (V': vmem)
         (l: instruction)
         (c: command)
         (o: obs)
         (W: the_write_stuff),
    iceval_w (k, N, V, Ins l) [o] (k, N', V', Ins skip) W ->
    iceval_w (k, N, V, (l;;c)) [o] (k, N', V', c) W
|CP_If_T: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r true -> 
    iceval_w (k, N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (k, N, V, c1) (nil, (readobs_loc r), nil)
|CP_If_F: forall(k: context) (N: nvmem) (V: vmem)
         (e: exp)
         (r: readobs)
         (c1 c2: command),
    eeval N V e r false ->
    iceval_w (k, N, V, (TEST e THEN c1 ELSE c2)) [Obs r] (k, N, V, c2) (nil, (readobs_loc r), nil).
(*CP_Reboot: I took out the equals premise and instead built it
into the types because I didn't want to define a context equality function*)

(********************************************)
(*helpers that use the evals
Definition el_arrayexp_eq (e: el) (a: array) (eindex: exp) (N: nvmem) (V: vmem) := (*transitions from el type to a[exp] representation*)
  (samearray e a) /\
  exists(r: readobs) (vindex: value), eeval N V eindex r vindex /\
                                 (eq_value (getindexel e) vindex).*)
(******)
Close Scope list_scope.
Close Scope type_scope.
