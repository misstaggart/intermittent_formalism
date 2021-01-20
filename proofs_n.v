Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool Init.Nat Arith.Arith Arith.EqNat
     Init.Datatypes Strings.String Program Logic.FunctionalExtensionality.
Require Export Coq.Strings.String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq fintype ssrnat ssrfun path.
From TLC Require Import LibTactics LibLogic.
From Coq_intermittent Require Export programs semantics algorithms lemmas_1
     lemmas_0 proofs_0. (*shouldn't have to import both of these*)

(*stuff to do with the nv mems*)

Lemma nvmem_eq {N1 N2} : (getmap N1) =1 (getmap N2) -> N1 = N2.
  intros Hm. destruct N1 as [m1 d1 H1].
  destruct N2 as [m2 d2 H2].
  simpl in Hm.
  apply functional_extensionality_dep in Hm. subst.
  suffices: d1 = d2.
  move => Heq. subst.
  move: (proof_irrelevance H1 H2) => Heq. by subst.
destruct H1 as [Hsv1 [Har1 [ Hsort1 Hu1] ] ].
destruct H2 as [Hsv2 [Har2 [Hsort2 Hu2] ] ].
apply sorted_sort in Hsort2; try apply loctrans .
apply sorted_sort in Hsort1; try apply loctrans .
rewrite- Hsort1. rewrite - Hsort2.
apply/leqlocP.
apply/allP.
move => x Hmaybe.
move: (count_uniq_mem x Hu1) (count_uniq_mem x Hu2) =>
one two.
simpl.
rewrite one. rewrite two.
destruct x as [sv | el].
destruct (inl sv \in d1) eqn: Hbool;
remember Hbool as Heq; clear HeqHeq.
apply (Hsv1 sv) in Hbool.
apply (Hsv2 sv) in Hbool. rewrite Hbool. by rewrite Heq.
apply negbT in Hbool.
move: (Hsv1 sv) => [Hsv10 Hsv11].
move: (Hsv2 sv) => [Hsv20 Hsv21].
move/contra: Hsv10 => Hsv10.
move/contra: Hsv21 => Hsv21.
apply Hsv10 in Hbool.
apply Hsv21 in Hbool.
rewrite Heq. apply/eqP.
symmetry. move/negbTE: Hbool => work.
  by rewrite work.
  remember el as el1.
destruct el1 as [a1 i].
assert (equal_index el a1 i) as Heqind.
unfold equal_index. subst; by split.
subst. move: (gen_locs_works Heqind) => Hin.
rewrite mem_cat in Hmaybe. move/ orP : Hmaybe => [Hd1 | Hd2]. rewrite Hd1.
assert (intersect (generate_locs a1) d1) as Hint.
  remember (inr (El a1 i)) as el.
  exists el. split; try assumption.
  move: (Har1 a1) => [Har10 Har11].
  move: (Har2 a1) => [Har20 Har21].
  apply Har11 in Hint. apply Har20 in Hint.
  apply/eqP. symmetry.
  apply Hint in Hin. by rewrite Hin.
assert (intersect (generate_locs a1) d2) as Hint.
  remember (inr (El a1 i)) as el.
  exists el. split; try assumption.
  move: (Har1 a1) => [Har10 Har11].
  move: (Har2 a1) => [Har20 Har21].
  apply Har21 in Hint. apply Har10 in Hint.
  apply/eqP. symmetry. 
  apply Hint in Hin. rewrite Hin.
 by rewrite Hd2.
Qed.
