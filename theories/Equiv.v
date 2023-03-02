From GameTheory Require Import ImpartialGame SumGames Bijection.
From Coq Require Import Morphisms RelationClasses Relations.

Definition equiv (a b : impartial_game) := losing_state (a ~+~ b) (start a, start b).
Notation "a == b" := (equiv a b) (at level 50).

Lemma bijection_equiv : forall a b, a ~~ b -> a == b.
  intros.
  destruct H.
  enough (forall s, losing_state (a ~+~ b) (s , f s)).
  { unfold equiv; rewrite <- H3; apply H4. }
  refine (well_founded_induction (finite_game a) _ _); intros x IH.
  constructor; intros.
  apply moves_in_game_sum in H4; destruct H4 as [[? ?] | [? ?]].
  - destruct s'. simpl in *. subst.
    apply trans_to_losing with (p, (f p)).
    apply moves_in_game_sum; right. simpl; intuition.
    apply IH; auto.
  - destruct s'; simpl in *; subst.
    apply trans_to_losing with (g p0, p0).
    apply moves_in_game_sum; left; simpl; intuition.
    replace x with (g (f x)); [| apply H0].
    apply H2; auto.
    replace (g p0, p0) with (g p0, f (g p0)).
    apply IH. replace x with (g (f x)). apply H2; auto.
    rewrite H0. reflexivity.
    rewrite H. reflexivity.
Qed.

Lemma sum_comm_equiv : forall a b, a ~+~ b == b ~+~ a.
Proof.
  auto using bijection_equiv, sum_comm_bijec.
Qed.

Lemma sum_assoc_equiv : forall a b c, (a ~+~ (b ~+~ c)) == ((a ~+~ b) ~+~ c).
Proof.
  auto using bijection_equiv, sum_assoc_bijec.
Qed.

Lemma is_losing_equiv : forall a b, a == b -> losing_state a (start a) -> losing_state b (start b).
  intros.
  auto using (sum_losing_then_losing a).
Qed.

#[export] Instance equiv_reflexive : Reflexive equiv.
  unfold Reflexive.
  intros.
  apply bijection_equiv.
  reflexivity.
Qed.

#[export] Instance equiv_symmetric : Symmetric equiv.
  unfold Symmetric.
  intros.
  unfold equiv in *.
  pose proof (sum_comm_bijec x y) as Hsym.
  apply (is_losing_bijec _ _ Hsym) in H; assumption.
Qed.

#[export] Instance sum_proper_r {z : impartial_game}: Proper (equiv ==> equiv) (sum_game z).
  unfold Proper, respectful; intros.
  unfold equiv in *.
  simpl.
  assert (Heq : (z ~+~ z) ~+~ (x ~+~ y) ~~ ((z ~+~ x) ~+~ (z ~+~ y))).
  {
    rewrite <- (sum_assoc_bijec z z (x ~+~ y)).
    rewrite (sum_assoc_bijec z x y).
    rewrite (sum_comm_bijec z x).
    rewrite <- (sum_assoc_bijec x z y).
    rewrite (sum_assoc_bijec z x (z ~+~ y)).
    rewrite (sum_comm_bijec z x).
    reflexivity.
  }
  apply (is_losing_bijec _ _ Heq).
  simpl.
  apply sum_losing_is_losing; auto using z_plus_z_is_losing.
Qed.

#[export] Instance equiv_transitive : Transitive equiv.
  unfold Transitive.
  intros ? ? ? Hxy Hyz.
  unfold equiv in *.
  apply sum_losing_then_losing with (x := y ~+~ y).
  assert (Heq: (x ~+~ y) ~+~ (y ~+~ z) == (y ~+~ y) ~+~ (x ~+~ z)).
  {
    apply bijection_equiv.
    rewrite (sum_comm_bijec x y).
    rewrite <- (sum_assoc_bijec y x (y ~+~ z)).
    rewrite (sum_assoc_bijec x y z).
    rewrite (sum_comm_bijec x y).
    rewrite <- (sum_assoc_bijec y x z).
    rewrite (sum_assoc_bijec y y (x ~+~ z)).
    reflexivity.
  }
  simpl; apply (is_losing_equiv _ _ Heq).
  simpl.
  apply sum_losing_is_losing; auto.
  simpl; apply z_plus_z_is_losing.
Qed.

#[export] Instance equiv_equiv : Equivalence equiv.
Proof.
  constructor;
    [ exact equiv_reflexive |
      exact equiv_symmetric |
      exact equiv_transitive ].
Qed.


#[export] Instance sum_proper : Proper (equiv ==> equiv ==> equiv) sum_game.
  unfold Proper, respectful; intros.
  rewrite <- H0.
  rewrite (sum_comm_equiv x x0).
  rewrite (sum_comm_equiv y x0).
  rewrite H.
  reflexivity.
Qed.
