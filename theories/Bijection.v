From GameTheory Require Import ImpartialGame SumGames.
From Coq Require Import Morphisms RelationClasses.

Inductive bijection : impartial_game -> impartial_game -> Prop :=
  ex_bijection : forall (a b : impartial_game)
                     (f : position a -> position b)
                     (g : position b -> position a),
                     (forall x, f (g x) = x) ->
                     (forall x, g (f x) = x) ->
                     (forall s s', valid_move a s' s -> valid_move b (f s') (f s)) ->
                     (forall s s', valid_move b s' s -> valid_move a (g s') (g s)) ->
                     f (start a) = start b ->
                     bijection a b.

Check bijection_ind.
Notation "a ~~ b" := (bijection a b) (at level 50).

#[export] Instance bijection_reflexive : Reflexive bijection.
  unfold Reflexive; intros a.
  apply (ex_bijection a a (fun x => x) (fun x => x)); auto.
Qed.

#[export] Instance bijection_symmetric : Symmetric bijection.
  unfold Symmetric; intros.
  destruct H.
  apply (ex_bijection _ _ g f); auto.
  rewrite <- H3. rewrite H0. reflexivity.
Qed.

#[export] Instance bijection_transitive : Transitive bijection.
  unfold Transitive; intros.
  destruct H as [a b f1 g1 ?].
  destruct H0 as [b c f2 g2 ?].
  apply (ex_bijection a c (fun s => f2 (f1 s)) (fun s => g1 (g2 s))); intuition.
  rewrite H. rewrite H0. reflexivity.
  rewrite H5. rewrite H1. reflexivity.
  rewrite <- H8. rewrite <- H4. reflexivity.
Qed.

#[export] Instance bijection_equiv : Equivalence bijection.
Proof.
  constructor;
    [ exact bijection_reflexive |
      exact bijection_symmetric |
      exact bijection_transitive ].
Qed.

Lemma sum_comm_bijec : forall a b, a ~+~ b ~~ b ~+~ a.
Proof.
  intros.
  apply (ex_bijection (a ~+~ b) (b ~+~ a) (fun s => (snd s, fst s)) (fun s => (snd s, fst s))); simpl; auto using surjective_pairing;
  intros [x y] [x' y'] H; simpl;
  repeat (apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *; subst;
  apply moves_in_game_sum; [right | left]; auto).
Qed.

Lemma sum_assoc_bijec : forall a b c, (a ~+~ (b ~+~ c)) ~~ ((a ~+~ b) ~+~ c).
  intros.
  apply (ex_bijection (a ~+~ (b ~+~ c)) ((a ~+~ b) ~+~ c)
           (fun s => match s with (x, (y, z)) => ((x, y), z) end)
           (fun s => match s with ((x, y), z) => (x, (y, z)) end)); simpl in *; intuition.
  - destruct s' as [x [y z]]. apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *. inversion H0; subst.
    apply moves_in_game_sum; left; intuition; simpl.
    apply moves_in_game_sum; left; intuition; simpl.

    apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *; subst.
    apply moves_in_game_sum; left; intuition; simpl.
    apply moves_in_game_sum; right; intuition; simpl.

    apply moves_in_game_sum; right; intuition; simpl.
  - destruct s' as [[x y] z]. apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *. inversion H0; subst.
    apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *; subst.
    apply moves_in_game_sum; left; intuition; simpl.
    apply moves_in_game_sum; right; intuition; simpl.
    apply moves_in_game_sum; left; intuition; simpl.
    inversion H0; subst.
    apply moves_in_game_sum; right; intuition; simpl.
    apply moves_in_game_sum; right; intuition; simpl.
Qed.

Lemma is_losing_bijec : forall a b, a ~~ b -> losing_state a (start a) -> losing_state b (start b).
  intros.
  destruct H.
  enough (forall s, (losing_state a s -> losing_state b (f s)) /\ (winning_state a s -> winning_state b (f s))).
  specialize H5 with (start a).
  apply H5 in H0.
  rewrite <- H4. intuition.
  refine (well_founded_induction (finite_game a) _ _).
  intros s IH.
  split.
  - intros Hlosing.
    constructor; intros.
    specialize IH with (g s').
    assert (valid_move a (g s') s).
    { rewrite <- H1. apply H3; assumption. }
    destruct IH; auto.
    rewrite H in H8.
    apply H8.
    destruct Hlosing.
    specialize H9 with (g s'). auto.
  - intros Hwinning.
    destruct Hwinning.
    apply trans_to_losing with (f s').
    apply H2; auto.
    specialize IH with s'.
    destruct IH; auto.
Qed.

#[export] Instance bijec_sum_proper_r {c : impartial_game}: Proper (bijection ==> bijection) (sum_game c).
  unfold Proper, respectful.
  intros. destruct H.
  apply (ex_bijection (c ~+~ a) (c ~+~ b)
           (fun s => match s with (z, x) => (z, f x) end)
           (fun s => match s with (z, y) => (z, g y) end)); simpl in *.
  - intros [z y]. rewrite H. reflexivity.
  - intros [z x]. rewrite H0. reflexivity.
  - intros [z x] [z' x']. intros.
    apply moves_in_game_sum in H4. destruct H4 as [[? ?] | [? ?]]; simpl in *; subst.
    apply moves_in_game_sum; left; intuition.
    apply moves_in_game_sum; right; simpl; intuition.
  - intros [z y] [z' y']. intros.
    apply moves_in_game_sum in H4. destruct H4 as [[? ?] | [? ?]]; simpl in *; subst.
    apply moves_in_game_sum; left; intuition.
    apply moves_in_game_sum; right; simpl; intuition.
  - rewrite H3. reflexivity.
Qed.

#[export] Instance bijec_sum_proper : Proper (bijection ==> bijection ==> bijection) sum_game.
  unfold Proper, respectful; intros.
  rewrite <- H0.
  rewrite (sum_comm_bijec x x0).
  rewrite (sum_comm_bijec y x0).
  rewrite H.
  reflexivity.
Qed.
