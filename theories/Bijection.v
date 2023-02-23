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
