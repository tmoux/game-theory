From GameTheory Require Import ImpartialGame.
Require Import Coq.Init.Wf.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.

Definition cg_pair_order {cg1 cg2} :=
  symprod _ _ (valid_move cg1) (valid_move cg2).
Definition cg_pair_order_wf {cg1 cg2} : well_founded cg_pair_order :=
  wf_symprod _ _ _ _ (finite_game cg1) (finite_game cg2).

Definition sum_game (a b : impartial_game) : impartial_game.
  (* Adapted from https://github.com/arthuraa/poleiro/blob/master/theories/CGT2.v *)
  refine {|
      position := position a * position b;
      start := (start a, start b);
      moves pos := map (fun s => (s, snd pos)) (moves a (fst pos)) ++
                   map (fun s => (fst pos, s)) (moves b (snd pos));
    |}.
  match goal with
  | |- well_founded ?R =>
      assert (EQ : RelationClasses.relation_equivalence R cg_pair_order)
  end.
  { intros [pos1' pos2'] [pos1 pos2]. split.
    - intros H.
      apply in_app_or in H.
      repeat rewrite in_map_iff in H.
      destruct H as [(pos1'' & H1 & H2) | (pos2'' & H1 & H2)];
        simpl in *; inversion H1; subst; clear H1;
        constructor; auto.
    - intros H.
      inversion H as [? ? H' ?|? ? H']; subst; clear H;
        rewrite in_app_iff; repeat rewrite in_map_iff;
        simpl; eauto. }
  rewrite EQ.
  apply cg_pair_order_wf.
Defined.

Notation "a ~+~ b" := (sum_game a b) (at level 31, left associativity).

Lemma moves_in_game_sum : forall a b (s s' : position (a ~+~ b)),
    valid_move (a ~+~ b) s' s <->
      (valid_move a (fst s') (fst s) /\ snd s' = snd s) \/
      (valid_move b (snd s') (snd s) /\ fst s' = fst s).
  intros.
  split; intros; destruct s, s'.
  - unfold valid_move in H. simpl in H.
    apply in_app_or in H.
    destruct H; rewrite in_map_iff in H; destruct H as [x [H1 H2]];
    [ left | right ]; inversion H1; subst; auto.
  - simpl in *.
    unfold valid_move. simpl.
    apply in_or_app.
    destruct H as [[H1 H2] | [H1 H2]]; subst;
      [ left | right ]; apply in_map_iff; [ exists p1 | exists p2 ]; auto.
Qed.
