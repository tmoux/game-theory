From GameTheory Require Import ImpartialGame.
Require Import Coq.Init.Wf.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.
Import Relation_Definitions.

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
Proof.
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

(* Transitive closure of relation adapted from https://madiot.fr/pso/tp6.html *)
Inductive trans {A} (R : relation A) : relation A :=
  | rel_same : forall x y, R x y -> trans R x y
  | rel_trans : forall x y z, R x y -> R y z -> trans R x z.

(* TODO: Understand what is going on here. *)
Lemma Acc_trans (A : Type) (R : relation A) :
  forall x, Acc R x -> Acc (trans R) x.
Proof.
  intros.
  induction H.
  constructor; intros.
  induction H1; auto.
  eapply Acc_inv.
  apply H0.
  apply H2.
  constructor. auto.
Qed.

Theorem wf_trans : forall (A : Type) (R : relation A),
  well_founded R -> well_founded (trans R).
Proof.
  intros A R W x; apply Acc_trans, W.
Qed.

(* In this proof, we need to go back two steps, not just one. *)
(* Therefore inducting on the Wf relation of a + b does not give us a strong enough induction principle. *)
(* Instead we define the transitive closure of this relation, and then prove it is well-founded. *)
(* Then we use this as our induction principle. *)
Lemma sum_losing_is_losing : forall a b x y,
    losing_state a x ->
    losing_state b y ->
    losing_state (a ~+~ b) (x, y).
Proof.
  intros a b.
  enough (forall s, losing_state a (fst s) ->
                    losing_state b (snd s) ->
                    losing_state (a ~+~ b) s) by auto.
  refine (well_founded_induction (wf_trans _ _ (finite_game (a ~+~ b))) _ _); intros [x y] IH ? ?; simpl in *.
  constructor; intros.
  apply moves_in_game_sum in H1 as [[? ?] | [? ?]]; destruct s'; simpl in *; subst.
  - inversion H; subst. specialize H2 with p.
    destruct H2; auto.
    apply trans_to_losing with (s', y).
    apply moves_in_game_sum; left; auto.
    apply IH; auto.
    apply rel_trans with (s, y); repeat (apply moves_in_game_sum; left; auto).
  - inversion H0; subst. specialize H2 with p0.
    destruct H2; auto.
    apply trans_to_losing with (x, s').
    apply moves_in_game_sum; right; auto.
    apply IH; auto.
    apply rel_trans with (x, s); repeat (apply moves_in_game_sum; right; auto).
Qed.

Lemma z_plus_z_is_losing : forall z, losing_state (z ~+~ z) (start z, start z).
Proof.
  intros z.
  enough (forall s, losing_state (z ~+~ z) (s, s)) by easy.
  refine (well_founded_induction (finite_game z) _ _); intros a IH.
  constructor; intros.
  destruct s'.
  apply moves_in_game_sum in H as [[? ?] | [? ?]]; simpl in *; subst.
  - apply trans_to_losing with (p, p).
    apply moves_in_game_sum; right; auto.
    apply IH; auto.
  - apply trans_to_losing with (p0, p0).
    apply moves_in_game_sum; left; auto.
    apply IH; auto.
Qed.

Lemma sum_losing_then_losing : forall x y,
    losing_state (x ~+~ y) (start x, start y) ->
    losing_state x (start x) ->
    losing_state y (start y).
Proof.
  intros.
  destruct (winning_or_losing y (start y)); auto.
  destruct w.
  pose proof (sum_losing_is_losing _ _ (start x) s').
  exfalso; apply (not_both_winning_losing (x ~+~ y) (start x, s')).
  intuition.
  inversion H; subst.
  apply (H4 (start x, s')).
  apply moves_in_game_sum; right; auto.
Qed.
