From GameTheory Require Import ImpartialGame Boolgroup SumGames Equiv.
From Coq Require Import BinNat Nnat.
Require Import Lia.

Open Scope N_scope.
Definition nums_lt : N -> list N :=
  (N.recursion [] (fun n l => n :: l)).

Lemma nums_lt_spec : forall n m,
    In m (nums_lt n) <-> (m < n).
Proof.
  split; intuition.
  - induction n using N.peano_ind.
    inversion H.
    unfold nums_lt in H.
    rewrite N.recursion_succ in H; intuition.
    destruct H. lia.
    fold nums_lt in H.
    apply IHn in H; lia.
  - induction n using N.peano_ind.
    lia.
    unfold nums_lt. rewrite N.recursion_succ; intuition.
    fold nums_lt.
    simpl.
    cut (m < n \/ n = m); [ intros [? | ?]; auto | lia ].
Qed.

Definition Nim (n : N) : impartial_game.
  refine {|
           position := N;
           start := n;
           moves := fun x => nums_lt x;
           finite_game := _
         |}.
  unfold well_founded.
  intros a.
  enough (forall x, Acc (fun next current : N => In next (nums_lt current)) x) by easy.
  induction x using N.peano_ind.
  constructor. simpl. intuition.
  constructor. intros.
  unfold nums_lt in H; rewrite N.recursion_succ in H; intuition.
  simpl in H; fold nums_lt in H.
  destruct H.
  rewrite <- H. assumption.
  apply IHx. assumption.
Defined.

Corollary nim_moves_spec :
  forall {m} (n n' : N),
    valid_move (Nim m) n' n <-> n' < n.
  intros.
  apply nums_lt_spec.
Qed.

Corollary a_not_in_moves :
  forall {m} (n : N), valid_move (Nim m) n n -> False.
  intros ? ?. rewrite nim_moves_spec. lia.
Qed.

Lemma nim_0_losing : get_outcome_b (Nim 0) 0 = false.
  rewrite get_outcome_b_unfold.
  simpl.
  reflexivity.
Qed.

Lemma xor_pos_3 : forall x p a b c,
    N.pos p = x ->
    N.lxor (N.lxor a b) c = x ->
    N.testbit a (N.log2 x) = true \/
      N.testbit b (N.log2 x) = true \/
      N.testbit c (N.log2 x) = true.
  intros.
  destruct (N.testbit a (N.log2 x)) eqn:?; auto.
  destruct (N.testbit b (N.log2 x)) eqn:?; auto.
  destruct (N.testbit c (N.log2 x)) eqn:?; auto.
  assert (N.testbit x (N.log2 x) = true).
  apply N.bit_log2. subst. discriminate.
  rewrite <- H0 in *.
  repeat (rewrite N.lxor_spec in H1).
  subst.
  rewrite Heqb0, Heqb1, Heqb2 in H1. simpl in H1. discriminate.
Qed.

Lemma log2_bits_diff_lt : forall k A B,
    (forall m, (k < m) -> N.testbit A m = false) ->
    (forall m, (k < m) -> N.testbit B m = false) ->
    N.testbit A k = false ->
    N.testbit B k = true ->
    (A < B).
  intros.
  destruct A eqn:?.
  destruct B; intuition; constructor.
  assert (N.log2 B = k). apply N.log2_bits_unique; auto.
  assert (N.log2 A < k).
  pose proof (N.lt_trichotomy (N.log2 A) k).
  destruct H4 as [Hlt | [Heq | Hgt]].
  auto.
  rewrite <- Heq in H1. rewrite Heqn in H1. rewrite N.bit_log2 in H1.
  discriminate.
  intuition. discriminate.
  specialize H with (N.log2 (N.pos p)).
  rewrite N.bit_log2 in H; intuition; try discriminate.
  rewrite Heqn in Hgt.
  apply H in Hgt.
  discriminate.
  subst.
  apply N.log2_lt_cancel; auto.
Qed.

Lemma sub_pow2 : forall A n,
    N.testbit A n = true ->
    N.testbit (A - 2 ^ n) n = false /\
    forall k, k <> n -> N.testbit (A - 2 ^ n) k = N.testbit A k.
  intros.
  assert (Hc : N.ldiff (2 ^ n) A = 0).
  {
    rewrite N.bits_inj with _ 0. reflexivity.
    unfold N.eqf; intros.
    rewrite N.ldiff_spec.
    destruct (N.eq_decidable n0 n).
    subst. rewrite N.pow2_bits_true. rewrite H. simpl. reflexivity.
    rewrite N.pow2_bits_false; auto.
  }
  split.
  - rewrite N.sub_nocarry_ldiff; auto.
    rewrite N.ldiff_spec.
    rewrite H. rewrite N.pow2_bits_true. reflexivity.
  - intros k Hk.
    rewrite N.sub_nocarry_ldiff; auto.
    rewrite N.ldiff_spec.
    rewrite N.pow2_bits_false; auto. simpl. rewrite andb_true_r. reflexivity.
Qed.

Definition P (A B k : N) : Prop :=
  (N.log2 A < N.log2 B + k) \/
    exists a b,
      (forall m, (N.log2 A - k < m) -> N.testbit a m = false) /\
        (forall m, (N.log2 A - k < m) -> N.testbit b m = false) /\
        (forall m, (N.log2 B < m) -> N.testbit a m = N.testbit b m) /\
        N.testbit a (N.log2 B) = false /\
        N.testbit b (N.log2 B) = true /\
        ((a < b) -> (N.lxor A B < A)).

Lemma Hind : forall A B, P A B 0 -> forall k, P A B k.
  intros A B P0.
  refine (N.peano_ind _ _ _); auto. clear P0.
  - intros n IH.
    destruct IH as [IH | [A' [B' [? [? [? [? [? ?]]]]]]]].
    left. lia.
    destruct (N.lt_decidable (N.log2 A) (N.log2 B + N.succ n)).
    left. lia.
    right.
    destruct (N.testbit A' (N.log2 A - n)) eqn:?.
    + pose proof (Heqb).
      rewrite H1 in H6; [| lia].
      exists (A' - (2 ^ (N.log2 A - n))), (B' - (2 ^ (N.log2 A - n))).
      pose proof (sub_pow2 A' (N.log2 A - n)) as HA'.
      apply HA' in Heqb.
      pose proof (sub_pow2 B' (N.log2 A - n)) as HB'.
      apply HB' in H6. clear HA' HB'.
      rename Heqb into HA', H6 into HB'.
      destruct HA' as [HA1 HA2].
      destruct HB' as [HB1 HB2].
      intuition.
      * assert (m = (N.log2 A - n) \/ (m > N.log2 A - n)). lia.
        destruct H7. subst. assumption. rewrite HA2. apply H; lia. lia.
      * assert (m = (N.log2 A - n) \/ (m > N.log2 A - n)). lia.
        destruct H7. subst. assumption. rewrite HB2. apply H0; lia. lia.
      * destruct (N.eq_decidable m (N.log2 A - n)).
        subst. rewrite HA1. rewrite HB1. reflexivity.
        rewrite HA2, HB2; try lia. apply H1; assumption.
      * rewrite HA2. apply H2. lia.
      * rewrite HB2. apply H3. lia.
      * apply H4. lia.
    + exists A', B'.
      intuition.
      assert (m = (N.log2 A - n) \/ (m > N.log2 A - n)). lia.
      destruct H7; [subst; auto | apply H; lia ].
      assert (m = (N.log2 A - n) \/ (m > N.log2 A - n)). lia.
      destruct H7.
      rewrite H1 in Heqb; [ subst; assumption | lia ].
      apply H0; lia.
Qed.

Lemma xor_lt : forall A B,
    (B <> 0) ->
    N.testbit A (N.log2 B) = true ->
    (N.lxor A B < A).
  intros.
  pose proof (N.bits_above_log2 B).
  pose proof (N.bits_above_log2 A).
  assert (forall m, (N.log2 B < m) -> N.testbit (N.lxor A B) m = N.testbit A m).
  { intros m Hm. rewrite N.lxor_spec. rewrite H1; auto. rewrite xorb_false_r. reflexivity. }
  assert (N.testbit (N.lxor A B) (N.log2 B) = false).
  { rewrite N.lxor_spec. rewrite H0. rewrite N.bit_log2; auto. }

  assert (N.log2 B <= N.log2 A).
  { destruct (N.le_decidable (N.log2 B) (N.log2 A)); auto.
  pose proof (N.bits_above_log2 A (N.log2 B)).
  rewrite H6 in H0. discriminate. lia.
  }

  assert (P0 : P A B 0). {
         right. exists (N.lxor A B), A.
         intuition.
         specialize H3 with m. rewrite H2 in H3. apply H3. lia. lia.
         apply H2. lia. }

  pose proof (Hind A B P0 (N.log2 A - N.log2 B)).
  destruct H6 as [H6 | [A' [B' [? [? [? [? [? ?]]]]]]]]; [ lia | ].
  apply H11.
  replace (N.log2 A - (N.log2 A - N.log2 B)) with (N.log2 B) in *; [| lia].
  apply log2_bits_diff_lt with (N.log2 B); auto.
Qed.

Lemma nim_xor_move (x : N) : forall A B,
    (B <> 0) ->
    N.testbit A (N.log2 B) = true ->
    valid_move (Nim x) (N.lxor A B) A.
  intros.
  apply (xor_lt A B) in H; auto.
  unfold valid_move.
  simpl.
  apply nums_lt_spec; auto.
Qed.

(* Here we need to reason about xor. *)
(* If the xor of x, y, z is 0, then any move will make the xor nonzero, *)
(* which by the IH, means that the state must be winning. *)
(* If the xor is nonzero, then we pick the one with a highest one-bit (log2) that *)
(* matches that of the xor (ther must be at least one). *)
(* Then we change its value to (x xor s), which we know to be strictly less than x *)
(* since it has a strictly lower log2 value. *)
(* This makes the xor zero, so by the IH, the state is losing. *)
Theorem nim_sum_losing_3 :
  forall x y z, losing_state ((Nim x) ~+~ (Nim y) ~+~ (Nim z)) (x, y, z) <-> (N.lxor (N.lxor x y) z) = 0.
  intros.
  enough (forall s : position ((Nim x ~+~ Nim y) ~+~ Nim z),
             match s with
             | (a, b, c) => losing_state ((Nim x ~+~ Nim y) ~+~ Nim z) (a, b, c) <->
                                     N.lxor (N.lxor a b) c = 0 end).
  specialize H with (x, y, z). apply H.
  apply (well_founded_induction (finite_game ((Nim x ~+~ Nim y) ~+~ Nim z))).
  intros [[A B] C] IH.
  split; intros.
  - match goal with
    | |- ?x = _ => destruct x eqn:?; auto
    end.
    exfalso; eapply not_both_winning_losing. split; [| apply H].
    destruct (xor_pos_3 _ _ A B C eq_refl Heqn) as [Hp | [Hp | Hp]].
    + apply (nim_xor_move x) in Hp; [ | discriminate ].
      match goal with
      | |- winning_state ?g ?cur => assert (Hv : valid_move g (N.lxor A (N.pos p), B, C) cur);
                                  [ repeat valid_move_sum_left |]
      end.
      apply trans_to_losing with (N.lxor A (N.pos p), B, C); auto.
      (* Show losing by IH *)
      specialize IH with (N.lxor A (N.pos p), B, C).
      apply IH; auto.
      rewrite <- Heqn.
      XorSolver.boolgroup_rw N.lxor 0.
    + apply (nim_xor_move y) in Hp; [| discriminate ].
      match goal with
      | |- winning_state ?g ?cur => assert (Hv : valid_move g (A, N.lxor B (N.pos p), C) cur);
                                  [ valid_move_sum_left; valid_move_sum_right | ]
      end.
      apply trans_to_losing with (A, N.lxor B (N.pos p), C); auto.
      (* Show losing by IH *)
      specialize IH with (A, N.lxor B (N.pos p), C).
      apply IH; auto.
      rewrite <- Heqn.
      XorSolver.boolgroup_rw N.lxor 0.
    + apply (nim_xor_move z) in Hp; [| discriminate ].
      match goal with
      | |- winning_state ?g ?cur => assert (Hv : valid_move g (A, B, N.lxor C (N.pos p)) cur);
                                  [ valid_move_sum_right |]
      end.
      apply trans_to_losing with (A, B, N.lxor C (N.pos p)); auto.
      (* Show losing by IH *)
      specialize IH with (A, B, N.lxor C (N.pos p)).
      apply IH; auto.
      rewrite <- Heqn.
      XorSolver.boolgroup_rw N.lxor 0.
    (* Lemma: since p is positive, one of A, B, C has the same highest bit as p. *)
    (* WLOG suppose it's A. Then change A to (A ^ (A ^ B ^ C)). *)
    (* First of all, this is a valid move, since the log2 of (A ^ B ^ C) is the same *)
    (* as the log2 of A, so their xor must have strictly smaller log2 *)
    (* (except for when A = 1...). *)
    (* Second, this leads to a losing state, since the xor is (B ^ C) ^ B ^ C = 0. *)
    (* And similarly for B or C... *)
  - constructor; intros [[a b] c] Hm.
    specialize IH with (a, b, c).
    pose proof Hm as Hm'.
    apply IH in Hm'.
    apply moves_in_game_sum in Hm as [[? ?] | [? ?]]; simpl in *; subst.
    apply moves_in_game_sum in H0 as [[? ?] | [? ?]]; simpl in *; subst.
    + destruct (winning_or_losing (((Nim x ~+~ Nim y) ~+~ Nim z)) (a, B, C)); auto.
    apply Hm' in l.
    (* Contradiction: this implies a = A, but since a is a valid move from A, *)
    (* it cannot be equal to A. *)
    assert (a = A).
    { apply N.lxor_eq_0_iff. rewrite <- N.lxor_0_r.
      rewrite <- l at 1; rewrite <- H at 1.
      (* Tedious goal: kill with boolgroup tactic. *)
      XorSolver.boolgroup_rw N.lxor 0. }
      match goal with
      | H : valid_move _ ?x ?y |- _ => subst; apply a_not_in_moves in H; contradiction H
      end.
    + destruct (winning_or_losing (((Nim x ~+~ Nim y) ~+~ Nim z)) (A, b, C)); auto.
      apply Hm' in l.
      assert (b = B).
      { apply N.lxor_eq_0_iff. rewrite <- N.lxor_0_r.
        rewrite <- l at 1; rewrite <- H at 1.
        (* Tedious goal: kill with boolgroup tactic. *)
        XorSolver.boolgroup_rw N.lxor 0. }
      match goal with
      | H : valid_move _ ?x ?y |- _ => subst; apply a_not_in_moves in H; contradiction H
      end.
    + inversion H1; subst.
      destruct (winning_or_losing (((Nim x ~+~ Nim y) ~+~ Nim z)) (A, B, c)); auto.
      apply Hm' in l.
      assert (c = C).
      { apply N.lxor_eq_0_iff. rewrite <- N.lxor_0_r.
        rewrite <- l at 1; rewrite <- H at 1.
        (* Tedious goal: kill with boolgroup tactic. *)
        XorSolver.boolgroup_rw N.lxor 0. }
      match goal with
      | H : valid_move _ ?x ?y |- _ => subst; apply a_not_in_moves in H; contradiction H
      end.
Qed.

Theorem nim_sum_equiv :
  forall x y, (Nim x) ~+~ (Nim y) == Nim (N.lxor x y).
  intros.
  unfold equiv.
  apply nim_sum_losing_3.
  simpl.
  XorSolver.boolgroup_rw N.lxor 0.
Qed.

Lemma nim_zero_is_zero : Nim 0 == zero.
  unfold equiv.
  constructor; intros s H.
  apply moves_in_game_sum in H.
  destruct H as [[? ?] | [? ?]]; simpl in *.
  inversion H.
  inversion H.
Qed.

Definition sum_list := fold_right sum_game zero.
Theorem nim_sum_list :
  forall (l : list N), sum_list (map Nim l) == Nim (fold_right N.lxor 0 l).
  induction l.
  simpl.
  symmetry; apply nim_zero_is_zero.
  simpl.
  rewrite IHl.
  apply nim_sum_equiv.
Qed.

Print Assumptions nim_sum_equiv.
Print Assumptions nim_sum_list.

Goal (Nim 1 ~+~ Nim 2 ~+~ Nim 3 == Nim 0).
  repeat (rewrite nim_sum_equiv).
  simpl.
  reflexivity.
Qed.
