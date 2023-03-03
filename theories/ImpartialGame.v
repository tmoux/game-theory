(** * Defining Impartial Games *)

From GameTheory Require Export In.
From Coq Require Export List.
Export ListNotations.

(** We define an impartial game as the following structure: *)
(** - A type of positions, *)
(** - A start position, *)
(** - A function mapping states to valid next moves, *)
(** - A proof that the induced relation between moves is well founded (corresponding to the fact that any game must terminate). *)
(** This is adapted from a #<a href="http://poleiro.info/posts/2013-09-08-an-introduction-to-combinatorial-game-theory.html">blog post </a># from the Polero blog. *)

Inductive impartial_game :=
  ImpartialGame {
      position: Type;
      start : position;
      moves : position -> list position;
      valid_move next current := In next (moves current);
      finite_game : well_founded valid_move;
    }.
Check ImpartialGame.

(** We define the notion of _winning_ and _losing_ states. *)
(** A state is winning if there is at least one transition to a losing state, *)
(** and a state is losing if all transitions are to a winning state. *)
(** The advantage of defining winning and losing like this is that it is quite natural and aligns with how winning and losing is usually understood. *)
(** One downside is that it is not immediately clear that these two notions are mutually exclusive, or that a state must be either winning or losing. *)

Section Winning.
  Variable game: impartial_game.
  Let S := position game.

  Inductive winning_state : S -> Prop :=
  | trans_to_losing : forall (s s' : S), valid_move game s' s -> losing_state s' -> winning_state s
  with losing_state : S -> Prop :=
  | all_winning : forall (s : S), (forall (s' : S), valid_move game s' s -> winning_state s') -> losing_state s.

  (** A state cannot be both winning and losing at the same time. *)
  Lemma not_both_winning_losing : forall (s : S), ~ ((winning_state s) /\ (losing_state s)).
    apply (well_founded_induction (finite_game game)); intuition.
    match goal with
    | [ H : forall y, _ -> _ -> False, H1 : winning_state ?x, H2: losing_state ?x |- _ ] =>
        destruct H1 as [s s' H1]; destruct H2; apply H with s'; auto
    end.
  Qed.
  Hint Resolve not_both_winning_losing : core.

  Lemma losing_implies_not_winning : forall (s : S), losing_state s -> ~ winning_state s.
    intros s H.
    pose (not_both_winning_losing s).
    unfold not in *.
    intuition.
  Qed.


  Definition get_outcome_b : S -> bool :=
  Fix (finite_game game) (fun _ : position game => bool)
    (fun (s : position game)
      (F : forall y : position game, valid_move game y s -> bool) =>
    existsb_In (moves game s)
      (fun (x : position game) (HIn : In x (moves game s)) => negb (F x HIn))).


  Lemma get_outcome_b_ext:
    forall
      (x : S)
      (f g : forall y : position game, valid_move game y x -> bool),
    (forall (y : position game) (p : valid_move game y x),
      f y p = g y p) ->
    existsb_In (moves game x)
      (fun (x0 : position game) (HIn : In x0 (moves game x)) =>
        negb (f x0 HIn)) =
      existsb_In (moves game x)
        (fun (x0 : position game) (HIn : In x0 (moves game x)) =>
          negb (g x0 HIn)).
    intros.
    eapply existsb_In_ext.
    intuition.
    apply f_equal.
    intuition.
  Qed.

  Lemma get_outcome_b_unfold : forall (s : S),
    get_outcome_b s = existsb_In (moves game s) (fun x P => negb (get_outcome_b x)).
    intros.
    unfold get_outcome_b.
    rewrite Fix_eq.
    reflexivity.
    apply get_outcome_b_ext.
  Qed.

  Lemma w_reflect':
    forall s, (get_outcome_b s = true -> winning_state s) /\
                (get_outcome_b s = false -> losing_state s).
    apply (well_founded_induction (finite_game game)); intuition.
    - rewrite get_outcome_b_unfold in H0.
      rewrite existsb_In_existsb with (g := fun x => negb (get_outcome_b x)) in H0; auto.
      apply existsb_exists in H0.
      destruct H0 as [y [Hy1 Hy2]].
      econstructor. apply Hy1. apply H; auto. apply negb_true_iff in Hy2. assumption.
    - rewrite get_outcome_b_unfold in H0.
      constructor. intros.
      apply H; auto.

      rewrite existsb_In_existsb with (g := fun x => negb (get_outcome_b x)) in H0; auto.
      eapply existsb_false in H0. apply negb_false_iff in H0. apply H0.
      assumption.
  Qed.

  Lemma w_reflect:
    forall s, reflect (winning_state s) (get_outcome_b s).
    intros.
    destruct (get_outcome_b s) eqn:?; constructor.
    - apply w_reflect'. assumption.
    - assert (losing_state s). apply w_reflect'. assumption.
      apply losing_implies_not_winning. assumption.
  Qed.

  Lemma winning_or_losing : forall s, winning_state s + losing_state s.
    intros.
    pose proof (w_reflect' s) as [? ?].
    destruct (get_outcome_b s); auto.
  Qed.

  (** If we have two predicates P and Q that are disjoint and at least one is true, then P <-> ~ Q and Q <-> ~ P. *)
  Lemma dec_disjoint_implies_negation {A : Type} : forall (P Q : A -> Prop), (forall s, ~ (P s /\ Q s)) -> (forall s, P s + Q s) -> (forall s, (P s <-> ~ Q s) /\ (Q s <-> ~ P s)).
    intros ? ? H1 H2 s.
    specialize (H1 s).
    specialize (H2 s).
    intuition.
  Qed.

  Lemma losing_equiv_not_winning : forall s, losing_state s <-> ~ winning_state s.
    apply dec_disjoint_implies_negation, winning_or_losing.
    apply not_both_winning_losing.
  Qed.

  Lemma winning_decidable : forall s, winning_state s + ~ (winning_state s).
    intros.
    destruct (w_reflect s); auto.
  Qed.

  Lemma get_outcome_b_false :
    forall s, (get_outcome_b s = false) -> losing_state s.
    intros.
    apply losing_equiv_not_winning.
    destruct (w_reflect s); [ discriminate | auto ].
  Qed.

  Lemma get_outcome_b_true :
    forall s, (get_outcome_b s = true) -> winning_state s.
    intros.
    destruct (w_reflect s); [ auto | discriminate].
  Qed.

End Winning.

Definition zero : impartial_game.
  refine {|
    position := unit;
    start := tt;
    moves s := [];
  |}.
  constructor; intros y H; inversion H.
Defined.
