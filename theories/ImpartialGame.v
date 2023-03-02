From Coq Require Export List.
Export ListNotations.
Require Export Coq.Bool.Bool.

Inductive impartial_game :=
  ImpartialGame {
      position: Type;
      start : position;
      moves : position -> list position;
      valid_move next current := In next (moves current);
      finite_game : well_founded valid_move;
    }.
Check ImpartialGame.

Section Winning.
  Variable game: impartial_game.
  Let S := position game.

  Inductive winning_state : S -> Prop :=
  | trans_to_losing : forall (s s' : S), valid_move game s' s -> losing_state s' -> winning_state s
  with losing_state : S -> Prop :=
  | all_winning : forall (s : S), (forall (s' : S), valid_move game s' s -> winning_state s') -> losing_state s.

  (* A state cannot be both winning and losing at the same time. *)
  Lemma not_both_winning_losing : forall (s : S), ~ ((winning_state s) /\ (losing_state s)).
    apply (well_founded_induction (finite_game game)); intuition.
    match goal with
    | [ H : forall y, _ -> _ -> False, H1 : winning_state ?x, H2: losing_state ?x |- _ ] =>
        destruct H1 as [s s' H1]; destruct H2; apply H with s'; auto
    end.
  Defined.
  Hint Resolve not_both_winning_losing : core.

  Lemma losing_implies_not_winning : forall (s : S), losing_state s -> ~ winning_state s.
    intros s H.
    pose (not_both_winning_losing s).
    unfold not in *.
    intuition.
  Qed.

  Fixpoint existsb_In {A} (l : list A) : (forall (x : A), In x l -> bool) -> bool :=
    match l with
    | [] => fun _ => false
    | x :: xs => fun f =>
                   orb (f x (or_introl _ eq_refl)) (existsb_In xs (fun x P => f x (or_intror _ P)))
    end.

  Definition get_outcome_b : S -> bool :=
  Fix (finite_game game) (fun _ : position game => bool)
    (fun (s : position game)
      (F : forall y : position game, valid_move game y s -> bool) =>
    existsb_In (moves game s)
      (fun (x : position game) (HIn : In x (moves game s)) => negb (F x HIn))).

  Lemma existsb_In_existsb {A : Type} :
    forall (l : list A)
           (f : forall x, In x l -> bool)
           (g : A -> bool)
           (H : forall x P, f x P = g x),
    existsb_In l f = existsb g l.
    induction l; auto.
    intros.
    simpl.
    rewrite H.
    apply f_equal.
    apply IHl; auto.
  Qed.

  Lemma existsb_false {A : Type}:
    forall (l : list A)
           (f : A -> bool),
           existsb f l = false ->
           (forall x, In x l -> f x = false).
    induction l; intuition.
    inversion H0.
    inversion H0; subst.
    simpl in H. apply orb_false_iff in H. intuition.
    apply IHl; auto.
    simpl in H. apply orb_false_iff in H; intuition.
  Qed.

  Lemma existsb_In_ext :
    forall A
           (l : list A)
           (f g: forall x, In x l -> bool)
           (EXT : forall x P, f x P = g x P),
    existsb_In l f = existsb_In l g.
    intros.
    induction l as [ | x l IH ]; auto.
    simpl.
    rewrite EXT.
    f_equal.
    apply IH; auto.
  Qed.

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
    destruct (get_outcome_b s) eqn:?; auto.
  Qed.

  (* If we have two predicates P and Q that are disjoint and at least one is true, then P <-> ~ Q and Q <-> ~ P. *)
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
