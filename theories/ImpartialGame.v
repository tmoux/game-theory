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

(*
Fixpoint nums_lt (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n' :: nums_lt n'
  end.

Definition Nim (n : nat) : impartial_game.
  refine {|
           position := nat;
           start := n;
           moves := fun x => nums_lt x;
           finite_game := _
         |}.
  unfold well_founded.
  induction a.
  constructor. simpl. intuition.
  constructor. simpl. intuition.
  rewrite <- H0. assumption.
  apply IHa. assumption.
Defined. *)

(* Weird recursive definition of winning. Seems harder to work with.
   Actually, may not be too bad, we just need a lemma to explain how it unfolds. *)
Definition is_winning (game: impartial_game) : position game -> Prop.
  refine (Fix (finite_game game)
            (fun _ => Prop)
            (fun x H => exists (s : position game) (p: valid_move game s x),
                           ~ (H s p))).
Defined.

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

  (* If we have two predicates P and Q and a list l where we can decide either P or Q,
then either there is s such that Q s, or we have P s for all s.
   *)
  Lemma exists_in_list {A : Type} : forall (P Q : A -> Prop) (l : list A), (forall x, In x l -> (P x) + (Q x)) -> (Exists Q l) + (Forall P l).
  Proof.
    induction l; intuition.
    match goal with
    | [ a : A, Dec : forall x, _ -> _, IH: _ -> Exists Q l + Forall P l |- _ ] => destruct (Dec a); destruct IH; intuition
    end.
  Defined.

  (* A state is either winning or losing. We prove this by demonstrating how to compute the outcome of a state by recursing on the well-founded game tree of moves. *)
  Definition get_outcome : forall s, winning_state s + losing_state s.
    refine (Fix (finite_game game) (fun s => sum (winning_state s) (losing_state s)) _).
    intros x IH.
    destruct (exists_in_list _ _ _ IH) as [Hexists | Hforall].
    - rewrite -> Exists_exists in Hexists; left; destruct Hexists as [y [? ?]]; econstructor; eauto.
    - rewrite -> Forall_forall in Hforall; right; constructor; auto.
  Defined.
  Hint Resolve get_outcome : core.

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


  Check reflect.

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


  (* If we have two predicates P and Q that are disjoint and at least one is true, then P <-> ~ Q and Q <-> ~ P. *)
  Lemma dec_disjoint_implies_negation {A : Type} : forall (P Q : A -> Prop), (forall s, ~ (P s /\ Q s)) -> (forall s, P s + Q s) -> (forall s, (P s <-> ~ Q s) /\ (Q s <-> ~ P s)).
    intros ? ? H1 H2 s.
    specialize (H1 s).
    specialize (H2 s).
    intuition.
  Qed.

  Lemma losing_equiv_not_winning : forall s, losing_state s <-> ~ winning_state s.
    apply dec_disjoint_implies_negation; auto.
  Qed.

  Lemma winning_or_losing : forall s, winning_state s + losing_state s.
    intros.
    destruct (w_reflect s);
    [ auto | right; apply losing_equiv_not_winning; auto ].
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

(*
Goal winning_state (Nim 0) 1.
  assert (H1: get_outcome_b (Nim 0) 1 = true).
  reflexivity.
  assert (H : reflect (winning_state (Nim 0) 1) (get_outcome_b (Nim 0) 1)).
  apply w_reflect.
  destruct H as [H | H].
  assumption.
  discriminate.
Qed. *)

(*
  apply (well_founded_induction (finite_game game)); intuition.
  destruct (get_outcome_b game x) eqn:E.
  - constructor. rewrite get_outcome_b_unfold in E.
    assert (exists y, get_outcome_b game y = false) as [y H]. admit.
    assert (valid_move game y x). admit.
    econstructor. apply H0. destruct (X y); auto. discriminate.
    (* If a state is not winning, it is losing. *)
    rewrite losing_equiv_not_winning. assumption.

  - constructor. admit.
Admitted. *)


(* Demonstration of using the unfolding lemma.
Goal forall n, get_outcome_b (Nim 0) (S n) = true.
  intros n.
  rewrite get_outcome_b_unfold.
  simpl.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite orb_true_r.
  reflexivity.
Qed. *)

Inductive game := Game {
                      moves_from_game : list game
                    }.

Lemma lift_forall : forall T (P : T -> Prop), (forall t, P t) -> forall l, Forall P l.
Proof. induction l; auto. Defined.

Definition game_ind' (P : game -> Prop)
  (H : forall l, Forall P l -> P (Game l)) :
  forall g, P g := fix F g :=
    match g with
    | Game l => H l (lift_forall _ P F l)
    end.

Check game_ind'.

Fixpoint is_winning_game (g : game) : bool :=
  match g with
  | {| moves_from_game := moves |} =>
      existsb (fun x => negb (is_winning_game x)) moves
  end.

(* Example of a game: nim. *)
Fixpoint nim (n : nat) : game :=
  let moves := (fix f (m : nat) :=
                  match m with
                  | 0 => []
                  | S m' => nim m' :: f m'
                  end)
  in Game (moves n).

Eval vm_compute in is_winning_game (nim 11).



Check get_outcome.
Definition extract_outcome {game : impartial_game} {s : position game} (outcome : winning_state game s + losing_state game s) : bool :=
  match outcome with
  | inl _ => false
  | inr _ => true
  end.


Definition zero : impartial_game.
  refine {|
    position := unit;
    start := tt;
    moves s := [];
  |}.
  constructor; intros y H; inversion H.
Defined.

(*
Definition embed_in_game cg (pos : position cg) : game :=
  Fix (finite_game cg)
      (fun _ => position game_as_cg)
      (fun pos F =>
         {| moves_from_game := (map_game cg pos F) |}
      pos). *)

(*
Rewrite using sections to reduce repeating parameters.
Define game trees (see Poleiro blog).
Define Nim game
Define sum of games.
  Show sum of two identical games is always losing.
Define equivalence of games (if they have effect when summing).
Or equivalently, two game are equal if they sum to the zero game. (i.e., are losing)

Prove nim XOR result.
Prove equivalence of nim-with-increases.
Prove Sprague-Grundy theorem.
 *)
