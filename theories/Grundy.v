From GameTheory Require Import ImpartialGame Boolgroup SumGames Equiv Nim.
Require Import Lia.
Require Import BinNat.

(* TODO: define mex in terms of N to make things easier (use peano_rect) *)
(* Fill in proof of specification of mex *)
(* May need to have unfolding lemma for grundy defn. *)
(* Need to prove extensionality property like for existsb. *)
(* Prove SG theorem *)
Fixpoint mex' (l : list N) (m n : N) : N.
  Check N.recursion.
Admitted.

Definition mex (l: list N) : N :=
  let len := N.of_nat (length l) in
  N.recursion len
    (fun n res : N => if existsb (N.eqb (len - N.succ n)) l
                      then res
                      else (len - N.succ n))
    len.
Print mex.

Compute (mex [0; 1; 2; 3; 4]).

Lemma mex_lt : forall (l : list N), (forall n, n < mex l -> In n l).
Admitted.

Lemma mex_neq : forall (l : list N), ~ In (mex l) l.
Admitted.


Fixpoint map_In {A B} (l : list A) : (forall (x : A), In x l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | x :: xs => fun f =>
                 f x (or_introl _ eq_refl) :: map_In xs (fun x P => f x (or_intror _ P))
  end.

Lemma map_In_map {A B : Type} :
  forall (l : list A)
         (f : forall (x : A), In x l -> B)
         (g : A -> B)
         (H : forall x P, f x P = g x),
    map_In l f = map g l.
Proof.
  induction l; auto.
  intros.
  simpl.
  rewrite H.
  apply f_equal.
  apply IHl; auto.
Qed.

Lemma map_In_ext :
  forall A B
         (l : list A)
         (f g: forall (x : A), In x l -> B)
         (EXT : forall x P, f x P = g x P),
    map_In l f = map_In l g.
Proof.
  intros.
  induction l as [ | x l IH ]; auto.
  simpl.
  rewrite EXT.
  f_equal.
  apply IH; auto.
Qed.

Section Grundy.
  Variable g : impartial_game.

  Definition grundy : position g -> N :=
    Fix (finite_game g)
      (fun _ => N)
      (fun x F => mex (map_In (moves g x) (fun y P => F y P))).


  Lemma grundy_unfold : forall s,
      grundy s = mex (map grundy (moves g s)).
    intros.
    unfold grundy.
    rewrite Fix_eq.
    apply f_equal.
    rewrite map_In_map with (g := Fix (finite_game g) (fun _ : position g => N)
       (fun (x : position g) (F : forall y : position g, valid_move g y x -> N) =>
          mex (map_In (moves g x) (fun (y : position g) (P : In y (moves g x)) => F y P)))).
    reflexivity.
    reflexivity.
    intros. apply f_equal. apply map_In_ext; auto.
  Qed.

  Lemma grundy_moves_valid : forall s s', valid_move g s' s -> In (grundy s') (map grundy (moves g s)).
    intros.
    unfold valid_move in H.
    apply (in_map grundy) in H.
    assumption.
  Qed.

  Lemma grundy_moves : forall s s',
      valid_move g s' s ->
      grundy s' < grundy s \/ grundy s < grundy s'.
    intros.
    destruct (N.lt_trichotomy (grundy s') (grundy s)) as [? | [? | ?]]; auto.
    apply grundy_moves_valid in H.
    rewrite H0 in H.
    rewrite grundy_unfold in H.
    apply mex_neq in H.
    contradiction.
  Qed.

  Lemma grundy_moves_lt : forall n s,
      n < grundy s ->
      exists s', valid_move g s' s /\ grundy s' = n.
    intros.
    rewrite grundy_unfold in H.
    apply mex_lt in H.
    apply in_map_iff in H as [s' [? ?]].
    exists s'; auto.
  Qed.

  Definition grundy_game : N := grundy (start g).

  Theorem sg_theorem : g == Nim (grundy_game).
    enough (forall s, forall n, losing_state (g ~+~ (Nim n)) (s, grundy s)).
    - unfold equiv. apply H.
    - refine (well_founded_induction (wf_trans _ _ (finite_game g)) _ _).
      intros.
      constructor; intros.
      apply moves_in_game_sum in H0 as [[? ?] | [? ?]].
      + destruct s'; simpl in *; subst.
        pose proof H0 as ?.
        apply grundy_moves in H0 as [H0 | H0].
        (* If our move is to a state with lower grundy number, *)
        (* make corresponding move on right side. *)
        * apply trans_to_losing with (p, grundy p).
          apply moves_in_game_sum; right; simpl; intuition.
          apply nim_moves_spec; assumption.
          apply H; constructor; assumption.
        (* If our move is to a state with higher grundy number, *)
        (* move back to state with original grundy value on left side *)
        * destruct (grundy_moves_lt _ _ H0) as [p' [? ?]].
          apply trans_to_losing with (p', grundy x).
          apply moves_in_game_sum; left; simpl; intuition.
          rewrite <- H3.
          apply H. constructor 2 with p; assumption.
      + destruct s'; simpl in *; subst.
        apply nim_moves_spec in H0.
        destruct (grundy_moves_lt _ _ H0) as [p' [? ?]].
        apply trans_to_losing with (p', p0).
        apply moves_in_game_sum; left; simpl; intuition.
        rewrite <- H2.
        apply H; constructor; assumption.
  Qed.
End Grundy.

Theorem sg_sum : forall g h, g ~+~ h == Nim (N.lxor (grundy_game g) (grundy_game h)).
  intros.
  rewrite (sg_theorem g) at 1.
  rewrite (sg_theorem h) at 1.
  apply nim_sum_equiv.
Qed.

Print Assumptions sg_sum.
