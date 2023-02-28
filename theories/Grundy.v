From GameTheory Require Import ImpartialGame Boolgroup SumGames Equiv Nim.
Require BinNat.

(* TODO: define mex in terms of N to make things easier (use peano_rect) *)
(* Fill in proof of specification of mex *)
(* Prove SG theorem *)
Fixpoint mex' (l : list nat) (N n : nat) : nat :=
  match n with
  | 0%nat => N
  | S n' => if existsb (Nat.eqb (N - n)) l then mex' l N n' else (N - n)
  end.

Definition mex (l: list nat) : nat :=
  mex' l (length l) (length l).

Compute (mex [0; 2; 3; 4]).

Lemma mex_lt : forall (l : list nat), (forall n, n < mex l -> In n l).
Admitted.

Lemma mex_neq : forall (l : list nat), ~ In (mex l) l.
Admitted.


Fixpoint map_In {A B} (l : list A) : (forall (x : A), In x l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | x :: xs => fun f =>
                 f x (or_introl _ eq_refl) :: map_In xs (fun x P => f x (or_intror _ P))
  end.

Section Grundy.
  Variable g : impartial_game.

  Definition grundy : position g -> nat :=
    Fix (finite_game g) (fun _ => nat) (fun x F => mex (map_In (moves g x) (fun y P => F y P))).

  Theorem sg_theorem : g == Nim (BinNat.N.of_nat (grundy (start g))).
    enough (forall s, losing_state (g ~+~ (Nim (BinNat.N.of_nat (grundy s)))) (s, BinNat.N.of_nat (grundy s))).
    unfold equiv.
    apply H.
  Admitted.

End Grundy.
