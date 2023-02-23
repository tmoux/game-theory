From GameTheory Require Import ImpartialGame SumGames.

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
