From GameTheory Require Import ImpartialGame SumGames.
From Coq Require Import Morphisms RelationClasses.

Definition equiv (a b : impartial_game) := losing_state (a ~+~ b) (start a, start b).
Notation "a == b" := (equiv a b) (at level 50).

#[export] Instance equiv_equiv : Equivalence equiv.
Admitted.

#[export] Instance sum_proper : Proper (equiv ==> equiv ==> equiv) sum_game.
Admitted.
