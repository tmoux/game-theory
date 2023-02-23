From GameTheory Require Import ImpartialGame SumGames.
From Coq Require Import Morphisms RelationClasses.

Definition equiv (a b : impartial_game) := losing_state (a ~+~ b) (start a, start b).
Notation "a == b" := (equiv a b) (at level 50).

#[export] Instance equiv_reflexive : Reflexive equiv.
Admitted.

#[export] Instance equiv_symmetric : Symmetric equiv.
Admitted.

#[export] Instance equiv_transitive : Transitive equiv.
Admitted.

#[export] Instance equiv_equiv : Equivalence equiv.
Proof.
  constructor;
    [ exact equiv_reflexive |
      exact equiv_symmetric |
      exact equiv_transitive ].
Qed.

#[export] Instance sum_proper : Proper (equiv ==> equiv ==> equiv) sum_game.
Admitted.
