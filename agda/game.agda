module game where

-- open import Data.Nat
open import Data.List
import Data.List.Membership.DecPropositional as DecPropMembership
open import Relation.Binary.PropositionalEquality

-- open DecPropMembership Data.Nat._≟_

open import Data.List.Relation.Unary.Any using (here; there)

-- lem₁ : 1 ∈ 2 ∷ 1 ∷ 3 ∷ []
-- lem₁ = there (here refl)

open import Relation.Binary
open import Induction.WellFounded
open import Relation.Nullary
open import Data.Product

record Impartial : Set₁ where
  field
    S : Set
    _≟_ : DecidableEquality S
    start : S
    moves : S → List S

  open DecPropMembership _≟_
  valid_move : S → S → Set
  valid_move next current = next ∈ moves current

  field
    finite_game : WellFounded valid_move

module _ (game : Impartial) where
  open Impartial game

  data winning-state : S → Set
  data losing-state : S → Set

  data winning-state where
    trans-to-losing : (s s' : S) → valid_move s' s → losing-state s' → winning-state s
  data losing-state where
    all-winning : (s : S) → (∀ (s' : S) → valid_move s' s → winning-state s') → losing-state s

  -- A state cannot be both winning and losing.
  not-both-winning-losing : ∀ (s : S) → ¬ (winning-state s × losing-state s)
  not-both-winning-losing = {!!} -- prove this by well-founded induction


-- open import Data.List
-- open import Data.List.Membership.DecPropositional as DecPropMembership
-- -- open import Data.Nat
--
--
-- open DecPropMembership Data.Nat._≟_
--
-- lem₁ : 1 ∈ 2 ∷ 1 ∷ 3 ∷ []
-- lem₁ = ?
