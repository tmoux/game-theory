open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

module boolgroup where

record BoolGroup : Set₁ where
  infixl 30 _+_
  field
    A : Set
    e : A
    _+_ : A → A → A

    assoc : ∀ (a b c : A) → a + (b + c) ≡ (a + b) + c
    identl : ∀ (a : A) → e + a ≡ a
    identr : ∀ (a : A) → a + e ≡ a
    involutive : ∀ (a : A) → a + a ≡ e

module BoolGroupSolver (G : BoolGroup) where
  open BoolGroup G

  comm : ∀ (a b : A) → a + b ≡ b + a
  comm a b = a + b ≡⟨ sym (identr _) ⟩
             (a + b) + e                     ≡⟨ cong (_ +_) (sym (involutive (b + a))) ⟩
             (a + b) + ((b + a) + (b + a))   ≡⟨ assoc _ _ _ ⟩
             ((a + b) + (b + a)) + (b + a)   ≡⟨ cong (_+ (b + a)) (assoc _ _ _) ⟩
             (((a + b) + b) + a) + (b + a)   ≡⟨ cong (λ z → (z + _) + (b + a)) (sym (assoc _ _ _)) ⟩
             (((a + (b + b) + a))) + (b + a) ≡⟨ cong (λ z → (_ + z + _) + _) (involutive _) ⟩
             (((a + e + a))) + (b + a)       ≡⟨ cong (λ z → (z + _) + (b + a)) (identr _) ⟩
             (a + a) + (b + a)               ≡⟨ cong (_+ _) (involutive _) ⟩
             e + (b + a)                     ≡⟨ identl _ ⟩
             b + a ∎
