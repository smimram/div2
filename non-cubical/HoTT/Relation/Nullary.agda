{-# OPTIONS --without-K #-}

module HoTT.Relation.Nullary where

open import HoTT.Foundations.Prelude
open import HoTT.Data.Empty as ⊥

private
  variable
    ℓ  : Level
    A  : Type ℓ

infix 3 ¬_

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- Decidable types

data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

Discrete : Type ℓ → Type ℓ
Discrete A = (x y : A) → Dec (x ≡ y)
