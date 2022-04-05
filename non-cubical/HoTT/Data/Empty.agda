{-# OPTIONS --without-K #-}

module HoTT.Data.Empty where

open import HoTT.Foundations.Prelude

data ⊥ : Type₀ where

elim : ∀ {ℓ} {A : ⊥ → Type ℓ} → (x : ⊥) → A x
elim ()

isProp⊥ : isProp ⊥
isProp⊥ ()
