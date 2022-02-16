{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation

AC : Typeω
AC = {ℓ : Level} {A : Type ℓ} (f : A → Type ℓ) → ((x : A) → ∥ f x ∥) → ∥ ((x : A) → f x) ∥
