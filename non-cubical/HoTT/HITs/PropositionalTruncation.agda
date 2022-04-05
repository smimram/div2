{-# OPTIONS --without-K --rewriting #-}

module HoTT.HITs.PropositionalTruncation where

open import HoTT.Foundations.Prelude

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∥ A ∥

private
  variable
    ℓ : Level
    A : Type ℓ

postulate
  squash : ∀ (x y : ∥ A ∥) → x ≡ y

propTruncIsProp : isProp ∥ A ∥
propTruncIsProp x y = squash x y

postulate
  rec : ∀ {P : Type ℓ} → isProp P → (A → P) → ∥ A ∥ → P
  comp : ∀ {P : Type ℓ} (a : ∥ A ∥) → rec propTruncIsProp ∣_∣ a ≡ a
  {-# REWRITE comp #-}
