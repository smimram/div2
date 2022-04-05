{-# OPTIONS --without-K #-}

module HoTT.Data.Sum where

open import HoTT.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A B C D : Type ℓ

data _⊎_ (A : Type ℓ)(B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {C : A ⊎ B → Type ℓ} →  ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A ⊎ B) → C x
elim f _ (inl x) = f x
elim _ g (inr y) = g y
