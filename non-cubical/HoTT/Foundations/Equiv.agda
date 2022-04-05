{-# OPTIONS --without-K #-}

module HoTT.Foundations.Equiv where

open import HoTT.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

fiber : {A : Set ℓ} {B : Set ℓ'} (f : A → B) (y : B) → Set (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ A \ x → f x ≡ y

isEquiv : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isEquiv {B = B} f = (y : B) → isContr (fiber f y)

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ-max ℓ ℓ')
A ≃ B = Σ (A → B) isEquiv
