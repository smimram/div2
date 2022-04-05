{-# OPTIONS --without-K --allow-unsolved-metas #-}

module HoTT.Foundations.Isomorphism where

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Equiv
open import HoTT.Data.Sigma

-- Section and retract
module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where
  section : (f : A → B) → (g : B → A) → Type ℓ'
  section f g = ∀ b → f (g b) ≡ b

  retract : (f : A → B) → (g : B → A) → Type ℓ
  retract f g = ∀ a → g (f a) ≡ a

record Iso {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv : retract fun inv

isoToEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → Iso A B → A ≃ B
isoToEquiv i = Iso.fun i , λ y → (Iso.inv i y , Iso.rightInv i y) , λ { (x , refl) → ΣPathP (Iso.leftInv i x , {!!}) }
