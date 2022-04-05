{-# OPTIONS --without-K #-}

module HoTT.HITs.SetQuotients.Base where

open import HoTT.Foundations.Prelude

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

data _/_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  [_] : (a : A) → A / R

postulate
  eq/ : {A : Type ℓ} {R : A → A → Type ℓ'} → (a b : A) → (r : R a b) → _≡_ {A = A / R} [ a ] [ b ]
  squash/ : {R : A → A → Type ℓ'} (x y : A / R) → (p q : x ≡ y) → p ≡ q
