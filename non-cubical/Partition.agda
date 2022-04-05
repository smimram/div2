{-# OPTIONS --without-K #-}
module Partition where

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Function
open import HoTT.Foundations.Isomorphism
open import HoTT.Foundations.Equiv
open import HoTT.Data.Sigma
open import HoTT.Relation.Nullary
open import HoTT.Relation.Nullary.DecidableEq
open import HoTT.HITs.SetQuotients

module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : A → A → Type ℓ') where

  partition : A ≃ Σ (A / R) (fiber [_])
  partition = isoToEquiv i
    where
    i : Iso A (Σ (A / R) (fiber [_]))
    Iso.fun i a = [ a ] , a , refl
    Iso.inv i (_ , a , _) = a
    Iso.rightInv i (.([ a ]) , a , refl) = refl
    Iso.leftInv i a = refl
