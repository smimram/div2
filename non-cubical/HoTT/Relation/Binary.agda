{-# OPTIONS --without-K #-}

module HoTT.Relation.Binary where

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Equiv
open import HoTT.HITs.SetQuotients.Base

module BinaryRelation {ℓ ℓ' : Level} {A : Type ℓ} (R : A → A → Type ℓ') where
  isRefl : Type (ℓ-max ℓ ℓ')
  isRefl = (a : A) → R a a

  isSym : Type (ℓ-max ℓ ℓ')
  isSym = (a b : A) → R a b → R b a

  isTrans : Type (ℓ-max ℓ ℓ')
  isTrans = (a b c : A)  → R a b → R b c → R a c

  record isEquivRel : Type (ℓ-max ℓ ℓ') where
    constructor EquivRel
    field
      reflexive : isRefl
      symmetric : isSym
      transitive : isTrans

  isPropValued : Type (ℓ-max ℓ ℓ')
  isPropValued = (a b : A) → isProp (R a b)

  isEffective : Type (ℓ-max ℓ ℓ')
  isEffective = (a b : A) →
    let x : A / R
        x = [ a ]
        y : A / R
        y = [ b ]
    in (x ≡ y) ≃ R a b
