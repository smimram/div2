{-# OPTIONS --without-K #-}

module HoTT.HITs.SetQuotients.Properties where

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Isomorphism
open import HoTT.HITs.SetQuotients.Base
open import HoTT.Relation.Binary

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    R : A → A → Type ℓ'
    B : A / R → Type ℓ''

open BinaryRelation

-- NB: matching on refl is cheating here, we don't use most of the hypothsis...
effective : (Rprop : isPropValued R) (Requiv : isEquivRel R) (a b : A) → _≡_ {A = A / R} [ a ] [ b ] → R a b
effective Rprop Requiv a .a refl = isEquivRel.reflexive Requiv a

isEquivRel→isEffective : isPropValued R → isEquivRel R → isEffective R
isEquivRel→isEffective {R = R} Rprop Req a b = isoToEquiv i
  where
  i : Iso ([ a ] ≡ [ b ]) (R a b)
  Iso.fun i p = effective Rprop Req a b p
  Iso.inv i r = eq/ a b r
  Iso.rightInv i r = Rprop a b _ _
  Iso.leftInv i p = squash/ _ _ _ _
