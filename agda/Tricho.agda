{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []
open import Misc
open import Ends

module Tricho {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom
open import Bracketing SA SB isom
open import Switch SA SB isom
open import Swapper SA SB isom

---
--- The trichotomy
---

-- data Tricho (a : Arrows) : Type ℓ where
  -- wb : well-bracketed a → Tricho a
  -- sw : switched a       → Tricho a
  -- sl : slope (start a)  → Tricho a

data Tricho (c : Chains) : Type ℓ where
  wb : well-bracketed-chain c → Tricho c
  sw : switched-chain c       → Tricho c
  sl : slope-chain c          → Tricho c

abstract
  Tricho-isSet : (c : Chains) → isSet (Tricho c)
  Tricho-isSet c = subst isSet (sym lem) (isSet⊎ (isProp→isSet (well-bracketed-chain-isProp c)) (isSet⊎ (isProp→isSet (switched-chain-isProp c)) (isProp→isSet (slope-chain-isProp c))))
    where
    lem : Tricho c ≡ well-bracketed-chain c ⊎ (switched-chain c ⊎ slope-chain c)
    lem = ua (isoToEquiv i)
      where
      i : Iso (Tricho c) (well-bracketed-chain c ⊎ (switched-chain c ⊎ slope-chain c))
      Iso.fun i (wb x) = inl x
      Iso.fun i (sw x) = inr (inl x)
      Iso.fun i (sl x) = inr (inr x)
      Iso.inv i (inl x) = wb x
      Iso.inv i (inr (inl x)) = sw x
      Iso.inv i (inr (inr x)) = sl x
      Iso.rightInv i (inl x) = refl
      Iso.rightInv i (inr (inl x)) = refl
      Iso.rightInv i (inr (inr x)) = refl
      Iso.leftInv i (wb x) = refl
      Iso.leftInv i (sw x) = refl
      Iso.leftInv i (sl x) = refl

open import Classical

tricho : (c : Chains) → Tricho c
tricho c = [].elim Tricho-isSet T T≡ c
  where
  T : (a : Arrows) → Tricho [ a ]
  T a with LEM (well-bracketed-isProp a)
  ... | inl iswb = wb iswb
  ... | inr ¬wb with LEM (switched-isProp a)
  ... | inl issw = sw issw
  ... | inr ¬sw = sl (¬switched⇒sequential a ¬sw , (¬∀⇒∃¬ (λ _ → matched-isProp _) ¬wb))
  T≡ : (a b : Arrows) (r : ∥ reachable-arr a b ∥) → PathP (λ i → Tricho (eq/ a b r i)) (T a) (T b)
  T≡ a b r with LEM (well-bracketed-isProp a) | LEM (well-bracketed-isProp b)
  ... | inl awb | inl bwb = toPathP (cong wb (well-bracketed-chain-isProp [ b ] _ bwb))
  ... | inl awb | inr b¬wb = ⊥.rec (b¬wb (transport (well-bracketed-indep a b (reachable-arr-reveal r)) awb))
  ... | inr a¬wb | inl bwb = ⊥.rec (a¬wb (transport (sym (well-bracketed-indep a b (reachable-arr-reveal r))) bwb))
  ... | inr a¬wb | inr b¬wb with LEM (switched-isProp a) | LEM (switched-isProp b)
  ... | inl asw | inl bsw = toPathP (cong sw (switched-chain-isProp [ b ] _ bsw))
  ... | inl asw | inr b¬sw = ⊥.rec (b¬sw (transport (switched-indep (reachable-arr-reveal r)) asw))
  ... | inr a¬sw | inl bsw = ⊥.rec (a¬sw (transport (sym (switched-indep (reachable-arr-reveal r))) bsw))
  ... | inr a¬sw | inr b¬sw = toPathP (cong sl (slope-chain-isProp [ b ] _ _))
