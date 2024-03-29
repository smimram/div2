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
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []
open import Misc
open import Ends
open import Z

module Tricho {ℓ} {A B : Type ℓ} (DA : Discrete A) (DB : Discrete B) (isom : A × End ≃ B × End) where

open import Arrows DA DB isom
open import Bracketing DA DB isom
open import Switch DA DB isom
open import Swapper DA DB isom

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

-- using the LPO from there on...

import LPO as LPO

well-bracketed-isDec : (a : Arrows) → Dec (well-bracketed a)
well-bracketed-isDec a = well-bracketed-end-isDec (fw a)
  where
  well-bracketed-end-isDec : (a : Ends) → Dec (well-bracketed-end a)
  well-bracketed-end-isDec a = LPO.DecΠℤ (λ n → matched (arrow (iterate n a))) (λ _ → matched-isProp _) (λ _ → matched-isDec _)

switched-isDec : (a : Arrows) → Dec (switched a)
switched-isDec a = switched-end-isDec (fw a)
  where
  switched-end-isDec : (a : Ends) → Dec (switched-end a)
  switched-end-isDec a = LPO.DecΣℤ (switched-end-at a) (switched-end-at-isDec a)

¬∀⇒∃¬ : {ℓ : Level} (P : ℤ → Type ℓ) → ((n : ℤ) → Dec (P n)) → ¬ ((n : ℤ) → P n) → Σ ℤ (λ n → ¬ (P n))
¬∀⇒∃¬ P D N = Dec→NNE (LPO.DecΣℤ _ (λ n → Dec¬ (D n))) (¬∀¬¬⇒¬¬∃¬ λ ¬¬P → N λ n → Dec→NNE (D n) (¬¬P n))

tricho : (c : Chains) → Tricho c
tricho c =
  [].elim Tricho-isSet T T≡ c
  where
  T : (a : Arrows) → Tricho [ a ]
  T a with well-bracketed-isDec a
  ... | yes iswb = wb iswb
  ... | no ¬wb with switched-isDec a
  ... | yes issw = sw issw
  ... | no ¬sw = sl (¬switched⇒sequential a ¬sw , ∣ ¬∀⇒∃¬ _ (λ n → matched-isDec _) ¬wb ∣₁)
  T≡ : (a b : Arrows) (r : ∥ reachable-arr a b ∥₁) → PathP (λ i → Tricho (eq/ a b r i)) (T a) (T b)
  T≡ a b r with well-bracketed-isDec a | well-bracketed-isDec b
  ... | yes awb | yes bwb = toPathP (cong wb (well-bracketed-chain-isProp [ b ] _ bwb))
  ... | yes awb | no b¬wb = ⊥.rec (b¬wb (transport (well-bracketed-indep a b (reachable-arr-reveal r)) awb))
  ... | no a¬wb | yes bwb = ⊥.rec (a¬wb (transport (sym (well-bracketed-indep a b (reachable-arr-reveal r))) bwb))
  ... | no a¬wb | no b¬wb with switched-isDec a | switched-isDec b
  ... | yes asw | yes bsw = toPathP (cong sw (switched-chain-isProp [ b ] _ bsw))
  ... | yes asw | no b¬sw = ⊥.rec (b¬sw (transport (switched-indep (reachable-arr-reveal r)) asw))
  ... | no a¬sw | yes bsw = ⊥.rec (a¬sw (transport (sym (switched-indep (reachable-arr-reveal r))) bsw))
  ... | no a¬sw | no b¬sw = toPathP (cong sl (slope-chain-isProp [ b ] _ _))
