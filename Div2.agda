{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Binary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Z as ℤ hiding (_<_ ; _≤_ ; _≟_)
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Nat as ℕ
open import Misc
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

open import Ends

module Div2 {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom
open import Bracketing SA SB isom
open import Switch SA SB isom
open import Swapper SA SB isom
open import Tricho SA SB isom

---
--- The bijection
---

open import Partition
open import Sigma

-- we can create an equivalence between A and B by doing so on each chain
bij-by-chain : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'}
               (R : A ⊎ B → A ⊎ B → Type ℓ'') →
               ((x : (A ⊎ B) / R) → (Σ (fiber [_] x) (in-left ∘ fst)) ≃ (Σ (fiber [_] x) (in-right ∘ fst))) →
               A ≃ B
bij-by-chain {A = A} {B = B} R b =
  A                                                        ≃⟨ inl≃ ⟩
  Σ (A ⊎ B) in-left                                        ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv (partition R))) ⟩
  Σ (Σ ((A ⊎ B) / R) (fiber [_])) (in-left ∘ fst ∘ snd)    ≃⟨ assocΣ ⟩
  Σ ((A ⊎ B) / R) (λ x → Σ (fiber [_] x) (in-left ∘ fst))  ≃⟨ congΣEquiv b ⟩
  Σ ((A ⊎ B) / R) (λ x → Σ (fiber [_] x) (in-right ∘ fst)) ≃⟨ invEquiv assocΣ ⟩
  Σ (Σ ((A ⊎ B) / R) (fiber [_])) (in-right ∘ fst ∘ snd)   ≃⟨ Σ-cong-equiv-fst (invEquiv (partition R)) ⟩
  Σ (A ⊎ B) in-right                                       ≃⟨ invEquiv inr≃ ⟩
  B                                                        ■

-- cong₂ Iso (sym (ua partition)) (sym (ua partition))

Conway-chain : (c : Chains) → chain-A≃B c
Conway-chain c with tricho c
... | wb t = matching-equiv t
... | sw t = swapper-chain (switched-element c t)
... | sl t = slope-swapper t

-- finally, the Conway isomorphism!
Conway : A ≃ B
Conway = bij-by-chain is-reachable-arr Conway-chain

