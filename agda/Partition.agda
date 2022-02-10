{-# OPTIONS --cubical #-}
module Partition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Binary
open BinaryRelation
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

partition : {ℓ ℓ' : Level} {A : Type ℓ} (R : A → A → Type ℓ') → A ≃ Σ (A / R) (fiber [_])
partition {A = A} R = isoToEquiv i
  where
  i : Iso A (Σ (A / R) (fiber [_]))
  Iso.fun i a = [ a ] , a , refl
  Iso.inv i (_ , a , _) = a
  Iso.rightInv i (_ , a , p) = ΣPathP (p , toPathP (ΣPathP (transportRefl a , toPathP (squash/ _ _ _ p))))
  Iso.leftInv i a = refl

-- partitionΣ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'} (R : A → A → Type ℓ'') → Σ A B ≃ Σ (A / R) (λ x → Σ (fiber [_] x) (B ∘ fst))
-- partitionΣ {A = A} {B = B} R = isoToEquiv i
  -- where
  -- i : Iso (Σ A B) (Σ (A / R) (λ x → Σ (fiber [_] x) (B ∘ fst)))
  -- Iso.fun i (a , b) = [ a ] , (a , refl) , b
  -- Iso.inv i (_ , (a , _) , b) = a , b
  -- Iso.rightInv i ([a] , (a , p) , b) = ΣPathP (p , toPathP (ΣPathP (ΣPathP ((transportRefl a) , (toPathP (squash/ _ _ _ p))) , (toPathP {!refl!}))))
  -- Iso.leftInv i (a , b) = refl

open import Sigma

partitionΣ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : A → Type ℓ'} (R : A → A → Type ℓ'') → Σ A B ≃ Σ (A / R) (λ x → Σ (fiber [_] x) (B ∘ fst))
partitionΣ {A = A} {B = B} R =
  Σ A B ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv (partition R))) ⟩
  Σ (Σ (A / R) (fiber [_])) (B ∘ fst ∘ snd) ≃⟨ assocΣ ⟩
  Σ (A / R) (λ x → Σ (fiber [_] x) (B ∘ fst)) ■
