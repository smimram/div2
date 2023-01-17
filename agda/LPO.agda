{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Nat
open import Cubical.Axiom.Omniscience as O hiding (WLPO ; LPO)

open import Misc
open import Z

module LPO where

LPO : {ℓ ℓ' : Level} (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
LPO {ℓ' = ℓ'} A = (P : A → Type ℓ') → ((n : A) → isProp (P n)) → ((n : A) → Dec (P n)) → ((n : A) → P n) ⊎ Σ A (λ n → ¬ (P n))

postulate
  -- NOTE: one should be enough since the two are equivalent
  LPOℕ : {ℓ' : Level} → LPO {ℓ' = ℓ'} ℕ
  LPOℤ : {ℓ' : Level} → LPO {ℓ' = ℓ'} ℤ

DecΣ : {ℓ ℓ' : Level} {A : Type ℓ} → LPO A → (P : A → Type ℓ') → ((n : A) → Dec (P n)) → Dec (Σ A P)
DecΣ LPO P D with LPO (λ n → ¬ (P n)) (λ _ → isProp¬ _) (λ n → Dec¬ (D n))
... | inl ¬p = no λ { (n , p) → ¬p n p }
... | inr (n , ¬¬p) = yes (n , Dec→NNE (D n) ¬¬p)

DecΣℕ : {ℓ : Level} (P : ℕ → Type ℓ) → ((n : ℕ) → Dec (P n)) → Dec (Σ ℕ P)
DecΣℕ = DecΣ LPOℕ

DecΣℤ : {ℓ : Level} (P : ℤ → Type ℓ) → ((n : ℤ) → Dec (P n)) → Dec (Σ ℤ P)
DecΣℤ = DecΣ LPOℤ

DecΠℕ : {ℓ : Level} (P : ℕ → Type ℓ) → ((n : ℕ) → isProp (P n)) → ((n : ℕ) → Dec (P n)) → Dec ((n : ℕ) → P n)
DecΠℕ P PP D with LPOℕ P PP D
... | inl p = yes p
... | inr (n , ¬p) = no λ p → ¬p (p n)

DecΠℤ : {ℓ : Level} (P : ℤ → Type ℓ) → ((n : ℤ) → isProp (P n)) → ((n : ℤ) → Dec (P n)) → Dec ((n : ℤ) → P n)
DecΠℤ P PP D with LPOℤ P PP D
... | inl p = yes p
... | inr (n , ¬p) = no (λ p → ¬p (p n))
