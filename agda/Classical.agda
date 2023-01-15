{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as ∥∥

postulate LEM : ∀ {ℓ} {A : Type ℓ} → isProp A → (A ⊎ (¬ A))

NNE : ∀ {ℓ} {A : Type ℓ} → isProp A → ¬ (¬ A) → A
NNE P ¬¬a with LEM P
... | inl a = a
... | inr ¬a = ⊥.elim (¬¬a ¬a)

¬∀⇒∃¬ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → ¬ ((x : A) → B x) → ∥ Σ A (λ x → ¬ (B x)) ∥₁
¬∀⇒∃¬ {A = A} {B = B} PB P = NNE {A = ∥ Σ A (λ x → ¬ (B x)) ∥₁} isPropPropTrunc λ N → P (λ x → Sum.elim {C = λ _ → B x} (λ Bx → Bx) (λ ¬Bx → ⊥.elim (N ∣ x , (λ z → ¬Bx z) ∣₁)) (LEM {A = B x} (PB x)))

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

NNI : ∀ {ℓ} {A : Type ℓ} → A → ¬ (¬ A)
NNI a ¬a = ¬a a

-- in classical logic, propositional truncation coincides with double negation

classicalTruncationProp : {ℓ : Level} {A : Type ℓ} → isProp A → ∥ A ∥₁ ≃ (¬ ¬ A)
classicalTruncationProp {_} {A} P = isoToEquiv i
  where
  i : Iso ∥ A ∥₁ (¬ (¬ A))
  Iso.fun i a = ∥∥.rec (isProp¬ (¬ A)) NNI a
  Iso.inv i a = ∣ NNE P a ∣₁
  Iso.rightInv i a = isProp¬ _ _ _
  Iso.leftInv i a = isPropPropTrunc _ _

N⁴≃N² : {ℓ : Level} (A : Type ℓ) → (¬ ¬ ¬ ¬ A) ≃ (¬ ¬ A)
N⁴≃N² A = isoToEquiv i
  where
  i : Iso (¬ (¬ (¬ (¬ A)))) (¬ (¬ A))
  Iso.fun i = NNE (isProp¬ _)
  Iso.inv i = NNI
  Iso.rightInv i _ = isProp¬ _ _ _
  Iso.leftInv i _ = isProp¬ _ _ _
