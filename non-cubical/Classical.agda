{-# OPTIONS --without-K #-}

open import HoTT.Foundations.Prelude
open import HoTT.Relation.Nullary
open import HoTT.Data.Empty as ⊥
open import HoTT.Data.Sum as Sum
open import HoTT.HITs.PropositionalTruncation

postulate LEM : ∀ {ℓ} {A : Type ℓ} → isProp A → (A ⊎ (¬ A))

NNE : ∀ {ℓ} {A : Type ℓ} → isProp A → ¬ (¬ A) → A
NNE P ¬¬a with LEM P
... | inl a = a
... | inr ¬a = ⊥.elim (¬¬a ¬a)

¬∀⇒∃¬ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → ¬ ((x : A) → B x) → ∥ Σ A (λ x → ¬ (B x)) ∥
¬∀⇒∃¬ {A = A} {B = B} PB P = NNE {A = ∥ Σ A (λ x → ¬ (B x)) ∥} propTruncIsProp λ N → P (λ x → Sum.elim {C = λ _ → B x} (λ Bx → Bx) (λ ¬Bx → ⊥.elim (N ∣ x , (λ z → ¬Bx z) ∣)) (LEM {A = B x} (PB x)))
