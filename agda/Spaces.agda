{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Fibration
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
open import Cubical.HITs.SetTruncation as ∥∥₀

-- functoriality of 0-truncation

∥∥₀-fun : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
         (A → B) → (∥ A ∥₀ → ∥ B ∥₀)
∥∥₀-fun f = ∥∥₀.rec setTruncIsSet (λ a → ∣ f a ∣₀)

∥∥₀-fun-∘ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
           (f : A → B) (g : B → C) → ∥∥₀-fun (g ∘ f) ≡ ∥∥₀-fun g ∘ ∥∥₀-fun f
∥∥₀-fun-∘ f g = funExt (∥∥₀.elim (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ a → refl))

∥∥₀-fun-id : {ℓ : Level} {A : Type ℓ} → ∥∥₀-fun (idfun A) ≡ idfun ∥ A ∥₀
∥∥₀-fun-id = funExt (∥∥₀.elim (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ a → refl))

-- equivalences are compatible with 0-truncation

∥∥₀-equiv : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
           A ≃ B → ∥ A ∥₀ ≃ ∥ B ∥₀
∥∥₀-equiv {_} {_} {A} {B} e = isoToEquiv i
  where
  i : Iso ∥ A ∥₀ ∥ B ∥₀
  Iso.fun i = ∥∥₀-fun (equivFun e)
  Iso.inv i = ∥∥₀-fun (invEq e)
  Iso.rightInv i = funExt⁻ (sym (∥∥₀-fun-∘ _  _) ∙ cong ∥∥₀-fun (funExt (retEq e)) ∙ ∥∥₀-fun-id)
  Iso.leftInv i = funExt⁻ (sym (∥∥₀-fun-∘ _  _) ∙ cong ∥∥₀-fun (funExt (secEq e)) ∙ ∥∥₀-fun-id)

-- fiberwise equivalence

∥∥₀-equiv-fib : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               (e : A ≃ B) (x : ∥ A ∥₀) → fiber ∣_∣₀ x ≃ fiber ∣_∣₀ (∥∥₀-fun (equivFun e) x)
∥∥₀-equiv-fib e x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ x) (fiber ∣_∣₀ (∥∥₀-fun (equivFun e) x))
  Iso.fun i (a , p) = equivFun e a , cong (∥∥₀-fun (equivFun e)) p
  Iso.inv i (b , p) = invEq e b , cong (∥∥₀-fun (invEq e)) p ∙ secEq (∥∥₀-equiv e) x
  Iso.rightInv i (b , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (retEq e b)
  Iso.leftInv i (a , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (secEq e a)

Σ-components : {ℓ : Level} (A : Type ℓ) → A ≃ Σ ∥ A ∥₀ (fiber ∣_∣₀)
Σ-components A = totalEquiv ∣_∣₀

-- two
⊤⊤ : Type _
⊤⊤ = ⊤ ⊎ ⊤

-- two is a set
⊤⊤-isSet : isSet ⊤⊤
⊤⊤-isSet (inl tt) (inl tt) = isContr→isProp (refl , lem)
  where
  e : (tt ≡ tt) ≃ (inl tt ≡ inl tt)
  e = _ , isEmbedding-inl tt tt
  lem = λ p →
    refl                   ≡⟨ refl ⟩
    equivFun e refl        ≡⟨ cong (equivFun e) (isProp→isSet isPropUnit _ _ _ _) ⟩
    equivFun e (invEq e p) ≡⟨ retEq e p ⟩
    p                      ∎
⊤⊤-isSet (inl tt) (inr tt) p q = ⊥.rec (inl≢inr p)
⊤⊤-isSet (inr tt) (inl tt) p q = ⊥.rec (inl≢inr (sym p))
⊤⊤-isSet (inr tt) (inr x) = isContr→isProp (refl , λ p → cong (equivFun e) (isProp→isSet isPropUnit _ _ _ _) ∙ retEq e p)
  where
  e : (tt ≡ tt) ≃ (inr tt ≡ inr tt)
  e = _ , isEmbedding-inr tt tt

-- truncation and doubling
∥∥₀×⊤⊤ : {ℓ : Level} {A : Type ℓ} → ∥ A × ⊤⊤ ∥₀ ≃ ∥ A ∥₀ × ⊤⊤
∥∥₀×⊤⊤ {_} {A} = isoToEquiv i
  where
  f : ∥ A × ⊤⊤ ∥₀ → ∥ A ∥₀ × ⊤⊤
  f = ∥∥₀.rec (isSet× setTruncIsSet ⊤⊤-isSet) λ { (a , t) → ∣ a ∣₀ , t }
  g : ∥ A ∥₀ × ⊤⊤ → ∥ A × ⊤⊤ ∥₀
  g (a , t) = ∥∥₀.rec setTruncIsSet (λ a → ∣ a , t ∣₀) a
  i : Iso ∥ A × ⊤⊤ ∥₀ (∥ A ∥₀ × ⊤⊤)
  Iso.fun i = f
  Iso.inv i = g
  Iso.rightInv i (a , t) = ∥∥₀.elim {B = λ a → f (g (a , t)) ≡ (a , t)} (λ _ → isProp→isSet (isSet× setTruncIsSet ⊤⊤-isSet _ _)) (λ a → refl) a
  Iso.leftInv i a = ∥∥₀.elim {B = λ a → g (f a) ≡ a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ { (a , t) → refl }) a
