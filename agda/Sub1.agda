{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Misc

private
  variable
    ℓ ℓ' : Level

toSingl : {A : Type ℓ} (a : A) → singl a
toSingl a = a , refl

---
--- Predecessor
---

Suc : (A : Type ℓ) → Type ℓ
Suc A = A ⊎ ⊤

-- Suc-elim : {A : Type ℓ} {B : Suc A → Type ℓ'} (x : Suc A) →
           -- ((a : A) → (x ≡ inl a) → B x) →
           -- ((x ≡ inr tt) → B x) →
           -- B x
-- Suc-elim (inl a)  f g = f a refl
-- Suc-elim (inr tt) f g = g refl

-- Suc-fun : {A : Type ℓ} {B : Type ℓ'} → (A → B) → (Suc A → Suc B)
-- Suc-fun f (inl a)  = inl (f a)
-- Suc-fun f (inr tt) = inr tt

-- F : {A B : Type ℓ} (f : Suc A → Suc B) → isInjection f → A → B
-- F f inj a = Suc-elim (f (inl a)) (λ b _ → b) (λ p → Suc-elim (f (inr tt)) (λ b _ → b) (λ q → ⊥.rec (inl≢inr (inj (p ∙ sym q)))))

-- F : {A B : Type ℓ} (f : Suc A → Suc B) → isEmbedding f → A → B
-- F f emb a = Suc-elim (f (inl a)) (λ b _ → b) (λ p → Suc-elim (f (inr tt)) (λ b _ → b) (λ q → ⊥.rec (inl≢inr (invEq (_ , emb (inl a) (inr tt)) (p ∙ sym q)))))

-- NB: we would only need isInjection here instead of isEmbedding, but the
-- pattern matching in Suc-inj fails because "relevant arguments are found
-- instead of relevant ones"...
F : {A B : Type ℓ} (f : Suc A → Suc B) → isEmbedding f → A → B
F f emb a with toSingl (f (inl a))
... | inl b  , p = b
... | inr tt , p with toSingl (f (inr tt))
... | inl b  , q = b
... | inr tt , q = ⊥.rec (inl≢inr (isEmbedding→isInjection emb (p ∙ sym q)))

Suc-inj : (A B : Type ℓ) → Suc A ≃ Suc B → A ≃ B
Suc-inj A B e = isoToEquiv i
  where
  f : Suc A → Suc B
  f = equivFun e
  g : Suc B → Suc A
  g = invEq e
  f-inj : isInjection f
  f-inj = isEmbedding→isInjection (isEquiv→isEmbedding (snd e))
  g-inj : isInjection g
  g-inj = isEmbedding→isInjection (isEquiv→isEmbedding (snd (invEquiv e)))
  i : Iso A B
  Iso.fun i = F f (isEquiv→isEmbedding (snd e))
  Iso.inv i = F g (isEquiv→isEmbedding (snd (invEquiv e)))
  Iso.rightInv i b with toSingl (g (inl b))
  Iso.rightInv i b | inl a , p with toSingl (f (inl a))
  Iso.rightInv i b | inl a , p | inl b' , q = inl-injective (sym q ∙ sym (cong f p) ∙ Iso.leftInv (equivToIso (invEquiv e)) (inl b))
  Iso.rightInv i b | inl a , p | inr tt , q with toSingl (f (inr tt))
  Iso.rightInv i b | inl a , p | inr tt , q | inl b' , q' = ⊥.rec (inl≢inr (sym (Iso.leftInv (equivToIso (invEquiv e)) (inl b)) ∙ cong f p ∙ q))
  Iso.rightInv i b | inl a , p | inr tt , q | inr tt , q' = ⊥.rec (inl≢inr (f-inj (q ∙ sym q')))
  Iso.rightInv i b | inr tt , p with toSingl (g (inr tt))
  Iso.rightInv i b | inr tt , p | inl a , p' with toSingl (f (inl a))
  Iso.rightInv i b | inr tt , p | inl a , p' | inl b' , q = ⊥.rec (inl≢inr (sym q ∙ cong f (sym p') ∙ Iso.leftInv (equivToIso (invEquiv e)) (inr tt)))
  Iso.rightInv i b | inr tt , p | inl a , p' | inr tt , q with toSingl (f (inr tt))
  Iso.rightInv i b | inr tt , p | inl a , p' | inr tt , q | inl b' , q' = inl-injective (sym q' ∙ cong f (sym p) ∙ Iso.leftInv (equivToIso (invEquiv e)) (inl b))
  Iso.rightInv i b | inr tt , p | inl a , p' | inr tt , q | inr tt , q' = ⊥.elim (inl≢inr (sym (Iso.leftInv (equivToIso (invEquiv e)) (inl b)) ∙ cong f p ∙ q'))
  Iso.rightInv i b | inr tt , p | inr a , p' = ⊥.rec (inl≢inr (sym (Iso.leftInv (equivToIso (invEquiv e)) (inl b)) ∙ cong f p ∙ cong f (sym p') ∙ Iso.leftInv (equivToIso (invEquiv e)) (inr tt)))
  Iso.leftInv i a with toSingl (f (inl a))
  Iso.leftInv i a | inl b , p with toSingl (g (inl b))
  Iso.leftInv i a | inl b , p | inl a' , q = inl-injective (sym q ∙ sym (cong g p) ∙ Iso.leftInv (equivToIso e) (inl a))
  Iso.leftInv i a | inl b , p | inr tt , q with toSingl (g (inr tt))
  Iso.leftInv i a | inl b , p | inr tt , q | inl a' , q' = ⊥.rec (inl≢inr (sym (Iso.leftInv (equivToIso e) (inl a)) ∙ cong g p ∙ q))
  Iso.leftInv i a | inl b , p | inr tt , q | inr tt , q' = ⊥.rec (inl≢inr (g-inj (q ∙ sym q')))
  Iso.leftInv i a | inr tt , p with toSingl (f (inr tt))
  Iso.leftInv i a | inr tt , p | inl b , p' with toSingl (g (inl b))
  Iso.leftInv i a | inr tt , p | inl b , p' | inl a' , q = ⊥.rec (inl≢inr (sym q ∙ cong g (sym p') ∙ Iso.leftInv (equivToIso e) (inr tt)))
  Iso.leftInv i a | inr tt , p | inl b , p' | inr tt , q with toSingl (g (inr tt))
  Iso.leftInv i a | inr tt , p | inl b , p' | inr tt , q | inl a' , q' = inl-injective (sym q' ∙ cong g (sym p) ∙ Iso.leftInv (equivToIso e) (inl a))
  Iso.leftInv i a | inr tt , p | inl b , p' | inr tt , q | inr tt , q' = ⊥.elim (inl≢inr (sym (Iso.leftInv (equivToIso e) (inl a)) ∙ cong g p ∙ q'))
  Iso.leftInv i a | inr tt , p | inr tt , p' = ⊥.rec (inl≢inr (sym (Iso.leftInv (equivToIso e) (inl a)) ∙ cong g p ∙ cong g (sym p') ∙ Iso.leftInv (equivToIso e) (inr tt)))

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma

Fin-suc : (n : ℕ) → Fin (suc n) ≃ Suc (Fin n)
Fin-suc n = isoToEquiv i
  where
  i : Iso (Fin (suc n)) (Suc (Fin n))
  Iso.fun i (zero , k<n) = inr tt
  Iso.fun i (suc k , k<n) = inl (k , (pred-≤-pred k<n))
  Iso.inv i (inl (k , k<n)) = suc k , suc-≤-suc k<n
  Iso.inv i (inr tt) = 0 , suc-≤-suc zero-≤
  Iso.rightInv i (inl (zero , k<n)) = cong inl (ΣProp≡ (λ _ → m≤n-isProp) refl)
  Iso.rightInv i (inl (suc k , k<n)) = cong inl (ΣProp≡ (λ _ → m≤n-isProp) refl)
  Iso.rightInv i (inr tt) = refl
  Iso.leftInv i (zero , k<n) = ΣProp≡ (λ _ → m≤n-isProp) refl
  Iso.leftInv i (suc k , k<n) = ΣProp≡ (λ _ → m≤n-isProp) refl

Fin-zero-suc : {n : ℕ} → ¬ (Fin 0 ≡ Fin (suc n))
Fin-zero-suc p = ¬Fin0 (transport (sym p) (0 , suc-≤-suc zero-≤))

Fin-injective : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
Fin-injective {zero}  {zero}  p = refl
Fin-injective {zero}  {suc n} p = ⊥.rec (Fin-zero-suc p)
Fin-injective {suc m} {zero}  p = ⊥.rec (Fin-zero-suc (sym p))
Fin-injective {suc m} {suc n} p = cong suc (Fin-injective (ua (Suc-inj _ _ (compEquiv (invEquiv (Fin-suc m)) (compEquiv (pathToEquiv p) (Fin-suc n))))))

-- without ua
Fin-injective' : {m n : ℕ} → Fin m ≃ Fin n → m ≡ n
Fin-injective' {zero}  {zero}  p = refl
Fin-injective' {zero}  {suc n} p = ⊥.rec (¬Fin0 (invEq p fzero))
Fin-injective' {suc m} {zero}  p = ⊥.rec (¬Fin0 (equivFun p fzero))
Fin-injective' {suc m} {suc n} p = cong suc (Fin-injective' (Suc-inj _ _ (compEquiv (invEquiv (Fin-suc m)) (compEquiv p (Fin-suc n)))))
