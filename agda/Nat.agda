{-# OPTIONS --cubical #-}

module Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat public

+1-suc : (n : ℕ) → n + 1 ≡ suc n
+1-suc zero = refl
+1-suc (suc n) = cong suc (+1-suc n)

data is-even : ℕ → Type₀
data is-odd  : ℕ → Type₀

data is-even where
  even-zero : is-even zero
  even-suc  : {n : ℕ} → is-odd n → is-even (suc n)

data is-odd where
  odd-suc : {n : ℕ} → is-even n → is-odd (suc n)

is-even-isProp : (n : ℕ) → isProp (is-even n)
is-odd-isProp  : (n : ℕ) → isProp (is-odd  n)
is-even-isProp zero even-zero even-zero = refl
is-even-isProp (suc n) (even-suc o) (even-suc o') = cong even-suc (is-odd-isProp n o o')
is-odd-isProp zero ()
is-odd-isProp (suc n) (odd-suc e) (odd-suc e') = cong odd-suc (is-even-isProp n e e')

¬odd-zero : ¬ (is-odd zero)
¬odd-zero ()

odd-pred : {n : ℕ} → is-even (suc n) → is-odd n
odd-pred (even-suc o) = o

even-pred : {n : ℕ} → is-odd (suc n) → is-even n
even-pred (odd-suc e) = e

parity : (n : ℕ) → is-even n ⊎ is-odd n
parity zero = inl even-zero
parity (suc n) with parity n
... | inl p = inr (odd-suc p)
... | inr p = inl (even-suc p)

¬even-odd : (n : ℕ) → is-even n → is-odd n → ⊥
¬even-odd (suc n) even odd = ¬even-odd n (even-pred odd) (odd-pred even)

open import Cubical.Data.Nat.Order
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Induction.WellFounded
open import Cubical.HITs.PropositionalTruncation as ∥∥

-- if there exists a natural number, we can find it!
find : {ℓ : Level} (P : ℕ → Type ℓ) → ((n : ℕ) → isProp (P n)) → ((n : ℕ) → Dec (P n)) → ∥ Σ ℕ P ∥₁ → Σ ℕ P
find P prop dec ex = fst first , fst (snd first)
  where
  isFirst : ℕ → Type _
  isFirst n = P n × ((m : ℕ) → P m → n ≤ m)
  isFirst-unique : {m n : ℕ} → isFirst m → isFirst n → m ≡ n
  isFirst-unique fm fn = ≤-antisym (snd fm _ (fst fn)) (snd fn _ (fst fm))
  isFirst-isProp : (n : ℕ) → isProp (isFirst n)
  isFirst-isProp n = isProp× (prop n) (isPropΠ (λ m → isPropΠ λ _ → isProp≤))
  isPropΣ' : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → ((x y : A) → B x → B y → x ≡ y) → isProp (Σ A B)
  isPropΣ' p e (a , b) (a' , b') = ΣPathP ((e _ _ b b') , (toPathP (p _ _ _)))
  first-isProp : isProp (Σ ℕ isFirst)
  first-isProp = isPropΣ' isFirst-isProp (λ _ _ → isFirst-unique)
  firstUntil : (n : ℕ) → Type _
  firstUntil n = Σ ℕ isFirst ⊎ ((m : ℕ) → m < n → ¬ (P m))
  search-until : (n : ℕ) → firstUntil n
  search-until zero = inr λ m m<0 _ → ¬-<-zero m<0
  search-until (suc n) with search-until n
  ... | inl f = inl f
  ... | inr ¬P with dec n
  ... | yes Pn = inl (n , Pn , λ m Pm → case n ≟ m return (λ _ → n ≤ m) of λ { (lt n<m) → ≤-trans (≤-suc ≤-refl) n<m ; (eq m≡n) → subst (λ n → n ≤ m) (sym m≡n) ≤-refl ; (gt n>m) → ⊥.rec (¬P m n>m Pm) })
  ... | no ¬Pn = inr (λ m m<sn Pm → case <-split m<sn of λ { (inl m<n) → ¬P _ m<n Pm ; (inr m≡n) → ¬Pn (subst P m≡n Pm) })
  search : (n : ℕ) → P n → Σ ℕ isFirst
  search n Pn with search-until (suc n)
  ... | inl first = first
  ... | inr ¬P = ⊥.rec (¬P n ≤-refl Pn)
  first : Σ ℕ isFirst
  first = ∥∥.rec first-isProp (λ { (n , Pn) → search n Pn }) ex
