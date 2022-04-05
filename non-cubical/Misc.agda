{-# OPTIONS --without-K #-}

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Equiv
open import HoTT.Foundations.Isomorphism
-- open import HoTT.Data.Prod
open import HoTT.Data.Sum
open import HoTT.Data.Empty
open import HoTT.Data.Unit

-- usual notations

-- (this is cong)
-- ap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
-- ap f p i = f (p i)

-- happly : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
-- happly p x i = p i x

---
--- Inspection
---

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-- notations for equivalences

-- ≃→ : ∀ {i j} {A : Type i} {B : Type j} → A ≃ B → A → B
-- ≃→ e = equivFun e

-- ≃← : ∀ {i j} {A : Type i} {B : Type j} → A ≃ B → B → A
-- ≃← e = invEq e

-- non-dependent version of cong
-- cong-nd : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) (p : x ≡ y) → f x ≡ f y
-- cong-nd f p = f (p i)

-- ⊎-×-≃ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
-- ⊎-×-≃ {A = A} {B = B} {C = C} = isoToEquiv (iso f g f-g g-f)
  -- where
  -- f : (A ⊎ B) × C → (A × C) ⊎ (B × C)
  -- f (inl a , c) = inl (a , c)
  -- f (inr b , c) = inr (b , c)
  -- g : (A × C) ⊎ (B × C) → (A ⊎ B) × C
  -- g (inl (a , c)) = (inl a) , c
  -- g (inr (b , c)) = (inr b) , c
  -- g-f : (x : (A ⊎ B) × C) → g (f x) ≡ x
  -- g-f (inl a , c) = refl
  -- g-f (inr b , c) = refl
  -- f-g : (x : (A × C) ⊎ (B × C)) → f (g x) ≡ x
  -- f-g (inl (a , c)) = refl
  -- f-g (inr (b , c)) = refl

-- useful lemmas on coproducts

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} where

  disjoint-coprod' : {a : A} {b : B} → inl a ≡ inr b → Lift {_} {ℓ} ⊥
  disjoint-coprod' {a} p = subst A⊥ p a
    where
    A⊥ : A ⊎ B → Set ℓ
    A⊥ (inl _) = A
    A⊥ (inr _) = Lift ⊥

  -- injections into the coproduct are disjoint
  disjoint-coprod : {a : A} {b : B} → inl a ≡ inr b → ⊥
  disjoint-coprod p with disjoint-coprod' p
  ... | ()

  coprod-case : (x : A ⊎ B) → Σ A (λ a → x ≡ inl a) ⊎ Σ B (λ b → x ≡ inr b)
  coprod-case (inl a) = inl (a , refl)
  coprod-case (inr b) = inr (b , refl)

  data in-left  : A ⊎ B → Type (ℓ-max ℓ ℓ') where
    is-inl : (a : A) → in-left (inl a)

  data in-right : A ⊎ B → Type (ℓ-max ℓ ℓ') where
    is-inr : (b : B) → in-right (inr b)

  in-left-is-prop : (x : A ⊎ B) → isProp (in-left x)
  in-left-is-prop .(inl a) (is-inl a) (is-inl .a) = refl

  in-right-is-prop : (x : A ⊎ B) → isProp (in-right x)
  in-right-is-prop .(inr b) (is-inr b) (is-inr .b) = refl

  is-left : {x : A ⊎ B} → in-left x → Σ A (λ a → x ≡ inl a)
  is-left (is-inl a) = a , refl

  is-right : {x : A ⊎ B} → in-right x → Σ B (λ b → x ≡ inr b)
  is-right (is-inr b) = b , refl

  get-left : {x : A ⊎ B} → in-left x → A
  get-left (is-inl a) = a

  get-right : {x : A ⊎ B} → in-right x → B
  get-right (is-inr b) = b

  -- NB: I am sure that there is an equivalence lying there, but I am too lazy
  -- right now to think about it
  inl-get-left : {x : A ⊎ B} (l : in-left x) → inl (get-left l) ≡ x
  inl-get-left (is-inl a) = refl

  inr-get-right : {x : A ⊎ B} (r : in-right x) → inr (get-right r) ≡ x
  inr-get-right (is-inr b) = refl

-- is-left' : ∀ {ℓ} {A B : Type ℓ} → (A ⊎ B) → Type₀
-- is-left' (inl a) = Unit
-- is-left' (inr b) = ⊥

-- ×-≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → _≡_ { A = A × B } (a , b) (a' , b')
-- ×-≡ p q i = (p i , q i)
