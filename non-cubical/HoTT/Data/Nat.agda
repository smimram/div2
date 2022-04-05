{-# OPTIONS --without-K #-}

module HoTT.Data.Nat where

open import HoTT.Foundations.Prelude

open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ; _-_ to _∸_)

+-zero : ∀ m → m + 0 ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm m zero = +-zero m
+-comm m (suc n) = (+-suc m n) ∙ (cong suc (+-comm m n))

-- order
 
infix 4 _≤_ _<_

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Σ ℕ λ k → k + m ≡ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

private
  variable
    m n : ℕ

suc-≤-suc : m ≤ n → suc m ≤ suc n
suc-≤-suc (k , p) = k , (+-suc k _) ∙ (cong suc p)

data Trichotomy (m n : ℕ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

Trichotomy-suc : Trichotomy m n → Trichotomy (suc m) (suc n)
Trichotomy-suc (lt m<n) = lt (suc-≤-suc m<n)
Trichotomy-suc (eq m=n) = eq (cong suc m=n)
Trichotomy-suc (gt n<m) = gt (suc-≤-suc n<m)

_≟_ : ∀ m n → Trichotomy m n
zero ≟ zero = eq refl
zero ≟ suc n = lt (n , +-comm n 1)
suc m ≟ zero = gt (m , +-comm m 1)
suc m ≟ suc n = Trichotomy-suc (m ≟ n)
