{-# OPTIONS --without-K #-}

open import HoTT.Foundations.Prelude
open import HoTT.Data.Sigma
open import HoTT.Data.Nat renaming (_+_ to _+ℕ_) hiding (zero ; +-assoc)

ℤ : Type₀
ℤ = ℕ × ℕ

zero : ℤ
zero = (0 , 0)

-- fromℕ : ℕ → ℤ
-- fromℕ n = n , 0

infix 4 _≡ℤ_

_≡ℤ_ : ℤ → ℤ → Type₀
_≡ℤ_ (a , a') (b , b') = a +ℕ b' ≡ b +ℕ a'

-- TODO: we should really have a quotient type here...
postulate quotient : {m n : ℤ} → m ≡ℤ n → m ≡ n

postulate isSetℤ : isSet ℤ

neg : ℤ → ℤ
neg (a , a') = (a' , a)

neg-neg : (n : ℤ) → neg (neg n) ≡ n
neg-neg (a , a') = refl

infixl 6 _+_

_+_ : ℤ → ℤ → ℤ
(a , a') + (b , b') = a +ℕ b , a' +ℕ b'

+-inv-l : (n : ℤ) → neg n + n ≡ zero
+-inv-l (a , a') = quotient lem
  where
  lem =
    a' +ℕ a +ℕ 0 ≡⟨ +-zero (a' +ℕ a) ⟩
    a' +ℕ a ≡⟨ +-comm a' a ⟩
    a +ℕ a' ∎

-- +-inv-r : (n : ℤ) → n + neg n ≡ℤ zero
-- +-inv-r (a , a') = {!!}

zero-+ : (n : ℤ) → zero + n ≡ n
zero-+ (a , a') = refl

postulate +-assoc : (m n o : ℤ) → m + (n + o) ≡ (m + n) + o
