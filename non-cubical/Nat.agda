{-# OPTIONS --without-K #-}

open import HoTT.Foundations.Prelude
open import HoTT.Relation.Nullary
open import HoTT.Data.Sum
open import HoTT.Data.Nat public

data is-even : ℕ → Type₀
data is-odd  : ℕ → Type₀

data is-even where
  even-zero : is-even zero
  even-suc  : {n : ℕ} → is-odd n → is-even (suc n)

data is-odd where
  odd-suc : {n : ℕ} → is-even n → is-odd (suc n)
