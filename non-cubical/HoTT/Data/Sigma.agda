{-# OPTIONS --without-K #-}

module HoTT.Data.Sigma where

open import HoTT.Foundations.Prelude

infixr 5 _×_

_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A × B = Σ A (λ _ → B)

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'

ΣPathP : {x y : Σ A B}
  → Σ (fst x ≡ fst y) (λ a≡ → PathP B a≡ (snd x) (snd y))
  → x ≡ y
ΣPathP (refl , refl) = refl

