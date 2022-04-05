{-# OPTIONS --without-K #-}

module HoTT.Foundations.Function where

open import HoTT.Foundations.Prelude

_∘_ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ} {B : A → Type ℓ′} {C : (a : A) → B a → Type ℓ″}
        (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
