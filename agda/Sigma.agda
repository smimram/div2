{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma public

-- ×≡ : {ℓ ℓ' : Level} {A A' : Type ℓ} {B B' : Type ℓ'} → A ≡ A' → B ≡ B' → A × B ≡ A' × B'
-- ×≡ p q i = p i × q i
