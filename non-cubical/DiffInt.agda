{-# OPTIONS --without-K #-}

open import HoTT.Foundations.Prelude
-- open import HoTT.Foundations.HLevels
open import HoTT.Data.Sigma
open import HoTT.Data.Nat
-- open import HoTT.Data.DiffInt public
open import HoTT.HITs.SetQuotients
open import HoTT.Relation.Nullary.DecidableEq

-- isSetℤ : isSet ℤ
-- isSetℤ = Discrete→isSet discreteℤ

-- neg : ℤ → ℤ
-- neg [ a , a' ] = [ a' , a ]
-- neg (eq/ (a , a') (b , b') r i) = eq/ (a' , a) (b' , b) (+-comm a' b ∙ sym r ∙ +-comm a b') i
-- neg (squash/ m n e f i j) = isSet→isSet' isSetℤ (cong neg e) (cong neg f) refl refl i j

-- neg-neg : (n : ℤ) → neg (neg n) ≡ n
-- neg-neg [ a , a' ] = refl
-- neg-neg (eq/ (a , a') (b , b') r i) = {!!}
-- neg-neg (squash/ n n₁ p q i i₁) = {!!}

-- -- _+ℤ_ : ℤ → ℤ → ℤ
-- -- [ a , a' ] +ℤ [ b , b' ] = [ a + b' , b + a' ]
-- -- [ a , a' ] +ℤ eq/ (b , b') (c , c') e i = isSetℤ {!!} {!!} {!!} {!!} {!!} i
-- -- [ a ] +ℤ squash/ b b₁ p q i i₁ = {!!}
-- -- eq/ a b₁ r i +ℤ b = {!!}
-- -- squash/ a a₁ p q i i₁ +ℤ b = {!!}
