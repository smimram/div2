{-# OPTIONS --cubical #-}

module Ends where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum

-- ends of arrows : from src to tgt
data End : Set where
  src : End
  tgt : End

src≢tgt : ¬ (src ≡ tgt)
src≢tgt p = subst (λ { src → ⊤ ; tgt → ⊥ }) p tt

DiscreteEnd : Discrete End
DiscreteEnd src src = yes refl
DiscreteEnd src tgt = no (λ p → subst (λ { src → ⊤ ; tgt → ⊥ }) p tt)
DiscreteEnd tgt src = no (λ p → subst (λ { src → ⊥ ; tgt → ⊤ }) p tt)
DiscreteEnd tgt tgt = yes refl

End-isSet : isSet End
End-isSet = Discrete→isSet DiscreteEnd

case≡ : (e : End) → (e ≡ src) ⊎ (e ≡ tgt)
case≡ src = inl refl
case≡ tgt = inr refl

-- swap source and target
st : End → End
st src = tgt
st tgt = src

-- double swap is identity
st² : (e : End) → st (st e) ≡ e
st² src = refl
st² tgt = refl
