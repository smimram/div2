{-# OPTIONS --without-K #-}

module HoTT.Relation.Nullary.DecidableEq where

open import HoTT.Foundations.Prelude
open import HoTT.Relation.Nullary

postulate
  -- Hedberg's theorem
  Discrete→isSet : ∀ {ℓ} {A : Type ℓ} → Discrete A → isSet A
