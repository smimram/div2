{-# OPTIONS --without-K --allow-unsolved-metas #-}

module HoTT.Foundations.HLevels where

open import HoTT.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B : A → Type ℓ'
    C : (x : A) → B x → Type ℓ''
    D : (x : A) (y : B x) → C x y → Type ℓ
    

isSet→isSet' : isSet A → isSet A
isSet→isSet' {A = A} Aset = Aset

isPropΠ : (h : (x : A) → isProp (B x)) → isProp ((x : A) → B x)
isPropΠ h f g = funExt λ x → h x (f x) (g x)

isPropΠ2 : (h : (x : A) (y : B x) → isProp (C x y))
         → isProp ((x : A) (y : B x) → C x y)
isPropΠ2 h = isPropΠ λ x → isPropΠ λ y → h x y

isPropΠ3 : (h : (x : A) (y : B x) (z : C x y) → isProp (D x y z))
         → isProp ((x : A) (y : B x) (z : C x y) → D x y z)
isPropΠ3 h = isPropΠ λ x → isPropΠ λ y → isPropΠ λ z → h x y z
