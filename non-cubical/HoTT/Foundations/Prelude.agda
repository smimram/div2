{-# OPTIONS --without-K --rewriting #-}

module HoTT.Foundations.Prelude where

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Setω  to Typeω )
open import Agda.Builtin.Sigma public

-- Universes

Type : (ℓ : Level) → Set (ℓ-suc ℓ)
Type ℓ = Set ℓ

Type₀ : Type (ℓ-suc ℓ-zero)
Type₀ = Type ℓ-zero

Type₁ : Type (ℓ-suc (ℓ-suc ℓ-zero))
Type₁ = Type (ℓ-suc ℓ-zero)

record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
  constructor lift
  field
    lower : A

open Lift public

-- Equality

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'
    x y z : A

infix 4 _≡_
data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : (y : A) → Type ℓ where 
  refl : x ≡ x

{-# BUILTIN REWRITE _≡_ #-}

sym : x ≡ y → y ≡ x
sym refl = refl

infixr 30 _∙_
_∙_ : x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

≡⟨⟩-syntax : (x : A) → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 2 ≡⟨⟩-syntax

_∎ : (x : A) → x ≡ x
_ ∎ = refl

subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
subst B refl b = b

coe : {A B : Type ℓ} → A ≡ B → A → B
coe p a = subst (λ A → A) p a

cong : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

PathP : (B : A → Type ℓ') (p : x ≡ y) → B x → B y → Type ℓ'
PathP B p bx by = subst B p bx ≡ by

toPathP : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} {p : x ≡ y} {x' : B x} {y' : B y} → subst B p x' ≡ y' → PathP B p x' y'
toPathP p = p

toConstPathP : {B : Type ℓ'} {p : x ≡ y} {x' y' : B} (q : x' ≡ y') → PathP (λ _ → B) p x' y'
toConstPathP {p = refl} q = q

-- h-levels

isContr : Type ℓ → Type ℓ
isContr A = Σ A (λ x → (∀ y → x ≡ y))

isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y

isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)

-- function extensionality

postulate
  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

funExt2 : ∀ {ℓ'} {C : (x : A) → B x → Type ℓ'} {f g : (x : A) → (y : B x) → C x y} → ((x : A) (y : B x) → f x y ≡ g x y) → f ≡ g
funExt2 p = funExt λ x → funExt λ y → p x y
