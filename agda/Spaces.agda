{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Fiberwise as Fiberwise hiding (totalEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Fibration
open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Z as ℤ hiding (_<_ ; _≤_ ; _≟_)
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Nat as ℕ
open import Misc
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetTruncation as ∥∥₂
open import Cubical.HITs.SetQuotients as []

open import Ends

module Spaces {ℓ} {A B : Type ℓ} (equiv : (A × End) ≃ (B × End)) where

-- functoriality of 0-truncation

∥∥₂-map : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → ∥ A ∥₂ → ∥ B ∥₂
∥∥₂-map f = ∥∥₂.rec isSetSetTrunc (λ a → ∣ f a ∣₂)

∥∥₂-map-id : {ℓ : Level} {A : Type ℓ} (a : ∥ A ∥₂) → ∥∥₂-map (idfun A) a ≡ a
∥∥₂-map-id a = ∥∥₂.elim {B = λ a → ∥∥₂-map (λ a → a) a ≡ a} (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ _ → refl) a

∥∥₂-map-id-ext : {ℓ : Level} {A : Type ℓ} (f : A → A) → ((a : A) → f a ≡ a) → (a : ∥ A ∥₂) → ∥∥₂-map f a ≡ a
∥∥₂-map-id-ext f is-id a = cong (λ f → ∥∥₂-map f a) (funExt is-id) ∙ ∥∥₂-map-id a

∥∥₂-map-comp : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (g : B → C) (f : A → B) (a : ∥ A ∥₂) → ∥∥₂-map g (∥∥₂-map f a) ≡ ∥∥₂-map (g ∘ f) a
∥∥₂-map-comp g f a = ∥∥₂.elim {B = λ a → ∥∥₂-map g (∥∥₂-map f a) ≡ ∥∥₂-map (g ∘ f) a} (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ _ → refl) a

∥∥₂-rec₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          isSet C → (A → B → C) → (∥ A ∥₂ → ∥ B ∥₂ → C)
∥∥₂-rec₂ {B = B} {C = C} S f a b = ∥∥₂.rec (isSetΠ (λ _ → S)) (λ a b → ∥∥₂.rec S (λ b → f a b) b) a b

∥∥₂-map₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          (A → B → C) → (∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂)
∥∥₂-map₂ f = ∥∥₂-rec₂ isSetSetTrunc λ a b → ∣ f a b ∣₂

map₂ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {a a' : A} (f : A → B) → ∣ a ∣₂ ≡ ∣ a' ∣₂ → ∣ f a ∣₂ ≡ ∣ f a' ∣₂
map₂ f p = cong (∥∥₂-map f) p

-- equivalences are compatible with 0-truncation
∥∥₂-equiv : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
           A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
∥∥₂-equiv {_} {_} {A} {B} e = isoToEquiv i
  where
  i : Iso ∥ A ∥₂ ∥ B ∥₂
  Iso.fun i = ∥∥₂-map (equivFun e)
  Iso.inv i = ∥∥₂-map (invEq e)
  Iso.rightInv i b = ∥∥₂-map-comp _ _ b ∙ funExt⁻ (cong ∥∥₂-map (funExt (secEq e))) b ∙ ∥∥₂-map-id b
  Iso.leftInv i a = ∥∥₂-map-comp _ _ a ∙ funExt⁻ (cong ∥∥₂-map (funExt (retEq e))) a ∙ ∥∥₂-map-id a

-- the total space is the sum of the fibers
Σ-components : {ℓ : Level} (A : Type ℓ) → A ≃ Σ ∥ A ∥₂ (fiber ∣_∣₂)
Σ-components A = totalEquiv ∣_∣₂

-- fiberwise equivalence: an equivalence between the total space induces an
-- equivalence between the fibers
-- equiv-fib : {ℓ : Level} {A A' B : Type ℓ} →
            -- (f : A → B) (e : A ≃ A') (b : B) → fiber f b ≃ fiber (f ∘ invEq e) b
-- equiv-fib f e b = {!!}

-- ∥∥₂-equiv-fib' : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               -- (e : A ≃ B) (x : ∥ A ∥₂) → fiber ∣_∣₂ x ≃ fiber ∣_∣₂ (∥∥₂-map (equivFun e) x)
-- ∥∥₂-equiv-fib' e x = compEquiv (equiv-fib ∣_∣₂ e x) {!!}

∥∥₂-equiv-fib : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               (e : A ≃ B) (x : ∥ A ∥₂) → fiber ∣_∣₂ x ≃ fiber ∣_∣₂ (∥∥₂-map (equivFun e) x)
∥∥₂-equiv-fib e x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₂ x) (fiber ∣_∣₂ (∥∥₂-map (equivFun e) x))
  Iso.fun i (a , p) = equivFun e a , cong (∥∥₂-map (equivFun e)) p
  Iso.inv i (b , p) = invEq e b , cong (∥∥₂-map (invEq e)) p ∙ retEq (∥∥₂-equiv e) x
  Iso.rightInv i (b , p) = Σ≡Prop (λ _ → isSetSetTrunc _ _) (secEq e b)
  Iso.leftInv i (a , p) = Σ≡Prop (λ _ → isSetSetTrunc _ _) (retEq e a)

-- fiberwise equivalence: conversely, if we have equivalent base and fibers then
-- we are equivalent
glueing-equiv : {ℓ ℓ' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≡ B)
                → ((x : A) → P x ≡ Q (transport p x))
                → Σ A P ≡ Σ B Q
glueing-equiv {A = A} {Q = Q} p f = cong (Σ A) (funExt f) ∙ Σ-cong-fst p

glueing-equiv' : {ℓ ℓ' ℓ'' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≃ B)
                → ((x : A) → P x ≃ Q (equivFun p x))
                → Σ A P ≃ Σ B Q
glueing-equiv' {A = A} {B = B} {P = P} {Q = Q} p f = isoToEquiv (Σ-cong-iso (equivToIso p) (equivToIso ∘ f))

-- set truncation commutes with multiplication by a set
∥∥₂×set : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → isSet B → ∥ A × B ∥₂ ≃ ∥ A ∥₂ × B
∥∥₂×set {A = A} {B = B} SB = isoToEquiv i
  where
  f : ∥ A × B ∥₂ → ∥ A ∥₂ × B
  f = ∥∥₂.rec (isSet× isSetSetTrunc SB) λ { (a , t) → ∣ a ∣₂ , t }
  g : ∥ A ∥₂ × B → ∥ A × B ∥₂
  g (a , t) = ∥∥₂.rec isSetSetTrunc (λ a → ∣ a , t ∣₂) a
  i : Iso ∥ A × B ∥₂ (∥ A ∥₂ × B)
  Iso.fun i = f
  Iso.inv i = g
  Iso.rightInv i (a , t) = ∥∥₂.elim {B = λ a → f (g (a , t)) ≡ (a , t)} (λ _ → isProp→isSet (isSet× isSetSetTrunc SB _ _)) (λ a → refl) a
  Iso.leftInv i a = ∥∥₂.elim {B = λ a → g (f a) ≡ a} (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ { (a , t) → refl }) a

-- set trucation  commutes with disjoint union
∥∥₂⊎ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → ∥ A ⊎ B ∥₂ ≃ ∥ A ∥₂ ⊎ ∥ B ∥₂
∥∥₂⊎ {_} {_} {A} {B} = isoToEquiv i
  where
  F : ∥ A ⊎ B ∥₂ → ∥ A ∥₂ ⊎ ∥ B ∥₂
  F = ∥∥₂.rec (isSet⊎ isSetSetTrunc isSetSetTrunc) λ { (inl a) → inl ∣ a ∣₂ ; (inr b) → inr ∣ b ∣₂ }
  G : ∥ A ∥₂ ⊎ ∥ B ∥₂ → ∥ A ⊎ B ∥₂
  G (inl a) = ∥∥₂.rec isSetSetTrunc (λ a → ∣ inl a ∣₂) a
  G (inr b) = ∥∥₂.rec isSetSetTrunc (λ b → ∣ inr b ∣₂) b
  i : Iso ∥ A ⊎ B ∥₂ (∥ A ∥₂ ⊎ ∥ B ∥₂)
  Iso.fun i = F
  Iso.inv i = G
  Iso.rightInv i (inl a) = ∥∥₂.elim {B = λ a → F (G (inl a)) ≡ inl a} (λ _ → isProp→isSet (isSet⊎ isSetSetTrunc isSetSetTrunc _ _)) (λ _ → refl) a
  Iso.rightInv i (inr b) = ∥∥₂.elim {B = λ b → F (G (inr b)) ≡ inr b} (λ _ → isProp→isSet (isSet⊎ isSetSetTrunc isSetSetTrunc _ _)) (λ _ → refl) b
  Iso.leftInv i x = ∥∥₂.elim {B = λ x → G (F x) ≡ x} (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ { (inl a) → refl ; (inr b) → refl }) x

-- set truncation commutes with taking subtypes
∥∥₂ΣP : {ℓ ℓ' : Level} {A : Type ℓ} (P : A → Type ℓ') (prop : (a : A) → isProp (P a)) → ∥ Σ A P ∥₂ ≃ Σ ∥ A ∥₂ (fst ∘ (∥∥₂.rec isSetHProp λ a → P a , prop a))
∥∥₂ΣP {A = A} P prop = isoToEquiv i
  where
  P' : ∥ A ∥₂ → Type _
  P' = fst ∘ (∥∥₂.rec isSetHProp λ a → P a , prop a)
  F : ∥ Σ A P ∥₂ → Σ ∥ A ∥₂ P'
  F = ∥∥₂.rec (isSetΣ isSetSetTrunc (λ a → ∥∥₂.elim {B = λ a → isSet (P' a)} (λ _ → isProp→isSet isPropIsSet) (λ a → isProp→isSet (prop a)) a)) λ { (a , p) → ∣ a ∣₂ , p }
  G : Σ ∥ A ∥₂ P' → ∥ Σ A P ∥₂
  G (a , p) = ∥∥₂.elim {B = λ a → P' a → ∥ Σ A P ∥₂} (λ _ → isSetΠ λ _ → isSetSetTrunc) (λ a Pa → ∣ a , Pa ∣₂) a p
  i : Iso ∥ Σ A P ∥₂ (Σ ∥ A ∥₂ P')
  Iso.fun i = F
  Iso.inv i = G
  Iso.rightInv i (a , p) = Σ≡Prop (λ a → ∥∥₂.elim {B = λ a → isProp (P' a)} (λ _ → isProp→isSet isPropIsProp) prop a) (∥∥₂.elim {B = λ a → (p : P' a) → F (G (a , p)) .fst ≡ a} (λ _ → isProp→isSet (isPropΠ λ _ → isSetSetTrunc _ _)) (λ a p → refl) a p)
  Iso.leftInv i = ∥∥₂.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) λ { (a , p) → refl}

--
-- import previous work on division by 2 on sets obtained by set truncation

A₂isSet : isSet ∥ A ∥₂
A₂isSet = isSetSetTrunc

B₂isSet : isSet ∥ B ∥₂
B₂isSet = isSetSetTrunc

A₂E≃B₂E : ∥ A ∥₂ × End ≃ ∥ B ∥₂ × End
A₂E≃B₂E = compEquiv (invEquiv (∥∥₂×set End-isSet)) (compEquiv (∥∥₂-equiv equiv) (∥∥₂×set End-isSet))

open import Ends
import Arrows A₂isSet B₂isSet A₂E≃B₂E as AS
import Div2 A₂isSet B₂isSet A₂E≃B₂E as DS
import Div2Reach A₂isSet B₂isSet A₂E≃B₂E as DRS
open import ArrowsBase equiv

open import Partition

f' : ∥ A ∥₂ → ∥ B ∥₂
f' = equivFun DS.Conway

g' : ∥ B ∥₂ → ∥ A ∥₂
g' = invEq DS.Conway

-- connected component
cc : dArrows → ∥ dArrows ∥₂
cc = ∣_∣₂

-- elements of the connected component
el-cc : ∥ dArrows ∥₂ → Type _
el-cc = fiber cc

-- alternative characterization
el-cc' : {ℓ : Level} {A : Type ℓ} (a : A) → (fiber ∣_∣₂ ∣ a ∣₂) ≃ (Σ[ a' ∈ A ] ∥ a ≡ a' ∥₁)
el-cc' {ℓ} {A = A} a = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₂ ∣ a ∣₂) (Σ[ a' ∈ A ] ∥ a ≡ a' ∥₁)
  Iso.fun i (a' , p) = a' , lem (sym p)
    where
    F : A → hProp _
    F a' = ∥ a ≡ a' ∥₁ , isPropPropTrunc
    lem : {a' : A} → ∣ a ∣₂ ≡ ∣ a' ∣₂ → ∥ a ≡ a' ∥₁
    lem {a'} p = subst (fst ∘ (∥∥₂.rec isSetHProp F)) p ∣ refl ∣₁
  Iso.inv i (a' , p) = a' , ∥∥.rec (isSetSetTrunc _ _) (λ p → cong ∣_∣₂ (sym p)) p
  Iso.rightInv i (a' , p) = Σ≡Prop (λ _ → isPropPropTrunc) refl
  Iso.leftInv i (a' , p) = Σ≡Prop (λ _ → isSetSetTrunc _ _) refl

-- next is a fiberwise equivalence
next≃f : {o : dArrows} → el-cc (cc o) ≃ el-cc (cc (next o))
-- next≃f {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc (cc o)) (el-cc (cc (next o)))
  -- Iso.fun i (a , p) = next a , map₂ next p
  -- Iso.inv i (a , p) = prev a , map₂ prev p ∙ cong ∣_∣₂ (prev-next o)
  -- Iso.rightInv i (a , p) = ΣPathP (next-prev a , toPathP (isSetSetTrunc _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (prev-next a , toPathP (isSetSetTrunc _ _ _ _))
next≃f {o} = ∥∥₂-equiv-fib next≃ (cc o)

prev≃f : {o : dArrows} → el-cc (cc o) ≃ el-cc (cc (prev o))
-- prev≃f {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc (cc o)) (el-cc (cc (prev o)))
  -- Iso.fun i (a , p) = prev a , map₂ prev p
  -- Iso.inv i (a , p) = next a , map₂ next p ∙ cong ∣_∣₂ (next-prev o)
  -- Iso.rightInv i (a , p) = ΣPathP (prev-next a , toPathP (isSetSetTrunc _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (next-prev a , toPathP (isSetSetTrunc _ _ _ _))
prev≃f {o} = ∥∥₂-equiv-fib (invEquiv next≃) (cc o)

-- reachable≃f' : {a b : Arrows} → reachable-arr a b → el-cc (cc a) ≃ el-cc (cc b)
-- reachable≃f' r = ?

-- reachable≃f : {a b : dArrows} → reachable a b → el-cc (cc a) ≃ el-cc (cc b)
-- reachable≃f {a} {b} (n , p) = ℤ.elim E Z N P P
  -- (λ n F → toPathP (funExt₃ (PN n F))) -- (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt (λ c → Σ≡Prop (λ _ → isSetSetTrunc _ _) {!!}))))) -- essentially prev-next
  -- (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt λ c → Σ≡Prop (λ _ → isSetSetTrunc _ _) {!!})))) -- essentially next-prev
  -- n a b p
  -- where
  -- E : (n : ℤ) → Type ℓ
  -- E n = (a b : dArrows) → iterate n a ≡ b → el-cc (cc a) ≃ el-cc (cc b)
  -- Z : E zero
  -- Z a b p = pathToEquiv (cong (el-cc ∘ cc) p)
  -- N : (n : ℤ) → E n → E (suc n)
  -- N n H a b p = compEquiv (H a (prev b) (sym (prev-next _) ∙ cong prev p)) (compEquiv next≃f (pathToEquiv (cong (el-cc ∘ cc) (next-prev b))))
  -- P : (n : ℤ) → E n → E (pred n)
  -- P n H a b p = compEquiv (H a (next b) (sym (next-prev _) ∙ cong next p)) (compEquiv prev≃f (pathToEquiv (cong (el-cc ∘ cc) (prev-next b))))
  -- PN : (n : ℤ) (F : E n) (a b : dArrows) (p : iterate (predl-suc n i1) a ≡ b) → transport (cong E (predl-suc n)) (P (suc n) (N n F)) a b p ≡ F a b p
  -- PN n F a b p = {!!}
    -- where
    -- Nfst : (n : ℤ) (F : E n) (a b : dArrows) (p : next (iterate n a) ≡ b) → N n F a b p .fst ≡ subst (el-cc ∘ cc) (next-prev b) ∘ equivFun next≃f ∘ F a (prev b) (sym (prev-next (iterate n a)) ∙ cong prev p) .fst
    -- Nfst n F a b p = refl
    -- Pfst : (n : ℤ) (F : E n) (a b : dArrows) (p : prev (iterate n a) ≡ b) → P n F a b p .fst ≡ subst (el-cc ∘ cc) (prev-next b) ∘ equivFun prev≃f ∘ F a (next b) (sym (next-prev (iterate n a)) ∙ cong next p) .fst
    -- Pfst n F a b p = refl
    -- lem : transport (cong E (predl-suc n)) (P (suc n) (N n F)) a b p .fst ≡ F a b p .fst
    -- lem =
      -- subst E (predl-suc n) (P (suc n) (N n F)) a b p .fst ≡⟨ refl ⟩
      -- subst (el-cc ∘ cc) (prev-next b) ∘ equivFun prev≃f ∘ subst (el-cc ∘ cc) (next-prev (next b)) ∘ equivFun next≃f ∘ F a (prev (next b)) {!!} .fst ≡⟨ {!!} ⟩
      -- subst (el-cc ∘ cc) {!prev-next b!} ∘ {!!} ≡⟨ {!!} ⟩
      -- F a b p .fst ∎



  -- PN' : (n : ℤ) (F : E n) (a b : dArrows) (p : iterate (predl-suc n i1) a ≡ b) (c : el-cc ∣ a ∣₂) →
       -- transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₂) c))) ≡ F a b p .fst c .fst
  -- PN' n F a b p c =
    -- transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₂) c))) ≡⟨ transportRefl _ ⟩
    -- fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₂) c)) ≡⟨ {!!} ⟩
    -- fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₂) c)) ≡⟨ {!!} ⟩
    -- F a b p .fst c .fst ∎

dArrows₂ : Type _
dArrows₂ = ∥ dArrows ∥₂

iterate₂ : ℤ → dArrows₂ → dArrows₂
iterate₂ n = ∥∥₂-map (iterate n)

reachable₂ : dArrows₂ → dArrows₂ → Type _
reachable₂ a b = Σ[ n ∈ ℤ ] iterate₂ n a ≡ b

dArrowsS₂ : AS.dArrows ≃ dArrows₂
dArrowsS₂ =
  AS.dArrows            ≃⟨ idEquiv _ ⟩
  (∥ A ∥₂ ⊎ ∥ B ∥₂) × End ≃⟨ cong≃ (λ X → X × End) (invEquiv ∥∥₂⊎) ⟩
  ∥ A ⊎ B ∥₂ × End       ≃⟨ invEquiv (∥∥₂×set End-isSet) ⟩
  ∥ dArrows ∥₂           ■

dArrowsS→0 : AS.dArrows → dArrows₂
dArrowsS→0 = equivFun dArrowsS₂

reachableS→0 : {a b : AS.dArrows} → AS.reachable a b → reachable₂ (dArrowsS→0 a) (dArrowsS→0 b)
reachableS→0 {a = a} (n , r) = n , {!!} ∙ cong dArrowsS→0 r

prev₂ : dArrows₂ → dArrows₂
prev₂ = ∥∥₂-map prev

next₂ : dArrows₂ → dArrows₂
next₂ = ∥∥₂-map next

next-prev₂ : (a : dArrows₂) → next₂ (prev₂ a) ≡ a
next-prev₂ a = ∥∥₂-map-comp next prev a ∙ ∥∥₂-map-id-ext _ next-prev a

prev-next₂ : (a : dArrows₂) → prev₂ (next₂ a) ≡ a
prev-next₂ a = ∥∥₂-map-comp prev next a ∙ ∥∥₂-map-id-ext _ prev-next a

iterate-suc₂ : (n : ℤ) (a : dArrows₂) → iterate₂ (suc n) a ≡ next₂ (iterate₂ n a)
iterate-suc₂ n a = sym (∥∥₂-map-comp next (iterate n) a)

iterate-pred₂ : (n : ℤ) (a : dArrows₂) → iterate₂ (pred n) a ≡ prev₂ (iterate₂ n a)
iterate-pred₂ n a = sym (∥∥₂-map-comp prev (iterate n) a)

Arrows₂ = ∥ Arrows ∥₂

ArrowsS₂ : AS.Arrows ≃ Arrows₂
ArrowsS₂ = invEquiv ∥∥₂⊎

ArrowsS→0 : AS.Arrows → Arrows₂
ArrowsS→0 = equivFun ArrowsS₂

Arrows0→S : Arrows₂ → AS.Arrows
Arrows0→S = invEq ArrowsS₂

fw₂ : Arrows₂ → dArrows₂
fw₂ a = dArrowsS→0 (AS.fw (invEq ArrowsS₂ a))

bw₂ : Arrows₂ → dArrows₂
bw₂ a = dArrowsS→0 (AS.bw (invEq ArrowsS₂ a))

orient₂ : Arrows₂ → End → dArrows₂
orient₂ a e = dArrowsS→0 (Arrows0→S a , e)

-- next is a fiberwise equivalence
next≃f' : {o : ∥ dArrows ∥₂} → el-cc o ≃ el-cc (next₂ o)
-- next≃f' {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc o) (el-cc (∥∥₂-map next o))
  -- Iso.fun i (a , p) = next a , cong next₂ p
  -- Iso.inv i (a , p) = prev a , cong prev₂ p ∙ ∥∥₂-map-comp next prev o ∙ cong (λ f → ∥∥₂-map f o) (funExt prev-next) ∙ ∥∥₂-map-id o
  -- Iso.rightInv i (a , p) = ΣPathP (next-prev a , toPathP (isSetSetTrunc _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (prev-next a , (toPathP (isSetSetTrunc _ _ _ _)))
next≃f' {o} = ∥∥₂-equiv-fib next≃ o

prev≃f' : {o : ∥ dArrows ∥₂} → el-cc o ≃ el-cc (prev₂ o)
prev≃f' {o} = ∥∥₂-equiv-fib (invEquiv next≃) o

reachable≃f' : {a b : ∥ dArrows ∥₂} → reachable₂ a b → el-cc a ≃ el-cc b
reachable≃f' {a} {b} (n , p) = ℤ.elim E Z N P P PN {!!} n a b p
  where
  E : (n : ℤ) → Type ℓ
  E n = (a b : dArrows₂) → iterate₂ n a ≡ b → el-cc a ≃ el-cc b
  Z : E zero
  Z a b p = pathToEquiv (cong el-cc (sym (∥∥₂-map-id a) ∙ p))
  N : (n : ℤ) → E n → E (suc n)
  N n H a b p = compEquiv (H a (prev₂ b) (lem ∙ cong prev₂ p)) (compEquiv next≃f' (pathToEquiv (cong el-cc (next-prev₂ b))))
    where
    lem =
      iterate₂ n a                 ≡⟨ sym (prev-next₂ _) ⟩
      prev₂ (next₂ (iterate₂ n a)) ≡⟨ sym (cong prev₂ (iterate-suc₂ n a)) ⟩
      prev₂ (iterate₂ (suc n) a)   ∎
  P : (n : ℤ) → E n → E (pred n)
  P n H a b p = compEquiv (H a (next₂ b) (sym (next-prev₂ _) ∙ sym (cong next₂ (iterate-pred₂ n a)) ∙ cong next₂ p)) (compEquiv prev≃f' (pathToEquiv (cong el-cc (prev-next₂ b))))
  PN : (n : ℤ) (H : E n) → PathP (λ i → E (predl-suc n i)) (P (suc n) (N n H)) H
  PN n H = toPathP (funExt₃ {!!})

-- NB: the lemmas below do not seem to be specific to ∣_∣₂

-- the fiber of a subtype is the same as the original fiber
-- Note: probably not the most elegant proof...
fiber-sub : {ℓ : Level} {A : Type ℓ} (P : A → Type ℓ) → ((x : A) → isProp (P x)) →
            (x : ∥ Σ A P ∥₂) → fiber ∣_∣₂ x ≃ fiber ∣_∣₂ (∥∥₂-map fst x)
fiber-sub {A = A} P prop x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₂ x) (fiber ∣_∣₂ (∥∥₂-map fst x))
  Iso.fun i ((a , p) , q) = a , cong (∥∥₂-map fst) q
  Iso.inv i (a , q) = (a , subst P' a'≡a₂ P'a') , lem'
    where
    P' : ∥ A ∥₂ → Type _
    P' = fst ∘ ∥∥₂.rec isSetHProp (λ a → P a , prop a)
    aPa : Σ ∥ A ∥₂ P'
    aPa = equivFun (∥∥₂ΣP P prop) x
    a' : ∥ A ∥₂
    a' = fst aPa
    P'a' : P' a'
    P'a' = snd aPa
    lem1 : (x : ∥ Σ A P ∥₂) → fst (equivFun (∥∥₂ΣP P prop) x) ≡ ∥∥₂-map fst x
    lem1 x = ∥∥₂.elim {B = λ x → fst (equivFun (∥∥₂ΣP P prop) x) ≡ ∥∥₂-map fst x} (λ _ → isProp→isSet (isSetSetTrunc _ _)) (λ { (a , p) → refl}) x
    a'≡a₂ : a' ≡ ∣ a ∣₂
    a'≡a₂ = lem1 x ∙ sym q
    lem' =
      ∣ a , subst P' a'≡a₂ P'a' ∣₂ ≡⟨ sym (retEq (∥∥₂ΣP P prop) ∣ a , subst P' a'≡a₂ P'a' ∣₂) ⟩
      invEq (∥∥₂ΣP P prop) (equivFun (∥∥₂ΣP P prop) ∣ a , subst P' a'≡a₂ P'a' ∣₂) ≡⟨ cong (invEq (∥∥₂ΣP P prop)) (ΣPathP (sym a'≡a₂ , toPathP _)) ⟩
      invEq (∥∥₂ΣP P prop) (equivFun (∥∥₂ΣP P prop) x) ≡⟨ retEq (∥∥₂ΣP P prop) x ⟩
      x ∎
  Iso.rightInv i (a , q) = Σ≡Prop (λ _ → isSetSetTrunc _ _) refl
  Iso.leftInv i ((a , p) , q) = Σ≡Prop (λ _ → isSetSetTrunc _ _) (Σ≡Prop prop refl)

fiber-inl : {ℓ : Level} {A B : Type ℓ} (a : ∥ A ∥₂) → fiber ∣_∣₂ a ≃ fiber ∣_∣₂ (∥∥₂-map (inl {B = B}) a)
fiber-inl {B = B} a =
  fiber ∣_∣₂ a                                  ≃⟨ ∥∥₂-equiv-fib (inl≃ {B = B}) a ⟩
  fiber ∣_∣₂ (∥∥₂-map (equivFun inl≃) a)         ≃⟨ fiber-sub in-left in-left-isProp (∥∥₂-map (equivFun inl≃) a) ⟩
  fiber ∣_∣₂ (∥∥₂-map fst (∥∥₂-map (fst inl≃) a)) ≃⟨ pathToEquiv (cong (fiber ∣_∣₂) (∥∥₂-map-comp fst (fst inl≃) a)) ⟩
  fiber ∣_∣₂ (∥∥₂-map (inl {B = B}) a)           ■

fiber-inr : {ℓ : Level} {A B : Type ℓ} (a : ∥ B ∥₂) → fiber ∣_∣₂ a ≃ fiber ∣_∣₂ (∥∥₂-map (inr {A = A}) a)
fiber-inr {A = A} a =
  fiber ∣_∣₂ a                                  ≃⟨ ∥∥₂-equiv-fib (inr≃ {A = A}) a ⟩
  fiber ∣_∣₂ (∥∥₂-map (equivFun inr≃) a)         ≃⟨ fiber-sub in-right in-right-isProp (∥∥₂-map (equivFun inr≃) a) ⟩
  fiber ∣_∣₂ (∥∥₂-map fst (∥∥₂-map (fst inr≃) a)) ≃⟨ pathToEquiv (cong (fiber ∣_∣₂) (∥∥₂-map-comp fst (fst inr≃) a)) ⟩
  fiber ∣_∣₂ (∥∥₂-map (inr {A = A}) a)           ■

Div2 : A ≃ B
Div2 = compEquiv (Σ-components A) (compEquiv (glueing-equiv' DS.Conway fiber-equiv) (invEquiv (Σ-components B)))
  where
  fiber-equiv : (a : ∥ A ∥₂) → fiber ∣_∣₂ a ≃ fiber ∣_∣₂ (equivFun DS.Conway a)
  fiber-equiv a =
    fiber ∣_∣₂ a                                                                                    ≃⟨ fiber-inl a ⟩
    fiber ∣_∣₂ (ArrowsS→0 (inl a))                                                                  ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (fw₂ (ArrowsS→0 (inl a)))                                                                 ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (dArrowsS→0 (AS.fw (inl a)))                                                              ≃⟨ reachable≃f' (reachableS→0 (AS.reachable-arr→reachable' (DRS.Conway-reachable a))) ⟩
    el-cc (dArrowsS→0 (inr (DRS.ConwayFun a) , AS.reachable-end (DRS.Conway-reachable a)))          ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (orient₂ (ArrowsS→0 (inr (DRS.ConwayFun a))) (AS.reachable-end (DRS.Conway-reachable a))) ≃⟨ {!!} ⟩ -- similar administrative step
    fiber ∣_∣₂ (ArrowsS→0 (inr (DRS.ConwayFun a)))                                                  ≃⟨ invEquiv (fiber-inr _) ⟩
    fiber ∣_∣₂ (equivFun DS.Conway a)                                                               ■
