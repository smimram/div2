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
open import Cubical.Relation.Nullary.DecidableEq
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
open import Cubical.HITs.SetTruncation as ∥∥₀
open import Cubical.HITs.SetQuotients as []

open import Ends

module Spaces {ℓ} {A B : Type ℓ} (equiv : (A × End) ≃ (B × End)) where

-- functoriality of 0-truncation

∥∥₀-map : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → ∥ A ∥₀ → ∥ B ∥₀
∥∥₀-map f = ∥∥₀.rec setTruncIsSet (λ a → ∣ f a ∣₀)

∥∥₀-map-id : {ℓ : Level} {A : Type ℓ} (a : ∥ A ∥₀) → ∥∥₀-map (idfun A) a ≡ a
∥∥₀-map-id a = ∥∥₀.elim {B = λ a → ∥∥₀-map (λ a → a) a ≡ a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ _ → refl) a

∥∥₀-map-id-ext : {ℓ : Level} {A : Type ℓ} (f : A → A) → ((a : A) → f a ≡ a) → (a : ∥ A ∥₀) → ∥∥₀-map f a ≡ a
∥∥₀-map-id-ext f is-id a = cong (λ f → ∥∥₀-map f a) (funExt is-id) ∙ ∥∥₀-map-id a

∥∥₀-map-comp : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (g : B → C) (f : A → B) (a : ∥ A ∥₀) → ∥∥₀-map g (∥∥₀-map f a) ≡ ∥∥₀-map (g ∘ f) a
∥∥₀-map-comp g f a = ∥∥₀.elim {B = λ a → ∥∥₀-map g (∥∥₀-map f a) ≡ ∥∥₀-map (g ∘ f) a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ _ → refl) a

∥∥₀-rec₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          isSet C → (A → B → C) → (∥ A ∥₀ → ∥ B ∥₀ → C)
∥∥₀-rec₂ {B = B} {C = C} S f a b = ∥∥₀.rec (isSetΠ (λ _ → S)) (λ a b → ∥∥₀.rec S (λ b → f a b) b) a b

∥∥₀-map₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          (A → B → C) → (∥ A ∥₀ → ∥ B ∥₀ → ∥ C ∥₀)
∥∥₀-map₂ f = ∥∥₀-rec₂ setTruncIsSet λ a b → ∣ f a b ∣₀

map₀ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {a a' : A} (f : A → B) → ∣ a ∣₀ ≡ ∣ a' ∣₀ → ∣ f a ∣₀ ≡ ∣ f a' ∣₀
map₀ f p = cong (∥∥₀-map f) p

-- equivalences are compatible with 0-truncation
∥∥₀-equiv : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
           A ≃ B → ∥ A ∥₀ ≃ ∥ B ∥₀
∥∥₀-equiv {_} {_} {A} {B} e = isoToEquiv i
  where
  i : Iso ∥ A ∥₀ ∥ B ∥₀
  Iso.fun i = ∥∥₀-map (equivFun e)
  Iso.inv i = ∥∥₀-map (invEq e)
  Iso.rightInv i b = ∥∥₀-map-comp _ _ b ∙ funExt⁻ (cong ∥∥₀-map (funExt (retEq e))) b ∙ ∥∥₀-map-id b
  Iso.leftInv i a = ∥∥₀-map-comp _ _ a ∙ funExt⁻ (cong ∥∥₀-map (funExt (secEq e))) a ∙ ∥∥₀-map-id a

-- the total space is the sum of the fibers
Σ-components : {ℓ : Level} (A : Type ℓ) → A ≃ Σ ∥ A ∥₀ (fiber ∣_∣₀)
Σ-components A = totalEquiv ∣_∣₀

-- fiberwise equivalence: an equivalence between the total space induces an
-- equivalence between the fibers
-- equiv-fib : {ℓ : Level} {A A' B : Type ℓ} →
            -- (f : A → B) (e : A ≃ A') (b : B) → fiber f b ≃ fiber (f ∘ invEq e) b
-- equiv-fib f e b = {!!}

-- ∥∥₀-equiv-fib' : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               -- (e : A ≃ B) (x : ∥ A ∥₀) → fiber ∣_∣₀ x ≃ fiber ∣_∣₀ (∥∥₀-map (equivFun e) x)
-- ∥∥₀-equiv-fib' e x = compEquiv (equiv-fib ∣_∣₀ e x) {!!}

∥∥₀-equiv-fib : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               (e : A ≃ B) (x : ∥ A ∥₀) → fiber ∣_∣₀ x ≃ fiber ∣_∣₀ (∥∥₀-map (equivFun e) x)
∥∥₀-equiv-fib e x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ x) (fiber ∣_∣₀ (∥∥₀-map (equivFun e) x))
  Iso.fun i (a , p) = equivFun e a , cong (∥∥₀-map (equivFun e)) p
  Iso.inv i (b , p) = invEq e b , cong (∥∥₀-map (invEq e)) p ∙ secEq (∥∥₀-equiv e) x
  Iso.rightInv i (b , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (retEq e b)
  Iso.leftInv i (a , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (secEq e a)

-- fiberwise equivalence: conversely, if we have equivalent base and fibers then
-- we are equivalent
glueing-equiv : {ℓ ℓ' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≡ B)
                → ((x : A) → P x ≡ Q (transport p x))
                → Σ A P ≡ Σ B Q
glueing-equiv {A = A} {Q = Q} p f = cong (Σ A) (funExt f) ∙ Σ-ap₁ p

glueing-equiv' : {ℓ ℓ' ℓ'' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≃ B)
                → ((x : A) → P x ≃ Q (equivFun p x))
                → Σ A P ≃ Σ B Q
glueing-equiv' {A = A} {B = B} {P = P} {Q = Q} p f = isoToEquiv (Σ-ap-iso (equivToIso p) (equivToIso ∘ f))

-- set truncation commutes with multiplication by a set
∥∥₀×set : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → isSet B → ∥ A × B ∥₀ ≃ ∥ A ∥₀ × B
∥∥₀×set {A = A} {B = B} SB = isoToEquiv i
  where
  f : ∥ A × B ∥₀ → ∥ A ∥₀ × B
  f = ∥∥₀.rec (isSet× setTruncIsSet SB) λ { (a , t) → ∣ a ∣₀ , t }
  g : ∥ A ∥₀ × B → ∥ A × B ∥₀
  g (a , t) = ∥∥₀.rec setTruncIsSet (λ a → ∣ a , t ∣₀) a
  i : Iso ∥ A × B ∥₀ (∥ A ∥₀ × B)
  Iso.fun i = f
  Iso.inv i = g
  Iso.rightInv i (a , t) = ∥∥₀.elim {B = λ a → f (g (a , t)) ≡ (a , t)} (λ _ → isProp→isSet (isSet× setTruncIsSet SB _ _)) (λ a → refl) a
  Iso.leftInv i a = ∥∥₀.elim {B = λ a → g (f a) ≡ a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ { (a , t) → refl }) a

-- set trucation  commutes with disjoint union
∥∥₀⊎ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → ∥ A ⊎ B ∥₀ ≃ ∥ A ∥₀ ⊎ ∥ B ∥₀
∥∥₀⊎ {_} {_} {A} {B} = isoToEquiv i
  where
  F : ∥ A ⊎ B ∥₀ → ∥ A ∥₀ ⊎ ∥ B ∥₀
  F = ∥∥₀.rec (isSet⊎ setTruncIsSet setTruncIsSet) λ { (inl a) → inl ∣ a ∣₀ ; (inr b) → inr ∣ b ∣₀ }
  G : ∥ A ∥₀ ⊎ ∥ B ∥₀ → ∥ A ⊎ B ∥₀
  G (inl a) = ∥∥₀.rec setTruncIsSet (λ a → ∣ inl a ∣₀) a
  G (inr b) = ∥∥₀.rec setTruncIsSet (λ b → ∣ inr b ∣₀) b
  i : Iso ∥ A ⊎ B ∥₀ (∥ A ∥₀ ⊎ ∥ B ∥₀)
  Iso.fun i = F
  Iso.inv i = G
  Iso.rightInv i (inl a) = ∥∥₀.elim {B = λ a → F (G (inl a)) ≡ inl a} (λ _ → isProp→isSet (isSet⊎ setTruncIsSet setTruncIsSet _ _)) (λ _ → refl) a
  Iso.rightInv i (inr b) = ∥∥₀.elim {B = λ b → F (G (inr b)) ≡ inr b} (λ _ → isProp→isSet (isSet⊎ setTruncIsSet setTruncIsSet _ _)) (λ _ → refl) b
  Iso.leftInv i x = ∥∥₀.elim {B = λ x → G (F x) ≡ x} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ { (inl a) → refl ; (inr b) → refl }) x

-- set truncation commutes with taking subtypes
∥∥₀ΣP : {ℓ ℓ' : Level} {A : Type ℓ} (P : A → Type ℓ') (prop : (a : A) → isProp (P a)) → ∥ Σ A P ∥₀ ≃ Σ ∥ A ∥₀ (fst ∘ (∥∥₀.rec isSetHProp λ a → P a , prop a))
∥∥₀ΣP {A = A} P prop = isoToEquiv i
  where
  P' : ∥ A ∥₀ → Type _
  P' = fst ∘ (∥∥₀.rec isSetHProp λ a → P a , prop a)
  F : ∥ Σ A P ∥₀ → Σ ∥ A ∥₀ P'
  F = ∥∥₀.rec (isSetΣ setTruncIsSet (λ a → ∥∥₀.elim {B = λ a → isSet (P' a)} (λ _ → isProp→isSet isPropIsSet) (λ a → isProp→isSet (prop a)) a)) λ { (a , p) → ∣ a ∣₀ , p }
  G : Σ ∥ A ∥₀ P' → ∥ Σ A P ∥₀
  G (a , p) = ∥∥₀.elim {B = λ a → P' a → ∥ Σ A P ∥₀} (λ _ → isSetΠ λ _ → setTruncIsSet) (λ a Pa → ∣ a , Pa ∣₀) a p
  i : Iso ∥ Σ A P ∥₀ (Σ ∥ A ∥₀ P')
  Iso.fun i = F
  Iso.inv i = G
  Iso.rightInv i (a , p) = ΣProp≡ (λ a → ∥∥₀.elim {B = λ a → isProp (P' a)} (λ _ → isProp→isSet isPropIsProp) prop a) (∥∥₀.elim {B = λ a → (p : P' a) → F (G (a , p)) .fst ≡ a} (λ _ → isProp→isSet (isPropΠ λ _ → setTruncIsSet _ _)) (λ a p → refl) a p)
  Iso.leftInv i = ∥∥₀.elim (λ _ → isProp→isSet (setTruncIsSet _ _)) λ { (a , p) → refl}

--
-- import previous work on division by 2 on sets obtained by set truncation

A₀isSet : isSet ∥ A ∥₀
A₀isSet = setTruncIsSet

B₀isSet : isSet ∥ B ∥₀
B₀isSet = setTruncIsSet

A₀E≃B₀E : ∥ A ∥₀ × End ≃ ∥ B ∥₀ × End
A₀E≃B₀E = compEquiv (invEquiv (∥∥₀×set End-isSet)) (compEquiv (∥∥₀-equiv equiv) (∥∥₀×set End-isSet))

open import Ends
import Arrows A₀isSet B₀isSet A₀E≃B₀E as AS
import Div2 A₀isSet B₀isSet A₀E≃B₀E as DS
import Div2Reach A₀isSet B₀isSet A₀E≃B₀E as DRS
open import ArrowsBase equiv

open import Partition
open import Sigma

f' : ∥ A ∥₀ → ∥ B ∥₀
f' = equivFun DS.Conway

g' : ∥ B ∥₀ → ∥ A ∥₀
g' = invEq DS.Conway

-- connected component
cc : dArrows → ∥ dArrows ∥₀
cc = ∣_∣₀

-- elements of the connected component
el-cc : ∥ dArrows ∥₀ → Type _
el-cc = fiber cc

-- alternative characterization
el-cc' : {ℓ : Level} {A : Type ℓ} (a : A) → (fiber ∣_∣₀ ∣ a ∣₀) ≃ (Σ[ a' ∈ A ] ∥ a ≡ a' ∥)
el-cc' {ℓ} {A = A} a = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ ∣ a ∣₀) (Σ[ a' ∈ A ] ∥ a ≡ a' ∥)
  Iso.fun i (a' , p) = a' , lem (sym p)
    where
    F : A → hProp _
    F a' = ∥ a ≡ a' ∥ , propTruncIsProp
    lem : {a' : A} → ∣ a ∣₀ ≡ ∣ a' ∣₀ → ∥ a ≡ a' ∥
    lem {a'} p = subst (fst ∘ (∥∥₀.rec isSetHProp F)) p ∣ refl ∣
  Iso.inv i (a' , p) = a' , ∥∥.rec (setTruncIsSet _ _) (λ p → cong ∣_∣₀ (sym p)) p
  Iso.rightInv i (a' , p) = ΣProp≡ (λ _ → propTruncIsProp) refl
  Iso.leftInv i (a' , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) refl

-- next is a fiberwise equivalence
next≃f : {o : dArrows} → el-cc (cc o) ≃ el-cc (cc (next o))
-- next≃f {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc (cc o)) (el-cc (cc (next o)))
  -- Iso.fun i (a , p) = next a , map₀ next p
  -- Iso.inv i (a , p) = prev a , map₀ prev p ∙ cong ∣_∣₀ (prev-next o)
  -- Iso.rightInv i (a , p) = ΣPathP (next-prev a , toPathP (setTruncIsSet _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (prev-next a , toPathP (setTruncIsSet _ _ _ _))
next≃f {o} = ∥∥₀-equiv-fib next≃ (cc o)

prev≃f : {o : dArrows} → el-cc (cc o) ≃ el-cc (cc (prev o))
-- prev≃f {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc (cc o)) (el-cc (cc (prev o)))
  -- Iso.fun i (a , p) = prev a , map₀ prev p
  -- Iso.inv i (a , p) = next a , map₀ next p ∙ cong ∣_∣₀ (next-prev o)
  -- Iso.rightInv i (a , p) = ΣPathP (prev-next a , toPathP (setTruncIsSet _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (next-prev a , toPathP (setTruncIsSet _ _ _ _))
prev≃f {o} = ∥∥₀-equiv-fib (invEquiv next≃) (cc o)

-- reachable≃f' : {a b : Arrows} → reachable-arr a b → el-cc (cc a) ≃ el-cc (cc b)
-- reachable≃f' r = ?

-- reachable≃f : {a b : dArrows} → reachable a b → el-cc (cc a) ≃ el-cc (cc b)
-- reachable≃f {a} {b} (n , p) = ℤ.elim E Z N P P
  -- (λ n F → toPathP (funExt₃ (PN n F))) -- (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt (λ c → ΣProp≡ (λ _ → setTruncIsSet _ _) {!!}))))) -- essentially prev-next
  -- (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt λ c → ΣProp≡ (λ _ → setTruncIsSet _ _) {!!})))) -- essentially next-prev
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



  -- PN' : (n : ℤ) (F : E n) (a b : dArrows) (p : iterate (predl-suc n i1) a ≡ b) (c : el-cc ∣ a ∣₀) →
       -- transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c))) ≡ F a b p .fst c .fst
  -- PN' n F a b p c =
    -- transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c))) ≡⟨ transportRefl _ ⟩
    -- fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c)) ≡⟨ {!!} ⟩
    -- fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c)) ≡⟨ {!!} ⟩
    -- F a b p .fst c .fst ∎

dArrows₀ : Type _
dArrows₀ = ∥ dArrows ∥₀

iterate₀ : ℤ → dArrows₀ → dArrows₀
iterate₀ n = ∥∥₀-map (iterate n)

reachable₀ : dArrows₀ → dArrows₀ → Type _
reachable₀ a b = Σ[ n ∈ ℤ ] iterate₀ n a ≡ b

dArrowsS₀ : AS.dArrows ≃ dArrows₀
dArrowsS₀ =
  AS.dArrows            ≃⟨ idEquiv _ ⟩
  (∥ A ∥₀ ⊎ ∥ B ∥₀) × End ≃⟨ cong≃ (λ X → X × End) (invEquiv ∥∥₀⊎) ⟩
  ∥ A ⊎ B ∥₀ × End       ≃⟨ invEquiv (∥∥₀×set End-isSet) ⟩
  ∥ dArrows ∥₀           ■

dArrowsS→0 : AS.dArrows → dArrows₀
dArrowsS→0 = equivFun dArrowsS₀

reachableS→0 : {a b : AS.dArrows} → AS.reachable a b → reachable₀ (dArrowsS→0 a) (dArrowsS→0 b)
reachableS→0 {a = a} (n , r) = n , {!!} ∙ cong dArrowsS→0 r

prev₀ : dArrows₀ → dArrows₀
prev₀ = ∥∥₀-map prev

next₀ : dArrows₀ → dArrows₀
next₀ = ∥∥₀-map next

next-prev₀ : (a : dArrows₀) → next₀ (prev₀ a) ≡ a
next-prev₀ a = ∥∥₀-map-comp next prev a ∙ ∥∥₀-map-id-ext _ next-prev a

prev-next₀ : (a : dArrows₀) → prev₀ (next₀ a) ≡ a
prev-next₀ a = ∥∥₀-map-comp prev next a ∙ ∥∥₀-map-id-ext _ prev-next a

iterate-suc₀ : (n : ℤ) (a : dArrows₀) → iterate₀ (suc n) a ≡ next₀ (iterate₀ n a)
iterate-suc₀ n a = sym (∥∥₀-map-comp next (iterate n) a)

iterate-pred₀ : (n : ℤ) (a : dArrows₀) → iterate₀ (pred n) a ≡ prev₀ (iterate₀ n a)
iterate-pred₀ n a = sym (∥∥₀-map-comp prev (iterate n) a)

Arrows₀ = ∥ Arrows ∥₀

ArrowsS₀ : AS.Arrows ≃ Arrows₀
ArrowsS₀ = invEquiv ∥∥₀⊎

ArrowsS→0 : AS.Arrows → Arrows₀
ArrowsS→0 = equivFun ArrowsS₀

Arrows0→S : Arrows₀ → AS.Arrows
Arrows0→S = invEq ArrowsS₀

fw₀ : Arrows₀ → dArrows₀
fw₀ a = dArrowsS→0 (AS.fw (invEq ArrowsS₀ a))

bw₀ : Arrows₀ → dArrows₀
bw₀ a = dArrowsS→0 (AS.bw (invEq ArrowsS₀ a))

orient₀ : Arrows₀ → End → dArrows₀
orient₀ a e = dArrowsS→0 (Arrows0→S a , e)

-- next is a fiberwise equivalence
next≃f' : {o : ∥ dArrows ∥₀} → el-cc o ≃ el-cc (next₀ o)
-- next≃f' {o} = isoToEquiv i
  -- where
  -- i : Iso (el-cc o) (el-cc (∥∥₀-map next o))
  -- Iso.fun i (a , p) = next a , cong next₀ p
  -- Iso.inv i (a , p) = prev a , cong prev₀ p ∙ ∥∥₀-map-comp next prev o ∙ cong (λ f → ∥∥₀-map f o) (funExt prev-next) ∙ ∥∥₀-map-id o
  -- Iso.rightInv i (a , p) = ΣPathP (next-prev a , toPathP (setTruncIsSet _ _ _ _))
  -- Iso.leftInv i (a , p) = ΣPathP (prev-next a , (toPathP (setTruncIsSet _ _ _ _)))
next≃f' {o} = ∥∥₀-equiv-fib next≃ o

prev≃f' : {o : ∥ dArrows ∥₀} → el-cc o ≃ el-cc (prev₀ o)
prev≃f' {o} = ∥∥₀-equiv-fib (invEquiv next≃) o

reachable≃f' : {a b : ∥ dArrows ∥₀} → reachable₀ a b → el-cc a ≃ el-cc b
reachable≃f' {a} {b} (n , p) = ℤ.elim E Z N P P PN {!!} n a b p
  where
  E : (n : ℤ) → Type ℓ
  E n = (a b : dArrows₀) → iterate₀ n a ≡ b → el-cc a ≃ el-cc b
  Z : E zero
  Z a b p = pathToEquiv (cong el-cc (sym (∥∥₀-map-id a) ∙ p))
  N : (n : ℤ) → E n → E (suc n)
  N n H a b p = compEquiv (H a (prev₀ b) (lem ∙ cong prev₀ p)) (compEquiv next≃f' (pathToEquiv (cong el-cc (next-prev₀ b))))
    where
    lem =
      iterate₀ n a                 ≡⟨ sym (prev-next₀ _) ⟩
      prev₀ (next₀ (iterate₀ n a)) ≡⟨ sym (cong prev₀ (iterate-suc₀ n a)) ⟩
      prev₀ (iterate₀ (suc n) a)   ∎
  P : (n : ℤ) → E n → E (pred n)
  P n H a b p = compEquiv (H a (next₀ b) (sym (next-prev₀ _) ∙ sym (cong next₀ (iterate-pred₀ n a)) ∙ cong next₀ p)) (compEquiv prev≃f' (pathToEquiv (cong el-cc (prev-next₀ b))))
  PN : (n : ℤ) (H : E n) → PathP (λ i → E (predl-suc n i)) (P (suc n) (N n H)) H
  PN n H = toPathP (funExt₃ {!!})

-- NB: the lemmas below do not seem to be specific to ∣_∣₀

-- the fiber of a subtype is the same as the original fiber
-- Note: probably not the most elegant proof...
fiber-sub : {ℓ : Level} {A : Type ℓ} (P : A → Type ℓ) → ((x : A) → isProp (P x)) →
            (x : ∥ Σ A P ∥₀) → fiber ∣_∣₀ x ≃ fiber ∣_∣₀ (∥∥₀-map fst x)
fiber-sub {A = A} P prop x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ x) (fiber ∣_∣₀ (∥∥₀-map fst x))
  Iso.fun i ((a , p) , q) = a , cong (∥∥₀-map fst) q
  Iso.inv i (a , q) = (a , subst P' a'≡a₀ P'a') , lem'
    where
    P' : ∥ A ∥₀ → Type _
    P' = fst ∘ ∥∥₀.rec isSetHProp (λ a → P a , prop a)
    aPa : Σ ∥ A ∥₀ P'
    aPa = equivFun (∥∥₀ΣP P prop) x
    a' : ∥ A ∥₀
    a' = fst aPa
    P'a' : P' a'
    P'a' = snd aPa
    lem1 : (x : ∥ Σ A P ∥₀) → fst (equivFun (∥∥₀ΣP P prop) x) ≡ ∥∥₀-map fst x
    lem1 x = ∥∥₀.elim {B = λ x → fst (equivFun (∥∥₀ΣP P prop) x) ≡ ∥∥₀-map fst x} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ { (a , p) → refl}) x
    a'≡a₀ : a' ≡ ∣ a ∣₀
    a'≡a₀ = lem1 x ∙ sym q
    lem' =
      ∣ a , subst P' a'≡a₀ P'a' ∣₀ ≡⟨ sym (secEq (∥∥₀ΣP P prop) ∣ a , subst P' a'≡a₀ P'a' ∣₀) ⟩
      invEq (∥∥₀ΣP P prop) (equivFun (∥∥₀ΣP P prop) ∣ a , subst P' a'≡a₀ P'a' ∣₀) ≡⟨ cong (invEq (∥∥₀ΣP P prop)) (ΣPathP (sym a'≡a₀ , toPathP _)) ⟩
      invEq (∥∥₀ΣP P prop) (equivFun (∥∥₀ΣP P prop) x) ≡⟨ secEq (∥∥₀ΣP P prop) x ⟩
      x ∎
  Iso.rightInv i (a , q) = ΣProp≡ (λ _ → setTruncIsSet _ _) refl
  Iso.leftInv i ((a , p) , q) = ΣProp≡ (λ _ → setTruncIsSet _ _) (ΣProp≡ prop refl)

fiber-inl : {ℓ : Level} {A B : Type ℓ} (a : ∥ A ∥₀) → fiber ∣_∣₀ a ≃ fiber ∣_∣₀ (∥∥₀-map (inl {B = B}) a)
fiber-inl {B = B} a =
  fiber ∣_∣₀ a                                  ≃⟨ ∥∥₀-equiv-fib (inl≃ {B = B}) a ⟩
  fiber ∣_∣₀ (∥∥₀-map (equivFun inl≃) a)         ≃⟨ fiber-sub in-left in-left-isProp (∥∥₀-map (equivFun inl≃) a) ⟩
  fiber ∣_∣₀ (∥∥₀-map fst (∥∥₀-map (fst inl≃) a)) ≃⟨ pathToEquiv (cong (fiber ∣_∣₀) (∥∥₀-map-comp fst (fst inl≃) a)) ⟩
  fiber ∣_∣₀ (∥∥₀-map (inl {B = B}) a)           ■

fiber-inr : {ℓ : Level} {A B : Type ℓ} (a : ∥ B ∥₀) → fiber ∣_∣₀ a ≃ fiber ∣_∣₀ (∥∥₀-map (inr {A = A}) a)
fiber-inr {A = A} a =
  fiber ∣_∣₀ a                                  ≃⟨ ∥∥₀-equiv-fib (inr≃ {A = A}) a ⟩
  fiber ∣_∣₀ (∥∥₀-map (equivFun inr≃) a)         ≃⟨ fiber-sub in-right in-right-isProp (∥∥₀-map (equivFun inr≃) a) ⟩
  fiber ∣_∣₀ (∥∥₀-map fst (∥∥₀-map (fst inr≃) a)) ≃⟨ pathToEquiv (cong (fiber ∣_∣₀) (∥∥₀-map-comp fst (fst inr≃) a)) ⟩
  fiber ∣_∣₀ (∥∥₀-map (inr {A = A}) a)           ■

Div2 : A ≃ B
Div2 = compEquiv (Σ-components A) (compEquiv (glueing-equiv' DS.Conway fiber-equiv) (invEquiv (Σ-components B)))
  where
  fiber-equiv : (a : ∥ A ∥₀) → fiber ∣_∣₀ a ≃ fiber ∣_∣₀ (equivFun DS.Conway a)
  fiber-equiv a =
    fiber ∣_∣₀ a                                                                                    ≃⟨ fiber-inl a ⟩
    fiber ∣_∣₀ (ArrowsS→0 (inl a))                                                                  ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (fw₀ (ArrowsS→0 (inl a)))                                                                 ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (dArrowsS→0 (AS.fw (inl a)))                                                              ≃⟨ reachable≃f' (reachableS→0 (AS.reachable-arr→reachable' (DRS.Conway-reachable a))) ⟩
    el-cc (dArrowsS→0 (inr (DRS.ConwayFun a) , AS.reachable-end (DRS.Conway-reachable a)))          ≃⟨ {!!} ⟩ -- similar administrative step
    el-cc (orient₀ (ArrowsS→0 (inr (DRS.ConwayFun a))) (AS.reachable-end (DRS.Conway-reachable a))) ≃⟨ {!!} ⟩ -- similar administrative step
    fiber ∣_∣₀ (ArrowsS→0 (inr (DRS.ConwayFun a)))                                                  ≃⟨ invEquiv (fiber-inr _) ⟩
    fiber ∣_∣₀ (equivFun DS.Conway a)                                                               ■
