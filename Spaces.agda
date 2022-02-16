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

∥∥₀-fun : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
         (A → B) → (∥ A ∥₀ → ∥ B ∥₀)
∥∥₀-fun f = ∥∥₀.rec setTruncIsSet (λ a → ∣ f a ∣₀)

∥∥₀-fun-∘ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
           (f : A → B) (g : B → C) → ∥∥₀-fun (g ∘ f) ≡ ∥∥₀-fun g ∘ ∥∥₀-fun f
∥∥₀-fun-∘ f g = funExt (∥∥₀.elim (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ a → refl))

∥∥₀-fun-id : {ℓ : Level} {A : Type ℓ} → ∥∥₀-fun (idfun A) ≡ idfun ∥ A ∥₀
∥∥₀-fun-id = funExt (∥∥₀.elim (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ a → refl))

-- equivalences are compatible with 0-truncation

∥∥₀-equiv : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} →
           A ≃ B → ∥ A ∥₀ ≃ ∥ B ∥₀
∥∥₀-equiv {_} {_} {A} {B} e = isoToEquiv i
  where
  i : Iso ∥ A ∥₀ ∥ B ∥₀
  Iso.fun i = ∥∥₀-fun (equivFun e)
  Iso.inv i = ∥∥₀-fun (invEq e)
  Iso.rightInv i = funExt⁻ (sym (∥∥₀-fun-∘ _  _) ∙ cong ∥∥₀-fun (funExt (retEq e)) ∙ ∥∥₀-fun-id)
  Iso.leftInv i = funExt⁻ (sym (∥∥₀-fun-∘ _  _) ∙ cong ∥∥₀-fun (funExt (secEq e)) ∙ ∥∥₀-fun-id)

-- fiberwise equivalence

∥∥₀-equiv-fib : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} →
               (e : A ≃ B) (x : ∥ A ∥₀) → fiber ∣_∣₀ x ≃ fiber ∣_∣₀ (∥∥₀-fun (equivFun e) x)
∥∥₀-equiv-fib e x = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ x) (fiber ∣_∣₀ (∥∥₀-fun (equivFun e) x))
  Iso.fun i (a , p) = equivFun e a , cong (∥∥₀-fun (equivFun e)) p
  Iso.inv i (b , p) = invEq e b , cong (∥∥₀-fun (invEq e)) p ∙ secEq (∥∥₀-equiv e) x
  Iso.rightInv i (b , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (retEq e b)
  Iso.leftInv i (a , p) = ΣProp≡ (λ _ → setTruncIsSet _ _) (secEq e a)

Σ-components : {ℓ : Level} (A : Type ℓ) → A ≃ Σ ∥ A ∥₀ (fiber ∣_∣₀)
Σ-components A = totalEquiv ∣_∣₀

-- -- two
-- ⊤⊤ : Type₀
-- ⊤⊤ = ⊤ ⊎ ⊤

-- -- two is a set
-- ⊤⊤-isSet : isSet ⊤⊤
-- ⊤⊤-isSet (inl tt) (inl tt) = isContr→isProp (refl , lem)
  -- where
  -- e : (tt ≡ tt) ≃ (inl tt ≡ inl tt)
  -- e = _ , isEmbedding-inl tt tt
  -- lem = λ p →
    -- refl                   ≡⟨ refl ⟩
    -- equivFun e refl        ≡⟨ cong (equivFun e) (isProp→isSet isPropUnit _ _ _ _) ⟩
    -- equivFun e (invEq e p) ≡⟨ retEq e p ⟩
    -- p                      ∎
-- ⊤⊤-isSet (inl tt) (inr tt) p q = ⊥.rec (inl≢inr p)
-- ⊤⊤-isSet (inr tt) (inl tt) p q = ⊥.rec (inl≢inr (sym p))
-- ⊤⊤-isSet (inr tt) (inr x) = isContr→isProp (refl , λ p → cong (equivFun e) (isProp→isSet isPropUnit _ _ _ _) ∙ retEq e p)
  -- where
  -- e : (tt ≡ tt) ≃ (inr tt ≡ inr tt)
  -- e = _ , isEmbedding-inr tt tt

-- truncation and doubling
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

-- ∥∥₀×⊤⊤ : {ℓ : Level} {A : Type ℓ} → ∥ A × ⊤⊤ ∥₀ ≃ ∥ A ∥₀ × ⊤⊤
-- ∥∥₀×⊤⊤ {_} {A} = ∥∥₀×set ⊤⊤-isSet

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

A₀isSet : isSet ∥ A ∥₀
A₀isSet = setTruncIsSet

B₀isSet : isSet ∥ B ∥₀
B₀isSet = setTruncIsSet

A₀E≃B₀E : ∥ A ∥₀ × End ≃ ∥ B ∥₀ × End
A₀E≃B₀E = compEquiv (invEquiv (∥∥₀×set End-isSet)) (compEquiv (∥∥₀-equiv equiv) (∥∥₀×set End-isSet))

-- ⊤⊤≡Ends : ⊤⊤ ≡ End
-- ⊤⊤≡Ends = ua (isoToEquiv i)
  -- where
  -- i : Iso ⊤⊤ End
  -- Iso.fun i (inl tt) = src
  -- Iso.fun i (inr tt) = tgt
  -- Iso.inv i src = inl tt
  -- Iso.inv i tgt = inr tt
  -- Iso.rightInv i src = refl
  -- Iso.rightInv i tgt = refl
  -- Iso.leftInv i (inl tt) = refl
  -- Iso.leftInv i (inr tt) = refl

open import Ends
import Arrows A₀isSet B₀isSet A₀E≃B₀E as AS
import Div2 A₀isSet B₀isSet A₀E≃B₀E as DS
import Div2Reach A₀isSet B₀isSet A₀E≃B₀E as DRS
open import ArrowsBase equiv

--we can "glue" multiple equivalences together
glueing-equiv : {ℓ ℓ' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≡ B)
                → ((x : A) → P x ≡ Q (transport p x))
                → Σ A P ≡ Σ B Q
glueing-equiv {A = A} {Q = Q} p f = cong (Σ A) (funExt f) ∙ Σ-ap₁ p

glueing-equiv' : {ℓ ℓ' ℓ'' : Level} {A B : Type ℓ} {P : A → Type ℓ'} {Q : B → Type ℓ'} → (p : A ≃ B)
                → ((x : A) → P x ≃ Q (equivFun p x))
                → Σ A P ≃ Σ B Q
glueing-equiv' {A = A} {B = B} {P = P} {Q = Q} p f = isoToEquiv (Σ-ap-iso (equivToIso p) (λ x → equivToIso (f x)))

-- compEquivFun : {ℓ : Level} {A B C : Type ℓ} (F : A ≃ B) (G : B ≃ C) (a : A) → equivFun (compEquiv F G) a ≡ (equivFun G) (equivFun F a)
-- compEquivFun F G a = refl

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

-- alternative characterization (??)
el-cc' : {ℓ : Level} {A : Type ℓ} (a : A) → (fiber ∣_∣₀ ∣ a ∣₀) ≃ (Σ[ a' ∈ A ] ∥ a ≡ a' ∥)
el-cc' {A = A} a = isoToEquiv i
  where
  i : Iso (fiber ∣_∣₀ ∣ a ∣₀) (Σ[ a' ∈ A ] ∥ a ≡ a' ∥)
  Iso.fun i (a' , p) = a' , {!!}
  Iso.inv i (a' , p) = a' , ∥∥.rec (setTruncIsSet _ _) (λ p → cong ∣_∣₀ (sym p)) p
  Iso.rightInv i = {!!}
  Iso.leftInv i = {!!}

∥∥₀-map : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → ∥ A ∥₀ → ∥ B ∥₀
∥∥₀-map f = ∥∥₀.rec setTruncIsSet (λ a → ∣ f a ∣₀)

∥∥₀-map-id : {ℓ : Level} {A : Type ℓ} (a : ∥ A ∥₀) → ∥∥₀-map (λ a → a) a ≡ a
∥∥₀-map-id = ∥∥₀.elim {B = λ a → ∥∥₀-map (λ a → a) a ≡ a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ _ → refl)

∥∥₀-map-comp : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} (f : A → B) (g : B → C) (a : ∥ A ∥₀) → ∥∥₀-map g (∥∥₀-map f a) ≡ ∥∥₀-map (g ∘ f) a
∥∥₀-map-comp f g a = ∥∥₀.elim {B = λ a → ∥∥₀-map g (∥∥₀-map f a) ≡ ∥∥₀-map (g ∘ f) a} (λ _ → isProp→isSet (setTruncIsSet _ _)) (λ a → refl) a

∥∥₀-rec₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          isSet C → (A → B → C) → (∥ A ∥₀ → ∥ B ∥₀ → C)
∥∥₀-rec₂ {B = B} {C = C} S f a b = ∥∥₀.rec (isSetΠ (λ _ → S)) (λ a b → ∥∥₀.rec S (λ b → f a b) b) a b

∥∥₀-map₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} →
          (A → B → C) → (∥ A ∥₀ → ∥ B ∥₀ → ∥ C ∥₀)
∥∥₀-map₂ f = ∥∥₀-rec₂ setTruncIsSet λ a b → ∣ f a b ∣₀

map₀ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {a a' : A} (f : A → B) → ∣ a ∣₀ ≡ ∣ a' ∣₀ → ∣ f a ∣₀ ≡ ∣ f a' ∣₀
map₀ f p = cong (∥∥₀-map f) p

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

reachable≃f : {a b : dArrows} → reachable a b → el-cc (cc a) ≃ el-cc (cc b)
reachable≃f {a} {b} (n , p) = ℤ.elim E Z N P P
  (λ n F → toPathP (funExt₃ (PN n F))) -- (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt (λ c → ΣProp≡ (λ _ → setTruncIsSet _ _) {!!}))))) -- essentially prev-next
  (λ n F → toPathP (funExt₃ (λ a b p → equivEq _ _ (funExt λ c → ΣProp≡ (λ _ → setTruncIsSet _ _) {!!})))) -- essentially next-prev
  n a b p
  where
  E : (n : ℤ) → Type ℓ
  E n = (a b : dArrows) → iterate n a ≡ b → el-cc (cc a) ≃ el-cc (cc b)
  Z : E zero
  Z a b p = pathToEquiv (cong (el-cc ∘ cc) p)
  N : (n : ℤ) → E n → E (suc n)
  N n H a b p = compEquiv (H a (prev b) (sym (prev-next _) ∙ cong prev p)) (compEquiv next≃f (pathToEquiv (cong (el-cc ∘ cc) (next-prev b))))
  P : (n : ℤ) → E n → E (pred n)
  P n H a b p = compEquiv (H a (next b) (sym (next-prev _) ∙ cong next p)) (compEquiv prev≃f (pathToEquiv (cong (el-cc ∘ cc) (prev-next b))))
  PN : (n : ℤ) (F : E n) (a b : dArrows) (p : iterate (predl-suc n i1) a ≡ b) → transport (cong E (predl-suc n)) (P (suc n) (N n F)) a b p ≡ F a b p
  PN n F a b p = {!!}
    where
    Nfst : (n : ℤ) (F : E n) (a b : dArrows) (p : next (iterate n a) ≡ b) → N n F a b p .fst ≡ subst (el-cc ∘ cc) (next-prev b) ∘ equivFun next≃f ∘ F a (prev b) (sym (prev-next (iterate n a)) ∙ cong prev p) .fst
    Nfst n F a b p = refl
    Pfst : (n : ℤ) (F : E n) (a b : dArrows) (p : prev (iterate n a) ≡ b) → P n F a b p .fst ≡ subst (el-cc ∘ cc) (prev-next b) ∘ equivFun prev≃f ∘ F a (next b) (sym (next-prev (iterate n a)) ∙ cong next p) .fst
    Pfst n F a b p = refl
    lem : transport (cong E (predl-suc n)) (P (suc n) (N n F)) a b p .fst ≡ F a b p .fst
    lem =
      subst E (predl-suc n) (P (suc n) (N n F)) a b p .fst ≡⟨ refl ⟩
      -- subst (el-cc ∘ cc) (prev-next b) ∘ equivFun prev≃f ∘ subst (el-cc ∘ cc) (next-prev (next b)) ∘ equivFun next≃f ∘ F a (prev (next b)) {!!} .fst ≡⟨ {!!} ⟩
      subst (el-cc ∘ cc) {!prev-next b!} ∘ {!!} ≡⟨ {!!} ⟩
      F a b p .fst ∎



  PN' : (n : ℤ) (F : E n) (a b : dArrows) (p : iterate (predl-suc n i1) a ≡ b) (c : el-cc ∣ a ∣₀) →
       transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c))) ≡ F a b p .fst c .fst
  PN' n F a b p c =
    transport (λ _ → dArrows) (fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c))) ≡⟨ transportRefl _ ⟩
    fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c)) ≡⟨ {!!} ⟩
    fst (fst (P (suc n) (N n F) (transport (λ _ → dArrows) a) (transport (λ _ → dArrows) b) (transport (λ j → prev-next (iterate n (transp (λ _ → dArrows) (~ j) a)) (~ j) ≡ transp (λ _ → dArrows) (~ j) b) p)) (transport (λ j → el-cc ∣ transp (λ _ → dArrows) (~ j) a ∣₀) c)) ≡⟨ {!!} ⟩
    F a b p .fst c .fst ∎

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
reachableS→0 (n , r) = n , {!!}

prev₀ : dArrows₀ → dArrows₀
prev₀ = ∥∥₀-map prev

next₀ : dArrows₀ → dArrows₀
next₀ = ∥∥₀-map next

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
reachable≃f' {a} {b} (n , p) = ℤ.elim E Z {!!} {!!} {!!} {!!} {!!} n a b p
  where
  E : (n : ℤ) → Type ℓ
  E n = (a b : dArrows₀) → iterate₀ n a ≡ b → el-cc a ≃ el-cc b
  Z : E zero
  Z a b p = pathToEquiv (cong el-cc (sym (∥∥₀-map-id a) ∙ p))
  N : (n : ℤ) → E n → E (suc n)
  N n H a b p = compEquiv (H a (prev₀ b) {!!}) (compEquiv next≃f' {!!})

-- TODO: from reachable≃f' by transport
-- reachable≃f'' : {a b : AS.dArrows} → AS.reachable a b → el-cc (dArrowsS→0 a) ≃ el-cc (dArrowsS→0 b)
-- reachable≃f'' r = {!!}

-- reachable≃f''' : {a b : AS.Arrows} → AS.reachable-arr a b → fiber ∣_∣₀ {!!} ≃ fiber ∣_∣₀ {!!}
-- reachable≃f'''  r = {!case AS.reachable-arr→reachable r of ?!}
-- with AS.reachable-arr→reachable r
-- ... | k = {!!}

-- -- predicate indicating when a reachability path is the "smallest one"
-- canonical : {a b : dArrows} (r : reachable a b) → Type ℓ
-- canonical = {!!}

-- -- the proof of canonicity is essentially the length of the smallest path, which is unique
-- canonical-isProp : {a b : dArrows} (r : reachable a b) → isProp (canonical r)
-- canonical-isProp = {!!}

-- -- there exists a unique canonical path between any two arrows
-- canonical-unique : {a b : dArrows} → isProp (Σ (reachable a b) canonical)
-- canonical-unique = {!!}

-- -- we can construct a canonical path from knowing its existence
-- reveal-canonical : {a b : dArrows} → is-reachable a b → reachable a b
-- reveal-canonical {a} {b} r = fst (aux r)
  -- where
  -- aux : is-reachable a b → Σ (reachable a b) canonical
  -- aux = ∥∥.rec canonical-unique {!!} -- we have to show that we can construct the canonical path when there exists one

-- -- two reachable arrows have the same connected components
-- is-reachable≃f : {a b : dArrows} → is-reachable a b → el-cc (cc a) ≃ el-cc (cc b)
-- is-reachable≃f r = reachable≃f (reveal-canonical r)

-- -- an element of a pointed chain has the same connected component as the origin
-- Chain≃f : (o : dArrows) (a : delements [ o ]) → el-cc (cc o) ≃ el-cc (cc (fst a))
-- Chain≃f o (a , p) = is-reachable≃f r
  -- where
  -- -- TODO: check that the fact that is-reachable is an equivalence relation can
  -- -- be performed without the set hypothesis
  -- r : is-reachable o a
  -- r = effective (λ _ _ → propTruncIsProp) {!!} _ _ (sym p)

--- NB: this does not seem to hold
-- Chain≃f : (c : dChains) (a b : delements c) → el-cc (cc (fst a)) ≃ el-cc (cc (fst b))
-- Chain≃f c a b = is-reachable≃f {!!}

-- Conway-fun : (a : ∥ A ∥₀) → equivFun DS.Conway a ≡ AS.chainB→B (equivFun (DS.Conway-chain [ inl a ]) ((inl a , refl) , subst in-left (sym (retEq (invEquiv (partition AS.is-reachable-arr)) (inl a))) (is-inl a)))
-- Conway-fun a = refl
  -- where
  -- is-inl-a' : in-left (inl a)
  -- is-inl-a' = subst in-left (sym (retEq (invEquiv (partition is-reachable-arr)) (inl a))) (is-inl a)
  -- x : chainA [ inl a ]
  -- x = ((inl a , refl) , is-inl-a')
  -- y : chainB [ inl a ]
  -- y = equivFun (Conway-chain [ inl a ]) x
  -- test : equivFun Conway a ≡ chainB→B y
  -- test = refl
  -- test2 : equivFun Conway a ≡ chainB→B y
  -- test2 = {!refl!}
  -- lem =
    -- equivFun Conway a ≡⟨ refl ⟩
    -- equivFun (bij-by-chain is-reachable-arr Conway-chain) a ≡⟨ refl ⟩
    -- -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr)))) ∘ (equivFun (invEquiv assocΣ)) ∘ (equivFun (congΣEquiv Conway-chain)) ∘ (equivFun assocΣ) ∘ (equivFun (invEquiv (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr))))) ∘ (equivFun inl≃)) a ≡⟨ refl ⟩
    -- -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr)))) ∘ (equivFun (invEquiv assocΣ)) ∘ (equivFun (congΣEquiv Conway-chain)) ∘ (equivFun assocΣ) ∘ (invEq (Σ-cong-equiv-fst' (invEquiv (partition is-reachable-arr))))) (inl a , is-inl a) ≡⟨ refl ⟩
    -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr)))) ∘ (equivFun (invEquiv assocΣ)) ∘ (equivFun (congΣEquiv Conway-chain)) ∘ (equivFun assocΣ))
       -- (([ inl a ] , (inl a , refl)) , is-inl-a') ≡⟨ refl ⟩
    -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr)))) ∘ (equivFun (invEquiv assocΣ)) ∘ (equivFun (congΣEquiv Conway-chain)))
       -- ([ inl a ] , x) ≡⟨ {!!} ⟩
    -- -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst (invEquiv (partition is-reachable-arr)))) ∘ (invEq assocΣ))
       -- -- ([ inl a ] , y) ≡⟨ refl ⟩
    -- {!!} ≡⟨ {!!} ⟩
    -- ((equivFun (invEquiv inr≃)) ∘ (equivFun (Σ-cong-equiv-fst' (invEquiv (partition is-reachable-arr)))))
       -- (([ inl a ] , fst y), snd y) ≡⟨ refl ⟩
    -- invEq inr≃ ((invEq (partition is-reachable-arr) ([ inl a ] , fst y)) , snd y) ≡⟨ refl ⟩
    -- invEq inr≃ (fst (fst y) , snd y) ≡⟨ {!!} ⟩
    -- chainB→B {!fst (fst y) , snd y!} ∎

-- import Tricho A₀isSet B₀isSet A₀E≃B₀E as Tricho

-- fiber-arrow : (o : dArrows₀) → el-cc o ≃ fiber ∣_∣₀ (∥∥₀-map arrow o)
-- fiber-arrow o =
  -- where
  -- fiber-arrow' : (o : Arrows₀ × End) → el-cc o ≃ fiber ∣_∣₀ (∥∥₀-map arrow o)
-- isoToEquiv i
  -- where
  -- i : Iso (el-cc o) (fiber ∣_∣₀ (∥∥₀-map arrow o))
  -- Iso.fun i (a , p) = arrow a , cong (∥∥₀-map arrow) p
  -- Iso.inv i (a , p) = {!!} , {!!}
  -- Iso.rightInv i = {!!}
  -- Iso.leftInv i = {!!}

-- essentially, the left inclusion into the coproduct preserves fibers
fiberA-arr : (a : ∥ A ∥₀) → fiber ∣_∣₀ a ≃ fiber ∣_∣₀ (ArrowsS→0 (inl a))
fiberA-arr a = {!!}

Div2 : A ≃ B
Div2 = compEquiv (Σ-components A) (compEquiv (glueing-equiv' DS.Conway {!fiber-equiv!}) (invEquiv (Σ-components B)))
  where
  fiber-equiv : (a : ∥ A ∥₀) → fiber ∣_∣₀ a ≃ fiber ∣_∣₀ (equivFun DS.Conway a)
  fiber-equiv a =
    fiber ∣_∣₀ a                                                                                    ≃⟨ {!!} ⟩
    fiber ∣_∣₀ (ArrowsS→0 (inl a))                                                                  ≃⟨ {!!} ⟩
    el-cc (fw₀ (ArrowsS→0 (inl a)))                                                                 ≃⟨ {!!} ⟩
    el-cc (dArrowsS→0 (AS.fw (inl a)))                                                              ≃⟨ reachable≃f' (reachableS→0 (AS.reachable-arr→reachable' (DRS.Conway-reachable a))) ⟩
    el-cc (dArrowsS→0 (inr (DRS.ConwayFun a) , AS.reachable-end (DRS.Conway-reachable a)))          ≃⟨ {!!} ⟩
    el-cc (orient₀ (ArrowsS→0 (inr (DRS.ConwayFun a))) (AS.reachable-end (DRS.Conway-reachable a))) ≃⟨ {!!} ⟩
    fiber ∣_∣₀ (ArrowsS→0 (inr (DRS.ConwayFun a)))                                                  ≃⟨ {!!} ⟩
    fiber ∣_∣₀ (equivFun DS.Conway a)                                                               ■
