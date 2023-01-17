{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetTruncation as ∥∥₀
open import Cubical.HITs.SetQuotients as []
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary


-- usual notations

-- (this is cong)
-- ap : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
-- ap f p i = f (p i)

--- this is called funExt⁻ in the cubical library
-- happly : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
-- happly p x i = p i x

---
--- Inspection
---

-- -- already defined as singl
-- data Singleton {a} {A : Set a} (x : A) : Set a where
  -- _with≡_ : (y : A) → x ≡ y → Singleton x

-- inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
-- inspect x = x with≡ refl

-- image : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
-- image {B = B} f = Σ B (λ b → ∥ fiber f b ∥)

toSingl : {ℓ : Level} {A : Type ℓ} (a : A) → singl a
toSingl a = a , refl


-- non-dependent version of cong₂, sometimes help with inference of metavariables
cong₂-nd : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
        (f : A → B → C)
        {x y : A} (p : x ≡ y)
        {u v : B} (q : u ≡ v) →
        f x u ≡ f y v
cong₂-nd f p q = cong₂ f p q

cong₃-nd : {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {D : Type ℓ'''}
        (f : A → B → C → D)
        {x y : A} (p : x ≡ y)
        {u v : B} (q : u ≡ v)
        {s t : C} (r : s ≡ t)→
        f x u s ≡ f y v t
cong₃-nd f p q r i = f (p i) (q i) (r i)

--- NB: we could further generalize to the case where B depends on A if needed
subst₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} (C : A → B → Type ℓ'') {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b') → C a b → C a' b'
subst₂ B {a' = a'} p {b = b} q x = subst (B a') q (subst (λ a → B a b) p x)

---
--- stolen from newer cubical library
---

-- congP : {ℓ ℓ' : Level} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  -- (f : (i : I) → (a : A i) → B i a) {x : A i0} {y : A i1}
  -- (p : PathP A x y) → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
-- congP f p i = f i (p i)
-- {-# INLINE congP #-}

-- congP₂ : {ℓ ℓ' ℓ'' : Level} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  -- {C : (i : I) (a : A i) → B i a → Type ℓ''}
  -- (f : (i : I) → (a : A i) → (b : B i a) → C i a b)
  -- {x : A i0} {y : A i1} {u : B i0 x} {v : B i1 y}
  -- (p : PathP A x y) (q : PathP (λ i → B i (p i)) u v)
  -- → PathP (λ i → C i (p i) (q i)) (f i0 x u) (f i1 y v)
-- congP₂ f p q i = f i (p i) (q i)
-- {-# INLINE congP₂ #-}

-- -- NB: this one should be part of the standard library ?
-- transP : {ℓ : Level} {A B : I → Type ℓ}
         -- {x : A i0} → {y : A i1} {y' : B i0} {z : B i1}
         -- (p : PathP A x y) (q : PathP B y' z) (AB : A i1 ≡ B i0) →
         -- PathP (λ i → ((λ j →  A j) ∙ AB ∙ (λ j → B j)) i) x z
-- transP p q AB j = toPathP {!!} {!!}

-- NB: this one should be part of the standard library ?
postulate
  funExtP : {ℓ ℓ' : Level} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    {f : (a : A i0) → B i0 a} {g : (a : A i1) → B i1 a} →
    ({x : A i0} {y : A i1} (p : PathP A x y) → PathP (λ i → B i (p i)) (f x) (g y)) →
    PathP (λ i → (a : A i) → B i a) f g
  -- funExtP {A = A} {B = B} {f = f} {g = g} p = toPathP (funExt (λ x → fromPathP {A = (λ i → B i (transp (λ j → A (i ∨ ~ j)) i x))} (p {!toPathP {A = A} {x = (transp (λ j → A (~ j)) i0 x)} {y = x} (transportTransport⁻ (λ i → A i) x)!})))

-- same as isPropΠ but with implicit arguments
isPropΠ' : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → (h : (x : A) → isProp (B x)) → isProp ({x : A} → B x)
isPropΠ' h f g i {x} = h x (f {x}) (g {x}) i

-- a variant of isPropΣ
isPropΣ' : {ℓ ℓ' : Level} {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → isProp (B x)) → ((x y : A) → B x → B y → x ≡ y) → isProp (Σ A B)
isPropΣ' prop eq (a , b) (a' , b') = ΣPathP ((eq _ _ b b') , (toPathP (prop _ _ _)))

---
--- custom elimination principle
---

∥∥-elim : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (SB : isSet B) (f : A → B) → ((a a' : A) → f a ≡ f a') → ∥ A ∥₁ → B
∥∥-elim {ℓ} {ℓ'} {A} {B} SB f p a = fst (F a)
  where
  im : Type (ℓ-max ℓ ℓ')
  im = Σ B (λ b → ∥ Σ A (λ a → f a ≡ b) ∥₁)
  im-isProp : isProp im
  im-isProp (b , e) (b' , e') = ΣPathP (b≡b' , toPathP (isPropPropTrunc _ e'))
    where
    b≡b' : b ≡ b'
    b≡b' = ∥∥.elim (λ _ → SB b b') (λ { (a , q) → ∥∥.elim (λ _ → SB b b') (λ { (a' , q') → sym q ∙ p a a' ∙ q' }) e' }) e
  F : ∥ A ∥₁ → im
  F a = ∥∥.elim (λ _ → im-isProp) (λ a → f a , ∣ a , refl ∣₁) a

-- []-rec : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} (R : A → A → Type ℓ') {B : Type ℓ''} →
        -- (f : (a : A) → B) →
        -- ({a b : A} → R a b → f a ≡ f b) →
        -- (A / R) → B
-- []-rec {A = A} R {B = B} f p [a] = {!!}
  -- where
  -- B' : Type _
  -- B' = Σ B (λ b → Σ A (λ a → (f a ≡ b) × ([ a ] ≡ [a])))
  -- B'-isSet
  -- b : B'
  -- b = Cubical.HITs.SetQuotients.elim {B = λ _ → B'} {!!} {!!} {!!} [a]

-- []-comp :
  -- {ℓ ℓ' : Level} {A : Type ℓ} {R : A → A → Type ℓ'} →
  -- {B : A / R → Type ℓ} →
  -- (Bset : (x : A / R) → isSet (B x)) →
  -- (f : (a : A) → (B [ a ])) →
  -- (feq : (a b : A) (r : R a b) → PathP (λ i → B (eq/ a b r i)) (f a) (f b)) →
  -- (a : A) → [].elim Bset f feq [ a ] ≡ f a
-- []-comp Bset f feq a = refl

-- []-elim :
  -- {ℓ ℓ' : Level} {A : Type ℓ} {R : A → A → Type ℓ'} →
  -- {B : A / R → Type ℓ} →
  -- (Bset : (x : A / R) → isSet (B x)) →
  -- (x : A / R) → 
  -- (f : (a : A) → [ a ] ≡ x → (B [ a ])) →
  -- (feq : (a b : A) (r : R a b) → PathP (λ i → B (eq/ a b r i)) (f a {!!}) (f b {!!})) →
  -- B x
-- []-elim = {!!}

-- NB: is seems that this useful principle is not part of the standard library
-- (at least for equalities: we have have equivPi for equivalences)
Π≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B C : A → Type ℓ'} → ((x : A) → B x ≡ C x) → ((x : A) → B x) ≡ ((x : A) → C x)
Π≡ {A = A} p i = (x : A) → p x i

Σfun : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'} →
       (f : A → A') (g : {a : A} → B a → B' (f a)) →
       (Σ A B → Σ A' B')
Σfun f g (a , b) = (f a , g b)

equivΣProp : {ℓ ℓ' : Level} {A A' : Type ℓ} {B : A → Type ℓ'} {B' : A' → Type ℓ'}
             (e : A ≃ A')
             (g : {a : A} → B a → B' (equivFun e a)) (g' : {a' : A'} → B' a' → B (invEq e a')) → ((a : A) → isProp (B a)) → ((a' : A') → isProp (B' a')) →
             Σ A B ≃ Σ A' B'
equivΣProp {_} {_} {A} {A'} {B} {B'} e g g' P P' = isoToEquiv i
  where
  f : A → A'
  f = equivFun e
  fi : Iso A A'
  fi = equivToIso e
  i : Iso (Σ A B) (Σ A' B')
  Iso.fun i = Σfun f g
  Iso.inv i = Σfun (Iso.inv fi) g'
  Iso.rightInv i (a' , b') = Σ≡Prop P' (Iso.rightInv fi a')
  Iso.leftInv i (a , b) = Σ≡Prop P (Iso.leftInv fi a)

⊎-×-≃ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
⊎-×-≃ {A = A} {B = B} {C = C} = isoToEquiv (iso f g f-g g-f)
  where
  f : (A ⊎ B) × C → (A × C) ⊎ (B × C)
  f (inl a , c) = inl (a , c)
  f (inr b , c) = inr (b , c)
  g : (A × C) ⊎ (B × C) → (A ⊎ B) × C
  g (inl (a , c)) = (inl a) , c
  g (inr (b , c)) = (inr b) , c
  g-f : (x : (A ⊎ B) × C) → g (f x) ≡ x
  g-f (inl a , c) = refl
  g-f (inr b , c) = refl
  f-g : (x : (A × C) ⊎ (B × C)) → f (g x) ≡ x
  f-g (inl (a , c)) = refl
  f-g (inr (b , c)) = refl

-- bring back from old cubical library
Σ-ap :
  ∀ {ℓ ℓ'} {X X' : Type ℓ} {Y : X → Type ℓ'} {Y' : X' → Type ℓ'}
  → (isom : X ≡ X')
  → ((x : X) → Y x ≡ Y' (transport isom x))
  → (Σ X Y) ≡ (Σ X' Y')
Σ-ap {X = X} p q = ua (Σ-cong-equiv (pathToEquiv p) (λ x → pathToEquiv (q x)))

---
--- Injections
---

isInjection : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → (A → B) → Type (ℓ-max ℓ ℓ')
isInjection {A = A} f = {x y : A} → f x ≡ f y → x ≡ y

isEmbedding→isInjection : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} {f : A → B} → isEmbedding f → isInjection f
isEmbedding→isInjection emb = invEq (_ , emb _ _)

-- useful lemmas on coproducts

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

disjoint-coprod' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a : A} {b : B} → inl a ≡ inr b → Lift {_} {ℓ} ⊥
disjoint-coprod' {ℓ} {ℓ'} {A = A} {B = B} {a} p = subst A⊥ p a
  where
  A⊥ : A ⊎ B → Type ℓ
  A⊥ (inl _) = A
  A⊥ (inr _) = Lift ⊥

-- injections into the coproduct are disjoint
disjoint-coprod : {a : A} {b : B} → inl a ≡ inr b → ⊥
disjoint-coprod p with disjoint-coprod' p
... | ()

inl≢inr = disjoint-coprod

inl-injective : {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
-- inl-injective {x = x} p = cong (λ { (inl x) → x ; (inr _) → x }) p
inl-injective p = isEmbedding→isInjection isEmbedding-inl p

inr-injective : {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
-- inr-injective {x = x} p = cong (λ { (inl _) → x ; (inr x) → x }) p
inr-injective p = isEmbedding→isInjection isEmbedding-inr p

coprod-case : (x : A ⊎ B) → Σ A (λ a → x ≡ inl a) ⊎ Σ B (λ b → x ≡ inr b)
coprod-case (inl a) = inl (a , refl)
coprod-case (inr b) = inr (b , refl)

data in-left {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} : A ⊎ B → Type (ℓ-max ℓ ℓ') where
  is-inl : (a : A) → in-left (inl a)

data in-right {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} : A ⊎ B → Type (ℓ-max ℓ ℓ') where
  is-inr : (b : B) → in-right (inr b)

in-left-isProp : (x : A ⊎ B) → isProp (in-left x)
in-left-isProp .(inl a) (is-inl a) (is-inl .a) = refl

in-right-isProp : (x : A ⊎ B) → isProp (in-right x)
in-right-isProp .(inr b) (is-inr b) (is-inr .b) = refl

is-left : {x : A ⊎ B} → in-left x → Σ A (λ a → x ≡ inl a)
is-left (is-inl a) = a , refl

is-right : {x : A ⊎ B} → in-right x → Σ B (λ b → x ≡ inr b)
is-right (is-inr b) = b , refl

get-left : {x : A ⊎ B} → in-left x → A
get-left (is-inl a) = a

get-right : {x : A ⊎ B} → in-right x → B
get-right (is-inr b) = b

inl-get-left : {x : A ⊎ B} (l : in-left x) → inl (get-left l) ≡ x
inl-get-left (is-inl a) = refl

inr-get-right : {x : A ⊎ B} (r : in-right x) → inr (get-right r) ≡ x
inr-get-right (is-inr b) = refl

inl≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ Σ (A ⊎ B) in-left
inl≃ = isoToEquiv i
  where
  i : Iso A (Σ (A ⊎ B) in-left)
  Iso.fun i a = inl a , is-inl a
  Iso.inv i (_ , l) = get-left l
  Iso.rightInv i (_ , l) = Σ≡Prop in-left-isProp (inl-get-left l)
  Iso.leftInv i a = refl

inr≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B ≃ Σ (A ⊎ B) in-right
inr≃ = isoToEquiv i
  where
  i : Iso B (Σ (A ⊎ B) in-right)
  Iso.fun i b = inr b , is-inr b
  Iso.inv i (_ , r) = get-right r
  Iso.rightInv i (_ , r) = Σ≡Prop in-right-isProp (inr-get-right r)
  Iso.leftInv i b = refl

---
--- Existence of a minimal element
---

-- open import Cubical.Induction.WellFounded

-- module _ {ℓ ℓ' : Level} {A : Type ℓ} (_<_ : A → A → Type ℓ') where
  -- Antisymmetric : Type _
  -- Antisymmetric = {x y : A} → x < y → y < x → ⊥

  -- Irreflexive : Type _
  -- Irreflexive = (x : A) → ¬ (x < x)

  -- Total : Type _
  -- Total = (x y : A) → (x < y) ⊎ (y < x)

  -- WellFounded→Irreflexive : WellFounded _<_ → Irreflexive
  -- WellFounded→Irreflexive wf = WFI.induction wf {P = λ x → ¬ (x < x)} (λ x h x<x → h x x<x x<x)

  -- reveal : isSet A →
           -- BinaryRelation.isPropValued _<_ → Antisymmetric → WellFounded _<_ → Total →
           -- {ℓ'' : Level} → (P : A → Type ℓ'') → ((a : A) → isProp (P a)) → ((a : A) → Dec (P a)) →
           -- ∥ Σ A P ∥ → Σ A P
  -- reveal Aset <p asym wf tot P Pp dec ex = {!!}
    -- where
    -- irr : Irreflexive
    -- irr = WellFounded→Irreflexive wf
    -- _≤_ : A → A → Type _
    -- x ≤ y = (x ≡ y) ⊎ (x < y)
    -- ≤-isProp : (a a' : A) → isProp (a ≤ a')
    -- ≤-isProp a a' le le' with le | le'
    -- ... | inl a≡a' | inl a≡a'' = cong inl (Aset _ _ a≡a' a≡a'')
    -- ... | inl a≡a' | inr a<a' = ⊥.rec (irr a' (subst (λ a → a < a') a≡a' a<a'))
    -- ... | inr a<a' | inl a≡a' = ⊥.rec (irr a' (subst (λ a → a < a') a≡a' a<a'))
    -- ... | inr a<a' | inr a<a'' = cong inr (<p _ _ a<a' a<a'')
    -- isFirst : A → Type _
    -- isFirst a = P a × ({a' : A} → P a' → a ≤ a')
    -- isFirst-unique : {a a' : A} → isFirst a → isFirst a' → a ≡ a'
    -- isFirst-unique {a} {a'} fa fa' with tot a a'
    -- isFirst-unique {a} {a'} fa fa' | inl a<a' with snd fa' (fst fa)
    -- isFirst-unique {a} {a'} fa fa' | inl a<a' | inl a'≡a = sym a'≡a
    -- isFirst-unique {a} {a'} fa fa' | inl a<a' | inr a'<a = ⊥.rec (asym a<a' a'<a)
    -- isFirst-unique {a} {a'} fa fa' | inr a'<a with snd fa (fst fa')
    -- isFirst-unique {a} {a'} fa fa' | inr a'<a | inl a≡a' = a≡a'
    -- isFirst-unique {a} {a'} fa fa' | inr a'<a | inr a<a' = ⊥.rec (asym a<a' a'<a)
    -- isFirst-isProp : (a : A) → isProp (isFirst a)
    -- isFirst-isProp a = isProp× (Pp a) (isPropΠ' (λ a' → isPropΠ (λ _ → ≤-isProp a a')))
    -- first-isProp : isProp (Σ A isFirst)
    -- first-isProp = isPropΣ' isFirst-isProp (λ a a' p q → isFirst-unique p q)
    -- firstUntil : (a : A) → Type _
    -- firstUntil a = Σ A isFirst ⊎ ((a' : A) → a' < a → ¬ (P a'))
    -- search : (a : A) → firstUntil a
    -- search = WFI.induction wf {P = firstUntil} ind
      -- where
      -- ind : (a : A) → ((a' : A) → a' < a → firstUntil a') → firstUntil a
      -- ind a h = {!!}

Discrete⊎ : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → Discrete A → Discrete B → Discrete (A ⊎ B)
Discrete⊎ DA DB (inl x) (inl y) with DA x y
... | yes p = yes (cong inl p)
... | no ¬p = no (¬p ∘ inl-injective)
Discrete⊎ DA DB (inr x) (inr y) with DB x y
... | yes p = yes (cong inr p)
... | no ¬p = no (¬p ∘ inr-injective)
Discrete⊎ DA DB (inl x) (inr y) = no inl≢inr
Discrete⊎ DA DB (inr x) (inl y) = no (inl≢inr ∘ sym)

Discrete× : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → Discrete A → Discrete B → Discrete (A × B)
Discrete× DA DB (a , b) (a' , b') with DA a a' | DB b b'
... | yes p | yes q = yes (ΣPathP (p , q))
... | yes p | no ¬q = no (¬q ∘ cong snd)
... | no ¬p | _ = no (¬p ∘ cong fst)

---
--- Decidability
---

Dec× : {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A × B)
Dec× (yes a) (yes b) = yes (a , b)
Dec× (yes a) (no ¬b) = no λ { (_ , b) → ¬b b}
Dec× (no ¬a) (yes b) = no λ { (a , _) → ¬a a}
Dec× (no ¬a) (no ¬b) = no λ { (a , b) → ¬a a}

Dec¬ : {ℓ : Level} {A : Type ℓ} → Dec A → Dec (¬ A)
Dec¬ (yes a) = no λ ¬a → ¬a a
Dec¬ (no ¬a) = yes λ a → ¬a a

Dec→NNE : {ℓ : Level} {A : Type ℓ} → Dec A → ¬ ¬ A → A
Dec→NNE (yes a) ¬¬a = a
Dec→NNE (no ¬a) ¬¬a = ⊥.elim (¬¬a ¬a)

---
--- Logic
---

¬∀¬¬⇒¬¬∃¬ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → ¬ ((x : A) → ¬ ¬ (B x)) → ¬ ¬ (Σ A (λ x → ¬ (B x)))
¬∀¬¬⇒¬¬∃¬ f g = f λ a b → g (a , b)
