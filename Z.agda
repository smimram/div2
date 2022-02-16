{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty hiding (elim ; rec)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.Order as ℕ using ()
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

data ℤ : Type₀  where
  zero  : ℤ
  suc   : ℤ → ℤ
  predl : ℤ → ℤ
  predr : ℤ → ℤ
  predl-suc : (z : ℤ) → predl (suc z) ≡ z
  suc-predr : (z : ℤ) → suc (predr z) ≡ z

pred = predl
pred-suc = predl-suc

one : ℤ
one = suc zero

-one : ℤ
-one = pred zero

predl≡predr : (z : ℤ) → predl z ≡ predr z
predl≡predr z = cong predl (sym (suc-predr z)) ∙ predl-suc (predr z)

suc-predl : (n : ℤ) → suc (predl n) ≡ n
suc-predl n = cong (λ n → suc (predl n)) (sym (suc-predr n)) ∙ cong suc (predl-suc _) ∙ suc-predr n

suc-pred = suc-predl

elim : ∀ {ℓ} (A : ℤ → Type ℓ)
       (z : A zero)
       (s : (n : ℤ) → A n → A (suc n))
       (p : (n : ℤ) → A n → A (predl n))
       (p' : (n : ℤ) → A n → A (predr n))
       (ps : (n : ℤ) → (x : A n) → PathP (λ i → A (predl-suc n i)) (p (suc n) (s n x)) x)
       (sp' : (n : ℤ) → (x : A n) → PathP (λ i → A (suc-predr n i)) (s (predr n) (p' n x)) x)
       (n : ℤ) → A n
elim A z s p p' ps sp' zero = z
elim A z s p p' ps sp' (suc n) = s n (elim A z s p p' ps sp' n)
elim A z s p p' ps sp' (predl n) = p n (elim A z s p p' ps sp' n)
elim A z s p p' ps sp' (predr n) = p' n (elim A z s p p' ps sp' n)
elim A z s p p' ps sp' (predl-suc n i) = ps n (elim A z s p p' ps sp' n) i
elim A z s p p' ps sp' (suc-predr n i) = sp' n (elim A z s p p' ps sp' n) i

-- same as above but with same function for the two predecessors (which is what
-- we use in practice)
elim' : ∀ {ℓ} (A : ℤ → Type ℓ)
        (z : A zero)
        (s : (n : ℤ) → A n → A (suc n))
        (p : (n : ℤ) → A n → A (predl n))
        (ps : (n : ℤ) → (x : A n) → PathP (λ i → A (predl-suc n i)) (p (suc n) (s n x)) x)
        (sp' : (n : ℤ) → (x : A n) → PathP (λ i → A (suc-predr n i)) (s (predr n) (subst A (predl≡predr n) (p n x))) x)
        (n : ℤ) → A n
elim' A z s p ps sp' n = elim A z s p (λ n An → subst A (predl≡predr n) (p n An)) ps sp' n

rec : ∀ {ℓ} {A : Type ℓ}
       (z : A)
       (s : ℤ → A → A)
       (p : ℤ → A → A)
       (p' : ℤ → A → A)
       (ps : (n : ℤ) → (x : A) → (p (suc n) (s n x)) ≡ x)
       (sp' : (n : ℤ) → (x : A) → (s (predr n) (p' n x)) ≡ x) →
       ℤ → A
rec {A = A} z s p p' ps sp' n = elim (λ _ → A) z s p p' ps sp' n

-- elim : ∀ {ℓ} (A : ℤ → Type ℓ)
      -- (z : A zero)
      -- (s : {n : ℤ} → A n → A (suc n))
      -- (p : {n : ℤ} → A n → A (predl n))
      -- (ps : {n : ℤ} → (x : A n) → PathP (λ i → A (predl-suc n i)) (p (s x)) x)
      -- (sp : {n : ℤ} → (x : A n) → PathP (λ i → A (suc-predl n i)) (s (p x)) x)
      -- (n : ℤ) → A n
-- elim A z s p ps sp n = elim' A z (λ n x → s x) (λ n x → p x) (λ n x → subst A (predl≡predr n) (p x)) (λ n x → ps x) (λ n x → {!transport (sym ?!}) n

-- simpl : ℤ → ℤ
-- simpl zero = zero
-- simpl (suc n) with simpl n
-- ... | zero = suc zero
-- ... | suc m = suc (suc m)
-- ... | predl m = m
-- ... | predr m = m
-- ... | predl-suc zero i = suc zero
-- ... | predl-suc (suc m) i = suc (suc m)
-- ... | predl-suc (predl m) i = suc-predl m i
-- ... | predl-suc (predr m) i = suc-predr m i
-- ... | predl-suc (predl-suc m i) j = {!!}
-- ... | predl-suc (suc-predr m i) j = {!!}
-- ... | suc-predr zero i = cong suc (suc-predr zero) i
-- ... | suc-predr (suc m) i = cong suc (suc-predr (suc m)) i
-- ... | suc-predr (predl m) i = ((cong suc (suc-predr (predl m))) ∙ (suc-predl m)) i
-- ... | suc-predr (predr m) i = ((cong suc (suc-predr (predr m))) ∙ (suc-predr m)) i
-- ... | suc-predr (predl-suc m i) j = {!!}
-- ... | suc-predr (suc-predr m i) j = {!!}
-- simpl (predl n) with simpl n
-- ... | zero = predl zero
-- ... | suc m = m
-- ... | predl m = predl (predl m)
-- ... | predr m = predl (predl m)
-- ... | predl-suc m i = {!!}
-- ... | suc-predr m i = {!!}
-- simpl (predr n) with simpl n
-- ... | zero = predl zero
-- ... | suc m = n
-- ... | predl m = predl (predl n)
-- ... | predr m = predl (predl n)
-- ... | predl-suc m i = {!!}
-- ... | suc-predr m i = {!!}
-- simpl (predl-suc n i) = {!!}
-- simpl (suc-predr n i) = {!!}

postulate discrete : Discrete ℤ
-- discreteℤ zero zero = yes refl
-- discreteℤ zero (suc n) = {!!}
-- discreteℤ zero (predl n) = {!!}
-- discreteℤ zero (predr n) = {!!}
-- discreteℤ zero (predl-suc n i) = {!!}
-- discreteℤ zero (suc-predr n i) = {!!}
-- discreteℤ (suc m) n = {!!}
-- discreteℤ (predl m) zero = {!!}
-- discreteℤ (predl m) (suc n) = {!!}
-- discreteℤ (predl m) (predl n) with discreteℤ m n
-- ... | yes p = yes (cong predl p)
-- ... | no ¬p = no λ m-≡n- → ¬p (sym (suc-predl m) ∙ cong suc m-≡n- ∙ suc-predl n)
-- discreteℤ (predl m) (predr n) = {!!}
-- discreteℤ (predl m) (predl-suc n i) = {!!}
-- discreteℤ (predl m) (suc-predr n i) = {!!}
-- discreteℤ (predr m) n = {!!}
-- discreteℤ (predl-suc m i) n = {!!}
-- discreteℤ (suc-predr m i) n = {!!}

ℤ-isSet : isSet ℤ
ℤ-isSet = Discrete→isSet discrete

postulate
  -- We would need discreteℤ to compute in order to be able to show this one
  -- with subst
  1≢0 : ¬ (suc zero ≡ zero)

_+_ : ℤ → ℤ → ℤ
zero + n = n
suc m + n = suc (m + n)
predl m + n = predl (m + n)
predr m + n = predr (m + n)
predl-suc m i + n = predl-suc (m + n) i
suc-predr m i + n = suc-predr (m + n) i

postulate
  +-assoc : (m n o : ℤ) → m + (n + o) ≡ (m + n) + o
  +-comm : (m n : ℤ) → m + n ≡ n + m
  zero-+ : (n : ℤ) → zero + n ≡ n
  +-zero : (n : ℤ) → n + zero ≡ n
  +-suc : (m n : ℤ) → m + suc n ≡ suc (m + n)
  +-pred : (m n : ℤ) → m + pred n ≡ pred (m + n)
  +-predr : (m n : ℤ) → m + predr n ≡ predr (m + n)
  +1-suc : (n : ℤ) → n + one ≡ suc n
  -1+suc : (n : ℤ) → -one + suc n ≡ n
  suc+-1 : (n : ℤ) → suc n + -one ≡ n

cong-+-r : (m : ℤ) {n n' : ℤ} → n ≡ n' → m + n ≡ m + n'
cong-+-r m p = cong (λ n → m + n) p

-- opposite of an integer
neg : ℤ → ℤ
neg zero = zero
neg (suc n) = predl (neg n)
neg (predl n) = suc (neg n)
neg (predr n) = suc (neg n)
neg (predl-suc n i) = suc-predl (neg n) i
neg (suc-predr n i) = predl-suc (neg n) i

postulate
  neg-neg : (n : ℤ) → neg (neg n) ≡ n
  neg+≡0 : (n : ℤ) → (neg n) + n ≡ zero
  +neg≡0 : (n : ℤ) → n + (neg n) ≡ zero
  neg-+ : (m n : ℤ) → neg (m + n) ≡ neg m + neg n

_-_ : ℤ → ℤ → ℤ
m - n = m + neg n

postulate
  n-n≡0 : (n : ℤ) → n - n ≡ zero
  -1-pred : (n : ℤ) → n - one ≡ pred n

-- op-op : (n : ℤ) → op (op n) ≡ n
-- op-op zero = refl
-- op-op (suc n) = cong suc (op-op n)
-- op-op (predl n) = cong predl (op-op n)
-- op-op (predr n) = cong predl (op-op n) ∙ predl≡predr n
-- op-op (predl-suc n i) = {!!} -- op (op (predl-suc n i)) ≡ predl-suc n i
-- op-op (suc-predr n i) = {!!} -- op (op (suc-predr n i)) ≡ suc-predr n i

fromℕ : ℕ → ℤ
fromℕ ℕ.zero = zero
fromℕ (ℕ.suc n) = suc (fromℕ n)

postulate
  fromℕ-+ : (m n : ℕ) → fromℕ (m ℕ.+ n) ≡ fromℕ m + fromℕ n

---
--- Comparison with non-quotiented definition
---

open import Cubical.Data.Int as Int using (Int ; pos ; negsuc ; sucInt ; predInt ; predSuc ; sucPred)

toInt : ℤ → Int
toInt zero = pos ℕ.zero
toInt (suc n) = sucInt (toInt n)
toInt (predl n) = predInt (toInt n)
toInt (predr n) = predInt (toInt n)
toInt (predl-suc n i) = predSuc (toInt n) i
toInt (suc-predr n i) = sucPred (toInt n) i

fromInt : Int → ℤ
fromInt (pos n) = fromℕ n
fromInt (negsuc n) = neg (fromℕ (ℕ.suc n))

open import Cubical.Core.Everything
open import Cubical.Foundations.Isomorphism

postulate
  ℤ≃Int : ℤ ≃ Int
  -- ℤ≃Int = isoToEquiv (iso toInt fromInt {!!} {!!})

---
--- Even / odd predicates
---

-- is-even : ℤ → Type₀
-- is-odd : ℤ → Type₀

-- is-even zero = Unit
-- is-even (suc n) = is-odd n
-- is-even (predl n) = is-odd n
-- is-even (predr n) = is-odd n
-- is-even (predl-suc n i) = is-even n
-- is-even (suc-predr n i) = is-even n

-- is-odd zero = ⊥
-- is-odd (suc n) = is-even n
-- is-odd (predl n) = is-even n
-- is-odd (predr n) = is-even n
-- is-odd (predl-suc n i) = is-odd n
-- is-odd (suc-predr n i) = is-odd n

data is-even : ℤ → Type₀
data is-odd  : ℤ → Type₀

data is-even where
  even-zero  : is-even zero
  even-suc   : {n : ℤ} → is-odd n → is-even (suc n)
  even-predl : {n : ℤ} → is-odd n → is-even (predl n)
  even-predr : {n : ℤ} → is-odd n → is-even (predr n)

data is-odd where
  odd-suc   : {n : ℤ} → is-even n → is-odd (suc n)
  odd-predl : {n : ℤ} → is-even n → is-odd (predl n)
  odd-predr : {n : ℤ} → is-even n → is-odd (predr n)

-- is-even-zero : (e : is-even zero) → e ≡ even-zero
-- is-even-zero e = {!!}

-- TODO
postulate is-even-isProp : {n : ℤ} → isProp (is-even n)
postulate is-odd-isProp  : {n : ℤ} → isProp (is-odd n)
-- is-even-isProp {zero} e e' = {!!}
-- is-even-isProp {suc n} e e' = {!!}
-- is-even-isProp {predl n} e e' = {!!}
-- is-even-isProp {predr n} e e' = {!!}
-- is-even-isProp {predl-suc n i} e e' = {!!}
-- is-even-isProp {suc-predr n i} e e' = {!!}
-- is-odd-isProp o o' = {!!}

postulate even-or-odd : (n : ℤ) → ¬ (is-even n × is-odd n)
-- even-or-odd zero (e , o) = {!!}
-- even-or-odd (suc n) (e , o) = {!!}
-- even-or-odd (predl n) (e , o) = {!!}
-- even-or-odd (predr n) (e , o) = {!!}
-- even-or-odd (predl-suc n i) (e , o) = {!!}
-- even-or-odd (suc-predr n i) (e , o) = {!!}

postulate
  even-suc-inv : (n : ℤ) → is-even (suc n) → is-odd n

open import Cubical.Data.Sum

dec-parity : (n : ℤ) → Type₀
dec-parity n = is-even n ⊎ is-odd n

parity : (n : ℤ) → dec-parity n
parity zero = inl even-zero
parity (suc n) with parity n
... | inl e = inr (odd-suc e)
... | inr o = inl (even-suc o)
parity (predl n) with parity n
... | inl e = inr (odd-predl e)
... | inr o = inl (even-predl o)
parity (predr n) with parity n
... | inl e = inr (odd-predr e)
... | inr o = inl (even-predr o)
parity (predl-suc n i) = lem n i
  where
  --- NB: this obvious idea does not work because it does not terminate...
  -- lem : (n : ℤ) → PathP (λ i → dec-parity (predl-suc n i)) (parity (predl (suc n))) (parity n)
  -- lem n = cong parity (predl-suc n)
  -- TODO
  postulate lem : (n : ℤ) → PathP (λ i → dec-parity (predl-suc n i)) (parity (predl (suc n))) (parity n)
  -- lem zero = {!!}
  -- lem (suc n) = {!!}
  -- lem (predl n) = {!!}
  -- lem (predr n) = {!!}
  -- lem (predl-suc n i) = {!!}
  -- lem (suc-predr n i) = {!!}
  -- lem : (n : ℤ) →  transport (cong dec-parity (predl-suc n)) (parity (predl (suc n))) ≡ (parity n)
  -- lem zero = {!refl!}
  -- lem (suc n) = {!!}
  -- lem (predl n) = {!!}
  -- lem (predr n) = {!!}
  -- lem (predl-suc n i) = {!!}
  -- lem (suc-predr n i) = {!!}
parity (suc-predr n i) = lem n i
  where
  postulate lem : (n : ℤ) → PathP (λ i → dec-parity (suc-predr n i)) (parity (suc (predr n))) (parity n)

-- parity-rec : ∀ {ℓ} (A : ℤ → Type ℓ) → ({n : ℤ} → is-even n → A n) → ({n : ℤ} → is-odd n → A n) → (n : ℤ) → A n
-- parity-rec A even odd n with parity n
-- ... | inl e = even e
-- ... | inr o = odd o

open import Nat as ℕ using (suc ; even-zero ; even-suc ; odd-suc)

is-evenℕ : {n : ℕ} → ℕ.is-even n → is-even (fromℕ n)
is-oddℕ  : {n : ℕ} → ℕ.is-odd n → is-odd (fromℕ n)
is-evenℕ even-zero    = even-zero
is-evenℕ (even-suc p) = even-suc (is-oddℕ p)
is-oddℕ  (odd-suc p)  = odd-suc  (is-evenℕ p)

abs : ℤ → ℕ
abs n = Int.abs (toInt n)

postulate
  zero-abs : {n : ℤ} → abs n ≡ 0 → n ≡ zero

-- order

_≤_ : ℤ → ℤ → Type₀
m ≤ n = Σ ℕ λ k → fromℕ k + m ≡ n

_<_ : ℤ → ℤ → Type₀
m < n = suc m ≤ n

_>_ : ℤ → ℤ → Type₀
m > n = n < m

0<1 : zero < one
0<1 = 0 , refl

≤-refl : {n : ℤ} → n ≤ n
≤-refl {n} = 0 , refl

≤-≡ : {m n : ℤ} → m ≡ n → m ≤ n
≤-≡ {m} {n} p = subst (λ n → m ≤ n) p ≤-refl

≤-path : {m n : ℤ} → m ≡ n → m ≤ n
≤-path {m} {n} p = subst (λ n → m ≤ n) p ≤-refl

≤-trans : {m n o : ℤ} → m ≤ n → n ≤ o → m ≤ o
≤-trans {m} {n} {o} m≤n n≤o = fst m≤n ℕ.+ fst n≤o ,
  (fromℕ (fst m≤n ℕ.+ fst n≤o) + m          ≡⟨ cong (λ n → n + m) (fromℕ-+ (fst m≤n) (fst n≤o)) ⟩
  (fromℕ (fst m≤n) + fromℕ (fst n≤o)) + m   ≡⟨ cong (λ n → n + m) (+-comm (fromℕ (fst m≤n)) _) ⟩
  (fromℕ (fst n≤o) + fromℕ (fst m≤n)) + m   ≡⟨ sym (+-assoc (fromℕ (fst n≤o)) _ _) ⟩
  (fromℕ (fst n≤o) + (fromℕ (fst m≤n) + m)) ≡⟨ cong (λ n → fromℕ (fst n≤o) + n) (snd m≤n) ⟩
  fromℕ (fst n≤o) + n                       ≡⟨ snd n≤o ⟩
  o                                         ∎)

≤-suc : {m n : ℤ} → m ≤ n → m ≤ suc n
≤-suc (k , p) = suc k , cong suc p

<→≤ : {m n : ℤ} → m < n → m ≤ n
<→≤ m<n = ≤-trans (≤-suc ≤-refl) m<n

postulate
  ≤-neg : {m n : ℤ} → neg n ≤ neg m → m ≤ n
  pos-fromℕ : {n : ℤ} → zero ≤ n → Σ ℕ (λ n' → n ≡ fromℕ n')

data Trichotomy (m n : ℤ) : Type₀ where
  lt : m < n → Trichotomy m n
  eq : m ≡ n → Trichotomy m n
  gt : n < m → Trichotomy m n

postulate
  _≟_ : (m n : ℤ) → Trichotomy m n

-- even/odd folding of ℤ into ℕ
ℤ≃ℕ : ℤ ≃ ℕ
ℤ≃ℕ = isoToEquiv i
  where
  f : ℤ → ℕ
  f n with toInt n
  ... | pos k = 2 ℕ.* k
  ... | negsuc k = suc (2 ℕ.* k)
  g : ℕ → ℤ
  g n = aux (ℕ.parity n)
    where
    aux : {n : ℕ} → ℕ.is-even n ⊎ ℕ.is-odd n → ℤ
    aux (inl even-zero) = ℤ.zero
    aux (inl (even-suc (odd-suc p))) = suc (aux (inl p))
    aux (inr (odd-suc even-zero)) = neg one
    aux (inr (odd-suc (even-suc p))) = pred (aux (inr p))
  i : Iso ℤ ℕ
  Iso.fun i = f
  Iso.inv i = g
  Iso.rightInv i n = {!!}
  Iso.leftInv i n = {!!}

-- a well founded order on ℤ
_≺_ : ℤ → ℤ → Type₀
m ≺ n = equivFun ℤ≃ℕ m ℕ.< equivFun ℤ≃ℕ n

open import Cubical.Foundations.Univalence

postulate
  ≺≡< : transport (cong (λ N → N → N → Type₀) (ua ℤ≃ℕ)) _≺_ ≡ ℕ._<_

open import Cubical.Induction.WellFounded

postulate
  ≺-wellfounded : WellFounded _≺_
  -- -- from ℕ.<-wellfounded
  -- ≺-wellfounded = subst WellFounded {!sym ≺≡<!} {!ℕ.<-wellfounded!} -- 
