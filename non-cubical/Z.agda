{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

module Z where

open import HoTT.Foundations.Prelude
open import HoTT.Data.Sigma
open import HoTT.Data.Sum hiding (elim)
open import HoTT.Data.Empty hiding (elim)
open import HoTT.Data.Unit
open import HoTT.Data.Nat renaming (_+_ to _+ℕ_)
open import HoTT.Relation.Nullary
open import HoTT.Relation.Nullary.DecidableEq

data ℤ : Type₀ where
  zero  : ℤ
  suc   : ℤ → ℤ
  predl : ℤ → ℤ
  predr : ℤ → ℤ

postulate
  predl-suc : (z : ℤ) → predl (suc z) ≡ z
  suc-predr : (z : ℤ) → suc (predr z) ≡ z
  elim : ∀ {ℓ} (A : ℤ → Type ℓ)
    (z : A zero)
    (s : (n : ℤ) → A n → A (suc n))
    (p : (n : ℤ) → A n → A (predl n))
    (p' : (n : ℤ) → A n → A (predr n))
    (ps : (n : ℤ) → (x : A n) → PathP A (predl-suc n) (p (suc n) (s n x)) x)
    (sp' : (n : ℤ) → (x : A n) → PathP A (suc-predr n) (s (predr n) (p' n x)) x)
    (n : ℤ) → A n
  comp-zero : ∀ {ℓ} (A : ℤ → Type ℓ)
    (z : A zero)
    (s : (n : ℤ) → A n → A (suc n))
    (p : (n : ℤ) → A n → A (predl n))
    (p' : (n : ℤ) → A n → A (predr n))
    (ps : (n : ℤ) → (x : A n) → PathP A (predl-suc n) (p (suc n) (s n x)) x)
    (sp' : (n : ℤ) → (x : A n) → PathP A (suc-predr n) (s (predr n) (p' n x)) x) →
    elim A z s p p' ps sp' zero ≡ z
  comp-suc : ∀ {ℓ} (A : ℤ → Type ℓ)
    (z : A zero)
    (s : (n : ℤ) → A n → A (suc n))
    (p : (n : ℤ) → A n → A (predl n))
    (p' : (n : ℤ) → A n → A (predr n))
    (ps : (n : ℤ) → (x : A n) → PathP A (predl-suc n) (p (suc n) (s n x)) x)
    (sp' : (n : ℤ) → (x : A n) → PathP A (suc-predr n) (s (predr n) (p' n x)) x)
    (n : ℤ) → elim A z s p p' ps sp' (suc n) ≡ s n (elim A z s p p' ps sp' n)
  comp-predl : ∀ {ℓ} (A : ℤ → Type ℓ)
    (z : A zero)
    (s : (n : ℤ) → A n → A (suc n))
    (p : (n : ℤ) → A n → A (predl n))
    (p' : (n : ℤ) → A n → A (predr n))
    (ps : (n : ℤ) → (x : A n) → PathP A (predl-suc n) (p (suc n) (s n x)) x)
    (sp' : (n : ℤ) → (x : A n) → PathP A (suc-predr n) (s (predr n) (p' n x)) x)
    (n : ℤ) → elim A z s p p' ps sp' (predl n) ≡ p n (elim A z s p p' ps sp' n)
  comp-predr : ∀ {ℓ} (A : ℤ → Type ℓ)
    (z : A zero)
    (s : (n : ℤ) → A n → A (suc n))
    (p : (n : ℤ) → A n → A (predl n))
    (p' : (n : ℤ) → A n → A (predr n))
    (ps : (n : ℤ) → (x : A n) → PathP A (predl-suc n) (p (suc n) (s n x)) x)
    (sp' : (n : ℤ) → (x : A n) → PathP A (suc-predr n) (s (predr n) (p' n x)) x)
    (n : ℤ) → elim A z s p p' ps sp' (predr n) ≡ p' n (elim A z s p p' ps sp' n)
  {-# REWRITE comp-zero comp-suc comp-predl comp-predr #-}

rec :  ∀ {ℓ} {A : Type ℓ}
       (z : A)
       (s : ℤ → A → A)
       (p : ℤ → A → A)
       (p' : ℤ → A → A)
       (ps : (n : ℤ) (x : A) → (p (suc n) (s n x)) ≡ x)
       (sp' : (n : ℤ) → (x : A) → (s (predr n) (p' n x)) ≡ x)
       (n : ℤ) → A
rec {A = A} z s p p' ps sp' n = elim (λ _ → A) z s p p' (λ n x → toConstPathP (ps n x)) (λ n x → toConstPathP (sp' n x)) n

pred = predl
pred-suc = predl-suc

one : ℤ
one = suc zero

predl≡predr : (z : ℤ) → predl z ≡ predr z
predl≡predr z = cong predl (sym (suc-predr z)) ∙ predl-suc (predr z)

suc-predl : (n : ℤ) → suc (predl n) ≡ n
suc-predl n = cong (λ n → suc (predl n)) (sym (suc-predr n)) ∙ cong suc (predl-suc _) ∙ suc-predr n

suc-pred = suc-predl

fromℕ : ℕ → ℤ
fromℕ ℕ.zero = zero
fromℕ (ℕ.suc n) = suc (fromℕ n)

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

postulate discreteℤ : Discrete ℤ
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
ℤ-isSet = Discrete→isSet discreteℤ

-- _+_ : ℤ → ℤ → ℤ
-- zero + n = n
-- suc m + n = suc (m + n)
-- predl m + n = predl (m + n)
-- predr m + n = predr (m + n)
-- predl-suc m i + n = predl-suc (m + n) i
-- suc-predr m i + n = suc-predr (m + n) i

_+_ : ℤ → ℤ → ℤ
m + n = rec {A = ℤ → ℤ}
  (λ n → n)
  (λ _ m+ n → suc (m+ n))
  (λ _ m+ n → predl (m+ n))
  (λ _ m+ n → predr (m+ n))
  (λ m m+ → funExt λ n → predl-suc (m+ n))
  (λ m m+ → funExt λ n → suc-predr (m+ n))
  m
  n

-- check that rewriting is working as expected
zero-unitl : (n : ℤ) → zero + n ≡ n
zero-unitl n = refl

-- -- opposite of an integer
-- op : ℤ → ℤ
-- op zero = zero
-- op (suc n) = pred (op n)
-- op (predl n) = suc (op n)
-- op (predr n) = suc (op n)

op : ℤ → ℤ
op = rec
  zero
  (λ _ → pred)
  (λ _ → suc)
  (λ _ → suc)
  (λ _ → suc-predl)
  (λ _ → predl-suc)

-- -- op-op : (n : ℤ) → op (op n) ≡ n
-- -- op-op zero = refl
-- -- op-op (suc n) = cong suc (op-op n)
-- -- op-op (predl n) = cong predl (op-op n)
-- -- op-op (predr n) = cong predl (op-op n) ∙ predl≡predr n
-- -- op-op (predl-suc n i) = {!!} -- op (op (predl-suc n i)) ≡ predl-suc n i
-- -- op-op (suc-predr n i) = {!!} -- op (op (suc-predr n i)) ≡ suc-predr n i

-- ---
-- --- Comparison with non-quotiented definition
-- ---

-- open import Cubical.Data.Int as Int

-- toInt : ℤ → Int
-- toInt zero = pos ℕ.zero
-- toInt (suc n) = sucInt (toInt n)
-- toInt (predl n) = predInt (toInt n)
-- toInt (predr n) = predInt (toInt n)
-- toInt (predl-suc n i) = predSuc (toInt n) i
-- toInt (suc-predr n i) = sucPred (toInt n) i

-- fromInt : Int → ℤ
-- fromInt (pos n) = fromℕ n
-- fromInt (negsuc n) = op (fromℕ (ℕ.suc n))

-- open import Cubical.Core.Everything
-- open import Cubical.Foundations.Isomorphism

-- ℤ≃Int : ℤ ≃ Int
-- ℤ≃Int = isoToEquiv (iso toInt fromInt {!!} {!!})

-- ---
-- --- Even / odd predicates
-- ---

-- -- define is-even and is-odd
-- is-parity : ℤ → Type₀ × Type₀
-- is-parity n = rec
  -- (⊤ , ⊥)
  -- (λ n p → snd p , fst p)
  -- (λ n p → snd p , fst p)
  -- (λ n p → snd p , fst p)
  -- (λ n p → refl)
  -- (λ n p → refl) n

-- is-even : ℤ → Type₀
-- is-even n = fst (is-parity n)

-- is-odd : ℤ → Type₀
-- is-odd n = snd (is-parity n)

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

-- -- is-even-zero : (e : is-even zero) → e ≡ even-zero
-- -- is-even-zero e = {!!}

-- -- TODO
-- postulate is-even-is-prop : {n : ℤ} → isProp (is-even n)
-- postulate is-odd-is-prop  : {n : ℤ} → isProp (is-odd n)
-- -- is-even-is-prop {zero} e e' = {!!}
-- -- is-even-is-prop {suc n} e e' = {!!}
-- -- is-even-is-prop {predl n} e e' = {!!}
-- -- is-even-is-prop {predr n} e e' = {!!}
-- -- is-even-is-prop {predl-suc n i} e e' = {!!}
-- -- is-even-is-prop {suc-predr n i} e e' = {!!}
-- -- is-odd-is-prop o o' = {!!}

-- postulate even-or-odd : (n : ℤ) → ¬ (is-even n × is-odd n)
-- -- even-or-odd zero (e , o) = {!!}
-- -- even-or-odd (suc n) (e , o) = {!!}
-- -- even-or-odd (predl n) (e , o) = {!!}
-- -- even-or-odd (predr n) (e , o) = {!!}
-- -- even-or-odd (predl-suc n i) (e , o) = {!!}
-- -- even-or-odd (suc-predr n i) (e , o) = {!!}

dec-parity : (n : ℤ) → Type₀
dec-parity n = is-even n ⊎ is-odd n

-- parity : (n : ℤ) → dec-parity n
-- parity zero = inl even-zero
-- parity (suc n) with parity n
-- ... | inl e = inr (odd-suc e)
-- ... | inr o = inl (even-suc o)
-- parity (predl n) with parity n
-- ... | inl e = inr (odd-predl e)
-- ... | inr o = inl (even-predl o)
-- parity (predr n) with parity n
-- ... | inl e = inr (odd-predr e)
-- ... | inr o = inl (even-predr o)
-- parity (predl-suc n i) = lem n i
  -- where
  -- --- NB: this obvious idea does not work because it does not terminate...
  -- -- lem : (n : ℤ) → PathP (λ i → dec-parity (predl-suc n i)) (parity (predl (suc n))) (parity n)
  -- -- lem n = cong parity (predl-suc n)
  -- -- TODO
  -- postulate lem : (n : ℤ) → PathP (λ i → dec-parity (predl-suc n i)) (parity (predl (suc n))) (parity n)
  -- -- lem zero = {!!}
  -- -- lem (suc n) = {!!}
  -- -- lem (predl n) = {!!}
  -- -- lem (predr n) = {!!}
  -- -- lem (predl-suc n i) = {!!}
  -- -- lem (suc-predr n i) = {!!}
  -- -- lem : (n : ℤ) →  transport (cong dec-parity (predl-suc n)) (parity (predl (suc n))) ≡ (parity n)
  -- -- lem zero = {!refl!}
  -- -- lem (suc n) = {!!}
  -- -- lem (predl n) = {!!}
  -- -- lem (predr n) = {!!}
  -- -- lem (predl-suc n i) = {!!}
  -- -- lem (suc-predr n i) = {!!}
-- parity (suc-predr n i) = lem n i
  -- where
  -- postulate lem : (n : ℤ) → PathP (λ i → dec-parity (suc-predr n i)) (parity (suc (predr n))) (parity n)

parity : (n : ℤ) → dec-parity n
parity n = elim dec-parity
  (inl even-zero)
  (λ { n (inl p) → inr (odd-suc p) ; n (inr p) → inl (even-suc p) })
  (λ { n (inl p) → inr (odd-predl p) ; n (inr p) → inl (even-predl p) })
  (λ { n (inl p) → inr (odd-predr p) ; n (inr p) → inl (even-predr p) })
  (λ { n (inl p) → {!!} ; n (inr p) → {!!} })
  {!!}
  n 

-- -- parity-rec : ∀ {ℓ} (A : ℤ → Type ℓ) → ({n : ℤ} → is-even n → A n) → ({n : ℤ} → is-odd n → A n) → (n : ℤ) → A n
-- -- parity-rec A even odd n with parity n
-- -- ... | inl e = even e
-- -- ... | inr o = odd o

open import Nat as ℕ hiding (is-even ; is-odd)

is-evenℕ : {n : ℕ} → ℕ.is-even n → is-even (fromℕ n)
is-oddℕ  : {n : ℕ} → ℕ.is-odd n → is-odd (fromℕ n)
is-evenℕ even-zero    = even-zero
is-evenℕ (even-suc p) = even-suc (is-oddℕ p)
is-oddℕ  (odd-suc p)  = odd-suc  (is-evenℕ p)
