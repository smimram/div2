{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma public

-- abstract
  -- -- an easy lemma, proved in an inelegant way
  -- ×≃ : {ℓ ℓ' : Level} {A A' : Type ℓ} {B B' : Type ℓ'} → A ≃ A' → B ≃ B' → A × B ≃ A' × B'
  -- ×≃ {ℓ} {ℓ'} {A} {A'} {B} {B'} eA eB = isoToEquiv i
    -- where
    -- iA : Iso A A'
    -- iA = equivToIso eA
    -- iB : Iso B B'
    -- iB = equivToIso eB
    -- i : Iso (A × B) (A' × B')
    -- Iso.fun i (a , b) = Iso.fun iA a , Iso.fun iB b
    -- Iso.inv i (a' , b') = Iso.inv iA a' , Iso.inv iB b'
    -- Iso.rightInv i (a' , b') = ΣPathP (Iso.rightInv iA a' , Iso.rightInv iB b')
    -- Iso.leftInv i (a , b) = ΣPathP (Iso.leftInv iA a , Iso.leftInv iB b)

×≡ : {ℓ ℓ' : Level} {A A' : Type ℓ} {B B' : Type ℓ'} → A ≡ A' → B ≡ B' → A × B ≡ A' × B'
×≡ p q i = p i × q i

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B : A → Type ℓ'

-- taken from more recent version of the library...

module _ {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
  {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)} where
  PathPΣ : PathP (λ i → Σ (A i) (B i)) x y
         → Σ[ p ∈ PathP A (fst x) (fst y) ] PathP (λ i → B i (p i)) (snd x) (snd y)
  PathPΣ eq = (λ i → fst (eq i)) , (λ i → snd (eq i))

  module PathPΣ (p : PathP (λ i → Σ (A i) (B i)) x y) where
    open Σ (PathPΣ p) public

Σ-cong-equiv-fst : (e : A ≃ A') → Σ A (B ∘ equivFun e) ≃ Σ A' B
-- we could just do this:
-- Σ-cong-equiv-fst e = isoToEquiv (Σ-cong-iso-fst (equivToIso e))
-- but the following reduces slightly better
Σ-cong-equiv-fst {A = A} {A' = A'} {B = B} e = intro , isEqIntro
 where
  intro : Σ A (B ∘ equivFun e) → Σ A' B
  intro (a , b) = equivFun e a , b
  isEqIntro : isEquiv intro
  isEqIntro .equiv-proof x = ctr , isCtr where
    PB : ∀ {x y} → x ≡ y → B x → B y → Type _
    PB p = PathP (λ i → B (p i))

    open Σ x renaming (fst to a'; snd to b)
    open Σ (equivCtr e a') renaming (fst to ctrA; snd to α)
    ctrB : B (equivFun e ctrA)
    ctrB = subst B (sym α) b
    ctrP : PB α ctrB b
    ctrP = symP (transport-filler (λ i → B (sym α i)) b)
    ctr : fiber intro x
    ctr = (ctrA , ctrB) , ΣPathP (α , ctrP)

    isCtr : ∀ y → ctr ≡ y
    isCtr ((r , s) , p) = λ i → (a≡r i , b!≡s i) , ΣPathP (α≡ρ i , coh i) where
      open PathPΣ p renaming (fst to ρ; snd to σ)
      open PathPΣ (equivCtrPath e a' (r , ρ)) renaming (fst to a≡r; snd to α≡ρ)

      b!≡s : PB (cong (equivFun e) a≡r) ctrB s
      b!≡s i = comp (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) b

      coh : PathP (λ i → PB (α≡ρ i) (b!≡s i) b) ctrP σ
      coh i j = fill (λ k → B (α≡ρ i (~ k))) (λ k → (λ
        { (i = i0) → ctrP (~ k)
        ; (i = i1) → σ (~ k)
        })) (inS b) (~ j)
