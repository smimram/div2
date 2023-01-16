{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
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
open import Partition
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

open import Ends

module Div2Reach {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom
open import Bracketing SA SB isom
open import Switch SA SB isom
open import Swapper SA SB isom
open import Tricho SA SB isom
open import Div2 SA SB isom

reachable-chain-A≃B : {c : Chains} (e : chain-A≃B c) → Type _
reachable-chain-A≃B {c} e = (a : chainA c) → reachable-arr (inl (chainA→A a)) (inr (chainB→B (equivFun e a)))

wb-reachable : {c : Chains} (wbc : well-bracketed-chain c) → reachable-chain-A≃B (matching-equiv {c} wbc)
wb-reachable {c} wbc = [].elim
  {P = λ c → (wbc : well-bracketed-chain c) → reachable-chain-A≃B {c} (matching-equiv wbc)}
  (λ _ → isSetΠ λ _ → isSetΠ λ _ → reachable-arr-isSet _ _)
  reachable'
  (λ o o' r → {!!}) -- independence of the origin
  c wbc
  where
  reachable' : (o : Arrows) (wbc : well-bracketed o) → (a : chainA [ o ]) → reachable-arr (inl (chainA→A a)) (inr (chainB→B (equivFun (matching-equiv wbc) a)))
  reachable' o wbc (a , l) = subst₂ reachable-arr (sym a≡) (sym b≡) ans
    where
    a≡ : inl (chainA→A (a , l)) ≡ fst a
    a≡ = inl-get-left l
    m : matched (fst a)
    m = wb-reachable-arr-matched wbc (element-is-reachable-arr a)   
    b≡' : chainB→B (equivFun (matching-equiv wbc) (a , l)) ≡ get-right (match-lr m l)
    b≡' = refl
    b≡ : inr (chainB→B (equivFun (matching-equiv wbc) (a , l))) ≡ match m
    b≡ = inr-get-right (match-lr m l)
    ans : reachable-arr (fst a) (match m)
    ans = match-reachable-arr m

sw-reachable : {c : Chains} (swc : switched-chain c) → reachable-chain-A≃B (swapper-chain (switched-element c swc))
sw-reachable {c} swc = [].elim
  {P = λ c → (swc : switched-chain c) → reachable-chain-A≃B (swapper-chain (switched-element c swc))}
  (λ _ → isSetΠ λ _ → isSetΠ λ _ → reachable-arr-isSet _ _)
  reachable'
  {!!}
  c swc
  where
  -- reachable' : (o : Arrows) (swc : switched-chain [ o ]) → reachable-chain-A≃B (swapper-chain (switched-element [ o ] swc))
  reachable' : (o : Arrows) (swc : switched-chain [ o ]) → (a : chainA [ o ]) → reachable-arr (inl (chainA→A a)) (inr (chainB→B (equivFun (swapper-chain (switched-element [ o ] swc)) a)))
  reachable' o swc (a , l) = {!!}
    where
    a≡ : inl (chainA→A (a , l)) ≡ fst a
    a≡ = inl-get-left l
    se : elements [ o ]
    se = switched-element [ o ] swc
    -- t =
      -- chainB→B (equivFun (swapper-chain se) (a , l)) ≡⟨ refl ⟩
      -- chainB→B (equivFun (swapper-chain-iso' se) (a , l)) ≡⟨ refl ⟩
      -- chainB→B ((subst chainB (sym (element-chain se)) ∘ fst (swapper-chain-iso (fst se)) ∘ subst chainA (element-chain se)) (a , l)) ≡⟨ {!!} ⟩
      -- {!!} ∎
    b≡' : chainB→B (equivFun (swapper-chain se) (a , l)) ≡ {!!}
    b≡' = {!!}
    b≡ : inr (chainB→B (equivFun (swapper-chain se) (a , l))) ≡ fst (fst (swapper-dchain (elements→delements se)))
    b≡ = {!!}
    ans : reachable-arr (fst a) (fst (fst (swapper-dchain (elements→delements se))))
    ans = {!!}

sl-reachable : {c : Chains} (slc : slope-chain c) → reachable-chain-A≃B (slope-swapper {c} slc)
sl-reachable {c} slc = [].elim
  {P = λ c → (slc : slope-chain c) → reachable-chain-A≃B (slope-swapper {c} slc)}
  (λ _ → isSetΠ λ _ → isSetΠ λ _ → reachable-arr-isSet _ _)
  reachable'
  {!!} -- independence of the origin
  c slc
  where
  reachable' : (o : Arrows) (slc : slope-chain [ o ]) → (a : chainA [ o ]) → reachable-arr (inl (chainA→A a)) (inr (chainB→B (equivFun (slope-swapper slc) a)))
  reachable' = {!!}

Conway-chain-reachable : (c : Chains) → reachable-chain-A≃B (Conway-chain c)
Conway-chain-reachable c with tricho c
... | Tricho.wb t = wb-reachable t
... | Tricho.sw t = sw-reachable t
... | Tricho.sl t = sl-reachable t

ConwayFun : A → B
ConwayFun = equivFun Conway

ConwayFun-def : (a : A) →
                ConwayFun a ≡ chainB→B (equivFun (Conway-chain [ inl a ]) ((inl a , refl) , subst in-left (sym (secEq (invEquiv (partition is-reachable-arr)) (inl a))) (is-inl a)))
ConwayFun-def a = refl

Conway-reachable : (a : A) → reachable-arr (inl a) (inr (ConwayFun a))
Conway-reachable a = r'
  where
  Conway-chain-reachable' : (c : Chains) → (a : chainA c) → reachable-arr (inl (chainA→A a)) (inr (chainB→B (equivFun (Conway-chain c) a)))
  Conway-chain-reachable' = Conway-chain-reachable
  ca : chainA [ inl a ]
  ca = (inl a , refl) , is-inl a
  ca' : chainA [ inl a ]
  ca' = (inl a , refl) , subst in-left (sym (secEq (invEquiv (partition is-reachable-arr)) (inl a))) (is-inl a)
  ca≡ca' : ca ≡ ca'
  ca≡ca' = Σ≡Prop (λ _ → in-left-isProp _) refl
  r : reachable-arr (inl (chainA→A ca)) (inr (chainB→B (equivFun (Conway-chain [ inl a ]) ca)))
  r = Conway-chain-reachable' [ inl a ] ca
  r' : reachable-arr (inl (chainA→A ca)) (inr (chainB→B (equivFun (Conway-chain [ inl a ]) ca')))
  r' = subst (λ ca' → reachable-arr (inl (chainA→A ca)) (inr (chainB→B (equivFun (Conway-chain [ inl a ]) ca')))) ca≡ca' r
