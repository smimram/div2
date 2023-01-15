{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
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
open import Equiv
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

open import Ends

module Swapper {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom
open import Bracketing SA SB isom
open import Switch SA SB isom

---
--- Swappers
---

-- the swapping function
swapper-dchain : {o : Ends} → delements [ o ] → delements [ o ]
swapper-dchain ((inl a , d) , r) = next (inl a , d) , sym (eq/ _ _ (∥∥.map (λ { (n , r) → suc  n , cong next r }) (delement-is-reachable ((inl a , d) , r))))
swapper-dchain ((inr b , d) , r) = prev (inr b , d) , sym (eq/ _ _ (∥∥.map (λ { (n , r) → pred n , cong prev r }) (delement-is-reachable ((inr b , d) , r))))

swapper-dchain-lr : {o : Ends} (a : delements [ o ]) → in-left (arrow (fst a)) → in-right (arrow (fst (swapper-dchain a)))
swapper-dchain-lr _ (is-inl a) = is-inr _

swapper-dchain-rl : {o : Ends} (a : delements [ o ]) → in-right (arrow (fst a)) → in-left (arrow (fst (swapper-dchain a)))
swapper-dchain-rl _ (is-inr b) = is-inl _

swapper-dchain² : {o : Ends} (a : delements [ o ]) → swapper-dchain (swapper-dchain a) ≡ a
swapper-dchain² ((inl a , d) , r) = Σ≡Prop (λ _ → dChains-isSet _ _) (prev-next (inl a , d))
swapper-dchain² ((inr b , d) , r) = Σ≡Prop (λ _ → dChains-isSet _ _) (next-prev (inr b , d))

dchainA : dChains → Type ℓ
dchainA c = Σ (delements c) (in-left ∘ fst ∘ fst)

dchainB : dChains → Type ℓ
dchainB c = Σ (delements c) (in-right ∘ fst ∘ fst)

-- we have a bijection between the elements in the chain
dchain-A≃B : dChains → Type ℓ
dchain-A≃B c = dchainA c ≃ dchainB c

swapper-dchain-iso : (o : dArrows) → dchain-A≃B [ o ]
swapper-dchain-iso o = isoToEquiv i
  where
  i : Iso (dchainA [ o ]) (dchainB [ o ])
  Iso.fun i (a , l) = swapper-dchain a , swapper-dchain-lr a l
  Iso.inv i (b , r) = swapper-dchain b , swapper-dchain-rl b r
  Iso.rightInv i (b , r) = Σ≡Prop (λ _ → in-right-isProp _) (swapper-dchain² b)
  Iso.leftInv i (a , l) = Σ≡Prop (λ _ → in-left-isProp _) (swapper-dchain² a)

swapper-dchain-indep : {o o' : Ends} (r : is-reachable o o') → PathP (λ i → cong (λ c → delements c → delements c) (eq/ o o' r) i) (swapper-dchain {o = o}) (swapper-dchain {o = o'})
swapper-dchain-indep {o} {o'} r = toPathP (funExt λ {
  ((inl a , d) , r) → Σ≡Prop (λ _ → dChains-isSet _ _) (p a d) ;
  ((inr b , d) , r) → Σ≡Prop (λ _ → dChains-isSet _ _) (q b d)
  })
  where
    p = λ (a : A) (d : End) →
      transport (λ _ → Ends) (inr (fst (f (transport (λ _ → A) a , st d))) , snd (f (transport (λ _ → A) a , st d))) ≡⟨ transportRefl _ ⟩
      inr (fst (f (transport (λ _ → A) a , st d))) , snd (f (transport (λ _ → A) a , st d)) ≡⟨ ΣPathP (cong (inr {A = A} ∘ fst ∘ f) (transportRefl _) , cong (snd ∘ f) (transportRefl _)) ⟩
      inr (fst (f (a , st d))) , snd (f (a , st d)) ∎
    q = λ (b : B) (d : End) →
      transport (λ _ → Ends) (inl (fst (g (transport (λ _ → B) b , d))) , st (snd (g (transport (λ _ → B) b , d)))) ≡⟨ transportRefl _ ⟩
      inl (fst (g (transport (λ _ → B) b , d))) , st (snd (g (transport (λ _ → B) b , d))) ≡⟨ ΣPathP (cong (inl {B = B} ∘ fst ∘ g) (transportRefl _) , cong (st ∘ snd ∘ g) (transportRefl _)) ⟩
      inl (fst (g (b , d))) , st (snd (g (b , d))) ∎

-- variant of the above
swapper-dchain-indep' : {o o' : Ends} (r : is-reachable o o') → transport (λ i → cong (λ c → delements c → delements c) (eq/ o o' r) i) swapper-dchain ≡ swapper-dchain
swapper-dchain-indep' r = fromPathP (swapper-dchain-indep r)

abstract
  -- another variant
  swapper-dchain-indep'' : {o o' : Ends} (r : is-reachable o o') → subst delements (eq/ o o' r) ∘ swapper-dchain ∘ subst delements (sym (eq/ o o' r)) ≡ swapper-dchain
  swapper-dchain-indep'' {o} {o'} r = sym (fromPathP (funTypeTransp delements delements (eq/ o o' r) swapper-dchain)) ∙ swapper-dchain-indep' r

  swapper-dchain-iso-indep : {o o' : Ends} (r : is-reachable o o') → PathP (λ i → cong dchain-A≃B (eq/ o o' r) i) (swapper-dchain-iso o) (swapper-dchain-iso o')
  swapper-dchain-iso-indep r = toPathP (equivEq (funExt λ { (a , l ) → Σ≡Prop (λ _ → in-right-isProp _) (funExt⁻ (fromPathP (swapper-dchain-indep r)) a) }))

  -- variant of the above
  swapper-dchain-iso-indep' : {o o' : Ends} (r : is-reachable o o') → transport (cong dchain-A≃B (eq/ o o' r)) (swapper-dchain-iso o) ≡ (swapper-dchain-iso o')
  swapper-dchain-iso-indep' r = equivEq (funExt λ { (a , l ) → Σ≡Prop (λ _ → in-right-isProp _) (funExt⁻ (fromPathP (swapper-dchain-indep r)) a) })

  -- another variant of the above
  swapper-dchain-iso-fst-indep'' : {o o' : Ends} (r : is-reachable o o') → subst dchainB (eq/ o o' r) ∘ fst (swapper-dchain-iso o) ∘ subst dchainA (sym (eq/ o o' r)) ≡ fst (swapper-dchain-iso o')
  swapper-dchain-iso-fst-indep'' r = cong fst (swapper-dchain-iso-indep' r)

dchain→chainA : {o : Arrows} → dchainA [ fw o ] → chainA [ o ]
dchain→chainA (e , is-inl a) = delements→elements e , is-inl _

dchain→chainB : {o : Arrows} → dchainB [ fw o ] → chainB [ o ]
dchain→chainB (e , is-inr b) = delements→elements e , is-inr _

chain→dchainA : {o : Arrows} → chainA [ o ] → dchainA [ fw o ]
chain→dchainA (e , is-inl a) = elements→delements e , element-end-is-left e (is-inl _)

chain→dchainB : {o : Arrows} → chainB [ o ] → dchainB [ fw o ]
chain→dchainB (e , is-inr b) = elements→delements e , element-end-is-right e (is-inr _)

dchain≃chainA : {o : Arrows} → dchainA [ fw o ] ≃ chainA [ o ]
dchain≃chainA {o} = equivΣProp
  delements≃elements
  (λ {a} l → l)
  (λ {a} l → element-end-is-left a l)
  (λ _ → in-left-isProp _)
  (λ _ → in-left-isProp _)

dchain≃chainB : {o : Arrows} → dchainB [ fw o ] ≃ chainB [ o ]
dchain≃chainB {o} = equivΣProp
  delements≃elements
  (λ {b} r → r)
  (λ {b} r → element-end-is-right b r)
  (λ _ → in-right-isProp _)
  (λ _ → in-right-isProp _)

dchainAB≡chain : {o : Arrows} → dchain-A≃B [ fw o ] ≡ chain-A≃B [ o ]
--- NB: the following is working, but we want something more explicit to compute more easily
-- dchainAB≡chain = cong₂ _≃_ dchainA≡chain dchainB≡chain
dchainAB≡chain {o} = ua (equivBiact dchain≃chainA dchain≃chainB)

-- dchainA≡chain : {o : Arrows} → dchainA [ fw o ] ≡ chainA [ o ]
-- dchainA≡chain {o} = Σ-ap canonical-orientation p
  -- where
  -- abstract
    -- p : (a : delements [ fw o ]) → in-left (fst a) ≡ in-left (fst (transport canonical-orientation a))
    -- p a =
      -- in-left (fst a)                                   ≡⟨ sym (ua (in-left-arrow≃ (fst a))) ⟩
      -- in-left (arrow (fst a))                           ≡⟨ cong in-left (sym (transportRefl (arrow (fst a)))) ⟩
      -- in-left (fst (transport canonical-orientation a)) ∎

-- -- same as above
-- dchainB≡chain : {o : Arrows} → dchainB [ fw o ] ≡ chainB [ o ]
-- dchainB≡chain {o} = Σ-ap canonical-orientation p
  -- where
  -- abstract
    -- p = λ a → sym (ua (in-right-arrow≃ (fst a))) ∙ cong in-right (sym (transportRefl (arrow (fst a))))

-- dchainAB≡chain : {o : Arrows} → dchain-A≃B [ fw o ] ≡ chain-A≃B [ o ]
--- NB: the following is working, but we want something more explicit to compute more easily
-- dchainAB≡chain = cong₂ _≃_ dchainA≡chain dchainB≡chain

dchain-A≃B→chain-A≃B : {o : Arrows} → dchain-A≃B [ fw o ] → chain-A≃B [ o ]
dchain-A≃B→chain-A≃B {o} e = transport dchainAB≡chain e

swapper-chain-iso : (o : Arrows) → chain-A≃B [ o ]
swapper-chain-iso o = dchain-A≃B→chain-A≃B (swapper-dchain-iso (fw o))

swapper-chain-iso-fst : (o : Arrows) → fst (swapper-chain-iso o) ≡ dchain→chainB ∘ fst (swapper-dchain-iso (fw o)) ∘ chain→dchainA
swapper-chain-iso-fst o =
  fst (swapper-chain-iso o) ≡⟨ refl ⟩
  fst (transport dchainAB≡chain (swapper-dchain-iso (fw o))) ≡⟨ refl ⟩
  fst (transport (ua (equivBiact dchain≃chainA dchain≃chainB)) (swapper-dchain-iso (fw o))) ≡⟨ cong fst (uaβ (equivBiact dchain≃chainA dchain≃chainB) (swapper-dchain-iso (fw o))) ⟩
  fst (equivFun (equivBiact dchain≃chainA dchain≃chainB) (swapper-dchain-iso (fw o))) ≡⟨ refl ⟩
  fst (compEquiv (compEquiv (invEquiv dchain≃chainA) (swapper-dchain-iso (fw o))) dchain≃chainB) ≡⟨ refl ⟩
  Σfun delements→elements (λ {b} r → r) ∘ fst (compEquiv (invEquiv dchain≃chainA) (swapper-dchain-iso (fw o))) ≡⟨ refl ⟩
  Σfun delements→elements (λ {b} r → r) ∘ fst (swapper-dchain-iso (fw o)) ∘ Σfun elements→delements (λ {a} l → element-end-is-left a l) ≡⟨ cong₂-nd (λ g f → g ∘ fst (swapper-dchain-iso (fw o)) ∘ f) p q ⟩
  dchain→chainB ∘ fst (swapper-dchain-iso (fw o)) ∘ chain→dchainA ∎
    where
    p : Σfun delements→elements (λ {b} r → r) ≡ dchain→chainB
    p = funExt λ { (_ , is-inr b) → Σ≡Prop (λ _ → in-right-isProp _) refl }
    q : Σfun elements→delements (λ {a} l → element-end-is-left a l) ≡ chain→dchainA
    q = funExt λ { (_ , is-inl a) → Σ≡Prop (λ _ → in-left-isProp _) refl }

-- TODO: we need the swapper hypothesis (and use the above lemma) and the corresponding lemma on dchains
swapper-chain-iso-fst-indep : {o o' : Arrows} (r : is-reachable (fw o) (fw o')) →
                              PathP (λ i → cong (λ c → chainA c → chainB c) (eq/ _ _ (is-reachable→is-reachable-arr r)) i) (fst (swapper-chain-iso o)) (fst (swapper-chain-iso o'))
swapper-chain-iso-fst-indep {o} {o'} r = toPathP p
  where
    r' : is-reachable-arr o o'
    r' = is-reachable→is-reachable-arr r
    -- close to substCommSlice ?
    exB : subst chainB (eq/ o o' r') ∘ dchain→chainB ≡ dchain→chainB ∘ subst dchainB (eq/ (fw o) (fw o') r)
    exB = funExt (λ b → Σ≡Prop (λ _ → in-right-isProp _) (Σ≡Prop (λ _ → Chains-isSet _ _) {!!}))
      where
      p = λ (b : dchainB [ fw o ]) →
        (subst chainB (eq/ o o' r') ∘ dchain→chainB) b .fst .fst ≡⟨ {!!} ⟩

        -- fst (delements→elements {!fst (subst dchainB (eq/ (fw o) (fw o') r) b)!}) ≡⟨ refl ⟩
        (dchain→chainB ∘ subst dchainB (eq/ (fw o) (fw o') r)) b .fst .fst ∎
    exA : chain→dchainA ∘ subst chainA (sym (eq/ o o' r')) ≡ subst dchainA (sym (eq/ (fw o) (fw o') r)) ∘ chain→dchainA
    exA = {!!}
    p =
      transport (λ i → cong (λ c → chainA c → chainB c) (eq/ o o' r') i) (fst (swapper-chain-iso o)) ≡⟨ fromPathP (funTypeTransp chainA chainB (eq/ o o' r') (fst (swapper-chain-iso o))) ⟩
      subst chainB (eq/ o o' r') ∘ fst (swapper-chain-iso o) ∘ subst chainA (sym (eq/ o o' r')) ≡⟨ cong (λ f → subst chainB (eq/ o o' r') ∘ f ∘ subst chainA (sym (eq/ o o' r'))) (swapper-chain-iso-fst o) ⟩
      subst chainB (eq/ o o' r') ∘ dchain→chainB ∘ fst (swapper-dchain-iso (fw o)) ∘ chain→dchainA ∘ subst chainA (sym (eq/ o o' r')) ≡⟨ cong₂-nd (λ g f → g  ∘ fst (swapper-dchain-iso (fw o)) ∘ f) exB exA ⟩

      dchain→chainB ∘ subst dchainB (eq/ (fw o) (fw o') r) ∘ fst (swapper-dchain-iso (fw o)) ∘ subst dchainA (sym (eq/ (fw o) (fw o') r)) ∘ chain→dchainA ≡⟨ cong (λ f → dchain→chainB ∘ f ∘ chain→dchainA) (swapper-dchain-iso-fst-indep'' r) ⟩
      dchain→chainB ∘ fst (swapper-dchain-iso (fw o')) ∘ chain→dchainA ≡⟨ sym (swapper-chain-iso-fst o') ⟩
      fst (swapper-chain-iso o') ∎

-- a variant
swapper-chain-iso' : {o : Arrows} → elements [ o ] → chain-A≃B [ o ]
swapper-chain-iso' x = subst chain-A≃B (sym (element-chain x)) (swapper-chain-iso (fst x))

swapper-chain-iso'-fst : {o : Arrows} (x : elements [ o ]) → fst (swapper-chain-iso' x) ≡ subst chainB (sym (element-chain x)) ∘ fst (swapper-chain-iso (fst x)) ∘ subst chainA (element-chain x)
swapper-chain-iso'-fst x = refl

swapper-chain-iso'-indep : {o : Arrows} {a b : elements [ o ]} → is-reachable (fw (fst a)) (fw (fst b)) → swapper-chain-iso' a ≡ swapper-chain-iso' b
swapper-chain-iso'-indep {o} {a} {b} r = equivEq p
  where
  r' : is-reachable-arr (fst a) (fst b)
  r' = is-reachable→is-reachable-arr r
  oa : [ o ] ≡ [ fst a ]
  oa = element-chain a
  ob : [ o ] ≡ [ fst b ]
  ob = element-chain b
  ab : [ fst a ] ≡ [ fst b ]
  ab = eq/ _ _ r'
  p =
    swapper-chain-iso' a .fst ≡⟨ refl ⟩
    subst chain-A≃B (sym oa) (swapper-chain-iso (fst a)) .fst ≡⟨ refl ⟩
    subst chainB (sym oa) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA oa ≡⟨ cong₂-nd (λ g f → g ∘ fst (swapper-chain-iso (fst a)) ∘ f) (cong (subst chainB) (Chains-isSet _ _ (sym oa) (ab ∙ sym ob))) (cong (subst chainA) (Chains-isSet _ _ oa (ob ∙ sym ab))) ⟩
    subst chainB (ab ∙ sym ob) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (ob ∙ sym ab) ≡⟨ funExt (λ x → cong (subst chainB (ab ∙ sym ob) ∘ fst (swapper-chain-iso (fst a))) (substComposite chainA ob (sym ab) x)) ⟩
    subst chainB (ab ∙ sym ob) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (sym ab) ∘ subst chainA ob ≡⟨ funExt (λ x → substComposite chainB ab (sym ob) _) ⟩
    subst chainB (sym ob) ∘ subst chainB ab ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (sym ab) ∘ subst chainA ob ≡⟨ refl ⟩
    subst chainB (sym ob) ∘ transport (λ i → cong (λ c → chainA c → chainB c) ab i) (fst (swapper-chain-iso (fst a))) ∘ subst chainA ob ≡⟨ cong (λ f → subst chainB (sym ob) ∘ f ∘ subst chainA ob) (fromPathP (swapper-chain-iso-fst-indep r)) ⟩
    subst chainB (sym ob) ∘ fst (swapper-chain-iso (fst b)) ∘ subst chainA ob ≡⟨ refl ⟩ -- sym (fromPathP (funTypeTransp chainA chainB (sym (element-chain b)) (swapper-chain-iso (fst b) .fst)))
    subst chain-A≃B (sym ob) (swapper-chain-iso (fst b)) .fst ≡⟨ refl ⟩
    swapper-chain-iso' b .fst ∎

swapper-chain-iso'-indepo : {o o' : Arrows} (p : [ o ] ≡ [ o' ]) (a : elements [ o ]) → subst chain-A≃B p (swapper-chain-iso' a) ≡ swapper-chain-iso' (subst elements p a)
swapper-chain-iso'-indepo {o} {o'} p a = equivEq lem
  where
  a' : elements [ o' ]
  a' = subst elements p a
  fst-a' : fst a' ≡ fst a
  fst-a' = transportRefl _
  o'a' : [ o' ] ≡ [ fst a' ]
  o'a' = element-chain a'
  lem =
    subst chain-A≃B p (swapper-chain-iso' a) .fst ≡⟨ refl ⟩
    subst chainB p ∘ fst (swapper-chain-iso' a) ∘ subst chainA (sym p) ≡⟨ refl ⟩
    subst chainB p ∘ subst chainB (sym (element-chain a)) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (element-chain a) ∘ subst chainA (sym p) ≡⟨ funExt (λ x → cong (subst chainB p ∘ subst chainB (sym (element-chain a)) ∘ fst (swapper-chain-iso (fst a))) (sym (substComposite chainA (sym p) (element-chain a) x))) ⟩
    subst chainB p ∘ subst chainB (sym (element-chain a)) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (sym p ∙ element-chain a) ≡⟨ funExt (λ x → sym (substComposite chainB (sym (element-chain a)) p _)) ⟩
    subst chainB (sym (element-chain a) ∙ p) ∘ fst (swapper-chain-iso (fst a)) ∘ subst chainA (sym p ∙ element-chain a) ≡⟨ cong (λ f → subst chainB (sym (element-chain a) ∙ p) ∘ f ∘ subst chainA (sym p ∙ element-chain a)) (sym (fromPathP (cong (fst ∘ swapper-chain-iso) fst-a'))) ⟩
    subst chainB (sym (element-chain a) ∙ p) ∘ fst (transport (cong (chain-A≃B ∘ [_]) fst-a') (swapper-chain-iso (fst a'))) ∘ subst chainA (sym p ∙ element-chain a) ≡⟨ refl ⟩
    subst chainB (sym (element-chain a) ∙ p) ∘ subst chainB (cong [_] fst-a') ∘ fst (swapper-chain-iso (fst a')) ∘ subst chainA (cong [_] (sym fst-a')) ∘ subst chainA (sym p ∙ element-chain a) ≡⟨ funExt (λ x → cong (subst chainB (sym (element-chain a) ∙ p) ∘ subst chainB (cong [_] fst-a') ∘ fst (swapper-chain-iso (fst a'))) (sym (substComposite chainA _ (cong [_] (sym fst-a')) x))) ⟩
    subst chainB (sym (element-chain a) ∙ p) ∘ subst chainB (cong [_] fst-a') ∘ fst (swapper-chain-iso (fst a')) ∘ subst chainA ((sym p ∙ element-chain a) ∙ cong [_] (sym fst-a')) ≡⟨ funExt (λ x → sym (substComposite chainB (cong [_] fst-a') _ _)) ⟩
    subst chainB (cong [_] fst-a' ∙ (sym (element-chain a) ∙ p)) ∘ fst (swapper-chain-iso (fst a')) ∘ subst chainA ((sym p ∙ element-chain a) ∙ cong [_] (sym fst-a')) ≡⟨ cong₂-nd (λ q p → subst chainB q ∘ fst (swapper-chain-iso (fst a')) ∘ subst chainA p) (Chains-isSet _ _ _ _) (Chains-isSet _ _ _ _) ⟩
    subst chainB (sym o'a') ∘ fst (swapper-chain-iso (fst a')) ∘ subst chainA o'a' ≡⟨ refl ⟩
    subst chain-A≃B (sym o'a') (swapper-chain-iso (fst a')) .fst ≡⟨ refl ⟩
    swapper-chain-iso' a' .fst ∎

-- another variant
swapper-chain : {c : Chains} → elements c → chain-A≃B c
swapper-chain {c} = [].elim {P = λ c → elements c → chain-A≃B c} (λ _ → isSetΠ λ _ → chain-A≃B-isSet _) (λ _ → swapper-chain-iso') (λ o o' r → indep r) c
  where
  indep' : {o o' : Arrows} (r : is-reachable-arr o o') → transport (λ i → elements (eq/ _ _ r i) → chain-A≃B (eq/ _ _ r i)) swapper-chain-iso' ≡ swapper-chain-iso'
  indep' {o} {o'} r = funExt (λ x → equivEq (p x))
    where
    p = λ (x : elements [ o' ]) →
      let oo' : [ o ] ≡ [ o' ]
          oo' = eq/ o o' r
          sidB =
            subst chainB oo' ∘ subst chainB (sym oo') ≡⟨ funExt (λ x → sym (substComposite chainB (sym oo') oo' x)) ⟩
            subst chainB (sym oo' ∙ oo') ≡⟨ cong (subst chainB) (lCancel oo') ⟩
            subst chainB refl ≡⟨ funExt (substRefl {B = chainB}) ⟩
            idfun (chainB [ o' ]) ∎
          sidA =
            subst chainA oo' ∘ subst chainA (sym oo') ≡⟨ funExt (λ x → sym (substComposite chainA (sym oo') oo' x)) ⟩
            subst chainA (sym oo' ∙ oo') ≡⟨ cong (subst chainA) (lCancel oo') ⟩
            subst chainA refl ≡⟨ funExt (substRefl {B = chainA}) ⟩
            idfun (chainA [ o' ]) ∎
      in
      transport (λ i → elements (oo' i) → chain-A≃B (oo' i)) (swapper-chain-iso' {o = o}) x .fst ≡⟨ refl ⟩
      (subst chain-A≃B oo' ∘ swapper-chain-iso' ∘ subst elements (sym oo')) x .fst ≡⟨ refl ⟩
      subst chainB oo' ∘ fst (swapper-chain-iso' (subst elements (sym oo') x)) ∘ subst chainA (sym oo') ≡⟨ cong (λ x → subst chainB oo' ∘ fst x ∘ subst chainA (sym oo')) (sym (swapper-chain-iso'-indepo (sym oo') x)) ⟩
      subst chainB oo' ∘ fst (subst chain-A≃B (sym oo') (swapper-chain-iso' x)) ∘ subst chainA (sym oo') ≡⟨ refl ⟩
      subst chainB oo' ∘ subst chainB (sym oo') ∘ fst (swapper-chain-iso' x) ∘ subst chainA oo' ∘ subst chainA (sym oo') ≡⟨ cong₂-nd (λ g f → g ∘ fst (swapper-chain-iso' x) ∘ f) sidB sidA ⟩
      swapper-chain-iso' {o = o'} x .fst ∎
  indep : {o o' : Arrows} (r : is-reachable-arr o o') → PathP (λ i → elements (eq/ _ _ r i) → chain-A≃B (eq/ _ _ r i)) swapper-chain-iso' swapper-chain-iso'
  indep r = toPathP (indep' r)

-- if we have a slope any element will do for the swapper
slope-swapper : {c : Chains} → slope-chain c → chain-A≃B c
slope-swapper {c} = [].elim
  {B = λ c → slope-chain c → chain-A≃B c}
  (λ c → isSetΠ (λ _ → chain-A≃B-isSet c))
  (λ o sl → {!equiv (fst sl) (snd sl)!})
  (λ a b r → {!equiv-indep r!})
  c
  where

  -- reindex the nth iteration from o according to (fw o)
  iterate-fw : ℤ → (o : Ends) → elements [ fst o ]
  iterate-fw n (o , src) = arrow (iterate n (fw o)) , sym (eq/ _ _ ∣ n , refl ∣₁)
  iterate-fw n (o , tgt) = arrow (iterate (ℤ.neg n) (fw o)) , sym (eq/ _ _ ∣ ℤ.neg n , refl ∣₁)

  iterate-fw-neg : (n : ℤ) (o : Ends) → iterate-fw (ℤ.neg n) o ≡ iterate-fw n (op o)
  iterate-fw-neg n (o , src) = refl
  iterate-fw-neg n (o , tgt) = cong (λ n → iterate-fw n (o , src)) (ℤ.neg-neg n)

  iterate-fw-reachable-arr-fw : {o : Ends} (n n' : ℤ) → reachable (fw (arrow (iterate n o))) (fw (arrow (iterate n' o))) → reachable (fw (fst (iterate-fw n o))) (fw (fst (iterate-fw n' o)))
  iterate-fw-reachable-arr-fw {o , src} n n' r = r
  iterate-fw-reachable-arr-fw {o , tgt} n n' r = transport lem' r
    where
    abstract
      lem : (n : ℤ) → arrow (iterate n (o , tgt)) ≡ arrow (iterate (ℤ.neg n) (o , src))
      lem n = cong arrow (iterate-op n (o , src))
      lem' : reachable (fw (arrow (iterate n (o , tgt)))) (fw (arrow (iterate n' (o , tgt)))) ≡ reachable (fw (fst (iterate (ℤ.neg n) (o , src)))) (fw (fst (iterate (ℤ.neg n') (o , src))))
      lem' = cong₂-nd reachable (cong fw (lem n)) (cong fw (lem n'))

  -- NB: we take o as origin for non matched but fw (fst o) as reference for
  -- the chain (even if o is oriented backwards...)
  equiv' : {o : Ends} → non-matched o → chain-A≃B [ fst o ]
  equiv' {o} (n , nm) = swapper-chain-iso' (iterate-fw n o)
  equiv'-indep : {o : Ends} (seq : sequential o) (nm nm' : non-matched o) → equiv' nm ≡ equiv' nm'
  equiv'-indep {o} seq (n , ¬m) (n' , ¬m') = equivEq (
    equiv' (n , ¬m) .fst ≡⟨ refl ⟩
    fst (swapper-chain-iso' xa) ≡⟨ cong fst (swapper-chain-iso'-indep ∣ iterate-fw-reachable-arr-fw n n' rsxy ∣₁) ⟩
    
    fst (swapper-chain-iso' ya) ≡⟨ refl ⟩
    equiv' (n' , ¬m') .fst ∎)
    where
    x = iterate n o
    y = iterate n' o
    xa : elements [ fst o ]
    xa = iterate-fw n o
    ya : elements [ fst o ]
    ya = iterate-fw n' o
    end-xy : end x ≡ end y
    end-xy = seq n n' ¬m ¬m'
    rxy : reachable x y
    rxy = reachable-trans (reachable-sym (n , refl)) (n' , refl)
    -- TODO: simplify with iterate-fw-reachable-arr-fw above
    rsxy : reachable (fw (arrow x)) (fw (arrow y))
    rsxy = {!!} -- TODO: by rxy and end-xy and cas analysis on the common end

  -- equiv' does not depend on the orientation of the origin
  equiv'-indep-op : {o : Ends} (nm : non-matched (op o)) → equiv' {o = o} (transport (non-matched-op _) nm) ≡ equiv' {o = op o} nm
  equiv'-indep-op {o} (n , m) = equivEq p
    where
    p =
      equiv' (transport (non-matched-op o) (n , m)) .fst                 ≡⟨ refl ⟩
      equiv' (ℤ.neg n , snd (transport (non-matched-op o) (n , m))) .fst ≡⟨ refl ⟩
      swapper-chain-iso' (iterate-fw (ℤ.neg n) o) .fst                   ≡⟨ cong (fst ∘ swapper-chain-iso') (iterate-fw-neg n o) ⟩
      swapper-chain-iso' (iterate-fw n (op o)) .fst                      ≡⟨ refl ⟩
      equiv' (n , m) .fst                                                ∎

  equiv'-indepo : {o o' : Arrows} {d d' : End} (r : reachable (o , d) (o' , d')) (nm : non-matched (o' , d')) →
                  subst chain-A≃B (sym (eq/ _ _ ∣ reachable→reachable-arr r ∣₁)) (equiv' nm) ≡ equiv' (non-matched-indep r nm)
  equiv'-indepo {o} {o'} {d} {d'} r nm = equivEq p
    where
    o→ : Ends
    o→ = o , d
    o'→ : Ends
    o'→ = o' , d'
    n : ℤ
    n = fst nm
    m : ¬ (matched (arrow (iterate n o'→)))
    m = snd nm
    o'o : [ o' ] ≡ [ o ]
    o'o = sym (eq/ o o' ∣ reachable→reachable-arr r ∣₁)
    a : elements [ o ]
    a = iterate-fw (fst r ℤ.+ n) o→
    a' : elements [ o' ]
    a' = iterate-fw n o'→
    p =
      subst chain-A≃B o'o (equiv' nm) .fst                                      ≡⟨ refl ⟩
      subst chainB o'o ∘ fst (equiv' nm) ∘ subst chainA (sym o'o)               ≡⟨ refl ⟩
      subst chainB o'o ∘ fst (swapper-chain-iso' a') ∘ subst chainA (sym o'o)   ≡⟨ cong fst (swapper-chain-iso'-indepo o'o a') ⟩
      swapper-chain-iso' (subst elements o'o a') .fst                           ≡⟨ cong (λ a → swapper-chain-iso' a .fst) so'oa' ⟩
      swapper-chain-iso' (iterate-fw (fst r ℤ.+ n) o→) .fst                  ≡⟨ refl ⟩
      swapper-chain-iso' (iterate-fw (fst (non-matched-indep r nm)) o→) .fst ≡⟨ refl ⟩
      equiv' (non-matched-indep {a = o→} {b = o'→} r nm) .fst                   ∎
        where
        so'oa' : subst elements o'o a' ≡ a
        so'oa' = Σ≡Prop (λ _ → Chains-isSet _ _) (
          subst elements o'o a' .fst ≡⟨ refl ⟩
          transport (λ _ → Arrows) (fst (iterate-fw n (o' , d'))) ≡⟨ transportRefl _ ⟩
          fst (iterate-fw n (o' , d'))                            ≡⟨ cong (fst ∘ iterate-fw n) (sym (snd r)) ⟩
          fst (iterate-fw n (iterate (fst r) (o , d)))            ≡⟨ iterate-fw-iterate-fst (fst r) n (o , d) ⟩
          fst (iterate-fw (fst r ℤ.+ n) (o , d))                  ≡⟨ refl ⟩
          a .fst                                                     ∎
          )
          where
          iterate-fw-iterate-fst : (m n : ℤ) (o : Ends) →
                                      fst (iterate-fw n (iterate m o)) ≡ fst (iterate-fw (m ℤ.+ n) o)
          iterate-fw-iterate-fst m n o = lem _ _ _ _ refl
            where
            lem : (o o' : Arrows) (d d' : End) → (o' , d') ≡ iterate m (o , d) → fst (iterate-fw n (o' , d')) ≡ fst (iterate-fw (m ℤ.+ n) (o , d))
            lem o o' src src p = cong fst (cong (iterate n) p ∙ iterate-+ m n (o , src))
            lem o o' src tgt p =
              fst (iterate (ℤ.neg n) (o' , src))                 ≡⟨ cong (fst ∘ (iterate (ℤ.neg n))) (cong op p) ⟩
              fst (iterate (ℤ.neg n) (op (iterate m (o , src)))) ≡⟨ cong fst (iterate-neg-op n (iterate m (o , src))) ⟩
              fst (op (iterate n (iterate m (o , src))))         ≡⟨ refl ⟩
              fst (iterate n (iterate m (o , src)))              ≡⟨ cong fst (iterate-+ m n (o , src)) ⟩
              fst (iterate (m ℤ.+ n) (o , src))                  ∎
            lem o o' tgt src p =
              fst (iterate n (o' , src))                  ≡⟨ cong (fst ∘ iterate n) p ⟩
              fst (iterate n (iterate m (o , tgt)))       ≡⟨ cong fst (iterate-+ m n (o , tgt)) ⟩
              fst (iterate (m ℤ.+ n) (o , tgt))           ≡⟨ refl ⟩
              fst (op (iterate (m ℤ.+ n) (op (o , src)))) ≡⟨ sym (cong fst (iterate-neg (m ℤ.+ n) (o , src))) ⟩
              fst (iterate (ℤ.neg (m ℤ.+ n)) (o , src))   ∎
            lem o o' tgt tgt p =
              fst (iterate (ℤ.neg n) (o' , src))                 ≡⟨ cong (fst ∘ iterate (ℤ.neg n)) (cong op p) ⟩
              fst (iterate (ℤ.neg n) (op (iterate m (o , tgt)))) ≡⟨ cong fst (iterate-neg-op n (iterate m (o , tgt))) ⟩
              fst (iterate n (iterate m (o , tgt)))              ≡⟨ cong fst (iterate-+ m n (o , tgt)) ⟩
              fst (iterate (m ℤ.+ n) (o , tgt))                  ≡⟨ refl ⟩
              fst (op (iterate (m ℤ.+ n) (o , tgt)))             ≡⟨ cong fst (sym (iterate-neg-op (m ℤ.+ n) (o , tgt))) ⟩
              fst (iterate (ℤ.neg (m ℤ.+ n)) (o , src))          ∎

  -- small variant/generalization of the above
  equiv'-indepo' : {o o' : Ends} {oo' : [ fst o ] ≡ [ fst o' ]} (r : reachable o o') (nm : non-matched o') →
                   subst chain-A≃B oo' (equiv' (non-matched-indep r nm)) ≡ equiv' nm
  equiv'-indepo' {o} {o'} {oo'} r nm = equivEq p
    where
    o'o : [ arrow o' ] ≡ [ arrow o ]
    o'o = eq/ _ _ ∣ reachable→reachable-arr (reachable-sym r) ∣₁
    p =
      subst chain-A≃B oo' (equiv' (non-matched-indep r nm)) .fst                     ≡⟨ cong (λ oo' → subst chain-A≃B oo' (equiv' (non-matched-indep r nm)) .fst) (Chains-isSet _ _ _ _) ⟩
      subst chain-A≃B (sym o'o) (equiv' (non-matched-indep r nm)) .fst               ≡⟨ cong fst (equiv'-indepo (reachable-sym r) (non-matched-indep r nm)) ⟩
      equiv' (non-matched-indep (reachable-sym r) (non-matched-indep r nm)) .fst ≡⟨ cong (fst ∘ equiv') (non-matched-indep² r nm) ⟩
      equiv' nm .fst ∎

  equiv : {o : Ends} → sequential o → is-non-matched o → chain-A≃B [ fst o ]
  equiv {o} seq nm = ∥∥-elim
    (chain-A≃B-isSet [ fst o ])
    equiv'
    (indep seq)
    nm
    where
    indep : {o : Ends} (seq : sequential o) (nm nm' : non-matched o) → equiv' nm ≡ equiv' nm'
    indep seq nm nm' = equiv'-indep seq nm nm'

  equiv-indep : {o o' : Arrows} (r : is-reachable-arr o o') →
                PathP (λ i → slope-chain (eq/ o o' r i) → chain-A≃B (eq/ o o' r i)) (λ sl → equiv (fst sl) (snd sl)) (λ sl → equiv (fst sl) (snd sl))
  equiv-indep {o} {o'} r = toPathP (funExt λ { (seq , nm) → equivEq _ _ {!equiv-indep1 seq nm!} })
    where
    oo' : [ o ] ≡ [ o' ]
    oo' = eq/ o o' r
    equiv-indep1 : (seq : sequential (fw o')) (nm : is-non-matched (fw o')) → subst chain-A≃B oo' (equiv (subst sequential-chain (sym oo') seq) (subst non-matched-chain (sym oo') nm)) .fst ≡ equiv seq nm .fst
    equiv-indep1 seq nm = ∥∥-elim
      (isProp→isSet (isSetΠ (λ _ → chainB-isSet _) _ _))
      (λ nm → p' nm)
      (λ _ _ → isSetΠ (λ _ → chainB-isSet _) _ _ _ _)
      nm
      where
      p : (nm : non-matched (fw o')) →
          subst chain-A≃B oo' (equiv (subst sequential-chain (sym oo') seq) (subst non-matched-chain (sym oo') ∣ nm ∣₁)) .fst ≡ equiv seq ∣ nm ∣₁ .fst
      -- p nm with reachable-arr→reachable (reachable-arr-reveal r)
      -- ... | inl r' = ?
      -- ... | inr r' = ?
      p nm =
        let seq' : sequential-chain [ o ]
            seq' = subst sequential-chain (sym oo') seq
            nm' : non-matched-chain [ o ]
            nm' = subst non-matched-chain (sym oo') ∣ nm ∣₁
        in
        --- NB: we need to to case here because pattern matching makes agda loop
        case reachable-arr→reachable (reachable-arr-reveal r) of λ {
          (inl r') →
            let nmo : non-matched (fw o)
                nmo = non-matched-indep r' nm
            in
            subst chain-A≃B oo' (equiv seq' nm') .fst     ≡⟨ cong (fst ∘ subst chain-A≃B oo' ∘ equiv seq') (non-matched-chain-isProp [ o ] nm' ∣ nmo ∣₁) ⟩
            subst chain-A≃B oo' (equiv seq' ∣ nmo ∣₁) .fst ≡⟨ refl ⟩
            subst chain-A≃B oo' (equiv' nmo) .fst         ≡⟨ cong fst (equiv'-indepo' r' nm) ⟩
            equiv' nm .fst                                ≡⟨ refl ⟩
            equiv seq ∣ nm ∣₁ .fst                         ∎
            ;
          (inr r') →
            let nmo : non-matched (fw o)
                nmo = non-matched-indep r' (transport (non-matched-op _) nm)
            in
            subst chain-A≃B oo' (equiv seq' nm') .fst     ≡⟨ cong (fst ∘ subst chain-A≃B oo' ∘ equiv seq') (non-matched-chain-isProp [ o ] nm' ∣ nmo ∣₁) ⟩
            subst chain-A≃B oo' (equiv seq' ∣ nmo ∣₁) .fst ≡⟨ refl ⟩
            subst chain-A≃B oo' (equiv' nmo ) .fst        ≡⟨ cong fst (equiv'-indepo' r' (transport (non-matched-op _) nm)) ⟩
            equiv' (transport (non-matched-op _) nm) .fst ≡⟨ cong fst (equiv'-indep-op nm) ⟩
            equiv' nm .fst                                ≡⟨ refl ⟩
            equiv seq ∣ nm ∣₁ .fst                        ∎
          }
      -- we need to transport along nm = ∣ nm' |, which holds since these are propositions
      p' : (nm' : non-matched (fw o')) →
           subst chain-A≃B oo' (equiv (subst sequential-chain (sym oo') seq) (subst non-matched-chain (sym oo') nm)) .fst ≡ equiv seq nm .fst
      p' nm' = {!cong (λ nm → subst chain-A≃B oo' (equiv (subst sequential-chain (sym oo') seq) (subst non-matched-chain (sym oo') nm)) .fst) ?!} ∙ p nm' ∙ {!!}
