{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Ends

module Arrows {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : Iso (A × End) (B × End)) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Binary
open BinaryRelation using (isEquivRel)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Z as ℤ
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order
open import Nat as ℕ
open import Misc
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

f : A × End → B × End
f = Iso.fun isom

g : B × End → A × End
g = Iso.inv isom

g-f : (x : A × End) → g (f x) ≡ x
g-f = Iso.leftInv isom

f-g : (x : B × End) → f (g x) ≡ x
f-g = Iso.rightInv isom

Arrows : Type ℓ
Arrows = A ⊎ B

Arrows-isSet : isSet Arrows
Arrows-isSet = isSet⊎ SA SB

-- this is only used for discreteness of A and B
open import Classical

A-discrete : Discrete A
A-discrete x y with LEM (SA x y)
... | inl x≡y = yes x≡y
... | inr x≢y = no  x≢y

B-discrete : Discrete B
B-discrete x y with LEM (SB x y)
... | inl x≡y = yes x≡y
... | inr x≢y = no  x≢y

Arrows-discrete : Discrete Arrows
Arrows-discrete = Discrete⊎ A-discrete B-discrete

Ends : Type ℓ
Ends = Arrows × End

-- an end seen as a directed arrow
dArrows = Ends

Ends-isSet : isSet Ends
Ends-isSet = isSet× Arrows-isSet End-isSet

End-discrete : Discrete End
End-discrete src src = yes refl
End-discrete src tgt = no (λ p → subst (λ { src → ⊤ ; tgt → ⊥ }) p tt)
End-discrete tgt src = no (λ p → subst (λ { src → ⊥ ; tgt → ⊤ }) p tt)
End-discrete tgt tgt = yes refl

Ends-discrete : Discrete Ends
Ends-discrete = Discrete× Arrows-discrete End-discrete

arrow : dArrows → Arrows
arrow = fst

end : dArrows → End
end = snd

end≡ : {e e' : Ends} → arrow e ≡ arrow e' → end e ≡ end e' → e ≡ e'
end≡ p q = ΣPathP (p , q)

-- the other end of an arrow
op : dArrows → dArrows
op (a , e) = a , st e

-- end-op : (a : Ends) → end (op a) ≡ st (end a)
-- end-op _ = refl

op-op : (e : dArrows) → op (op e) ≡ e
op-op e = end≡ refl (st² (end e))

op≢ : (e : dArrows) → ¬ (op e ≡ e)
op≢ (a , src) p = src≢tgt (sym (cong end p))
op≢ (a , tgt) p = src≢tgt (cong end p)

arrow-op : (x : dArrows) → arrow (op x) ≡ arrow x
arrow-op x = refl

orient : Arrows → End → dArrows
orient a e = (a , e)

-- make the arrow point in the → direction (we begin from the source)
fw : Arrows → dArrows
fw a = orient a src

-- make the arrow point in the ← direction (we begin from the end)
bw : Arrows → dArrows
bw a = orient a tgt

-- next arrow: we always suppose that we are at the beginning of an arrow
next : dArrows → dArrows
next (inl a , d) = inr (fst (f (a , st d))) , snd (f (a , st d))
next (inr b , d) = inl (fst (g (b , st d))) , snd (g (b , st d))

prev : dArrows → dArrows
prev (inl a , d) = inr (fst (f (a , d))) , st (snd (f (a , d)))
prev (inr b , d) = inl (fst (g (b , d))) , st (snd (g (b , d)))

next-prev : (x : dArrows) → next (prev x) ≡ x
next-prev (inl a , d) = end≡ p q
  where
    p =
      inl (fst (g (fst (f (a , d)) , st (st (snd (f (a , d))))))) ≡⟨ cong (inl ∘ fst ∘ g) (ΣPathP (refl , st² (snd (f (a , d))))) ⟩
      inl (fst (g (fst (f (a , d)) , snd (f (a , d))))) ≡⟨ cong (inl ∘ fst) (g-f (a , d)) ⟩
      inl a ∎
    q =
      snd (g (fst (f (a , d)) , st (st (snd (f (a , d)))))) ≡⟨ cong (snd ∘ g) (ΣPathP (refl , (st² _))) ⟩
      snd (g (fst (f (a , d)) , snd (f (a , d)))) ≡⟨ cong snd (g-f (a , d)) ⟩
      d ∎
next-prev (inr b , d) = end≡ p q
  where
    p =
      inr (fst (f (fst (g (b , d)) , st (st (snd (g (b , d))))))) ≡⟨ cong (inr ∘ fst ∘ f) (ΣPathP (refl , (st² _))) ⟩
      inr (fst (f (fst (g (b , d)) , snd (g (b , d))))) ≡⟨ cong (inr ∘ fst) (f-g _) ⟩
      inr b ∎
    q =
      snd (f (fst (g (b , d)) , st (st (snd (g (b , d)))))) ≡⟨ cong (snd ∘ f) (ΣPathP (refl , (st² _))) ⟩
      snd (f (fst (g (b , d)) , snd (g (b , d)))) ≡⟨ cong snd (f-g _) ⟩
      d ∎

prev-next : (x : dArrows) → prev (next x) ≡ x
prev-next (inl a , d) = end≡ (cong (inl ∘ fst) (g-f (a , st d))) (cong (st ∘ snd) (g-f (a , st d)) ∙ st² d)
prev-next (inr b , d) = end≡ (cong (inr ∘ fst) (f-g (b , st d))) (cong (st ∘ snd) (f-g (b , st d)) ∙ st² d)

cong-prev-next : {x y : dArrows} (p : x ≡ y) → PathP (λ i → prev-next x i ≡ prev-next y i) (cong prev (cong next p)) p
cong-prev-next p = toPathP (Ends-isSet _ _ _ _)

cong-next-prev : {x y : dArrows} (p : x ≡ y) → PathP (λ i → next-prev x i ≡ next-prev y i) (cong next (cong prev p)) p
cong-next-prev p = toPathP (Ends-isSet _ _ _ _)

next-op : (x : dArrows) → next (op x) ≡ op (prev x)
next-op (inl a , d) = end≡ p q
  where
  p =
    inr (fst (f (a , st (st d))))                             ≡⟨ cong (inr ∘ fst ∘ f) (ΣPathP (refl , st² d)) ⟩
    inr (fst (f (a , d)))                                     ≡⟨ refl ⟩
    arrow (inr (fst (f (a , d))) , snd (f (a , d)))           ≡⟨ cong arrow (ΣPathP (refl , (sym (st² (snd (f (a , d))))))) ⟩
    arrow (inr (fst (f (a , d))) , st (st (snd (f (a , d))))) ∎
  q =
    snd (f (a , st (st d)))   ≡⟨ cong (snd ∘ f) (ΣPathP (refl , (st² d))) ⟩
    snd (f (a , d))           ≡⟨ sym (st² _) ⟩
    st (st (snd (f (a , d)))) ∎
next-op (inr b , d) = end≡ p q
  where
  p =
    inl (fst (g (b , st (st d))))                             ≡⟨ cong (inl ∘ fst ∘ g) (ΣPathP (refl , st² d)) ⟩
    inl (fst (g (b , d)))                                     ≡⟨ refl ⟩
    arrow (inl (fst (g (b , d))) , snd (g (b , d)))           ≡⟨ cong arrow (ΣPathP (refl , (sym (st² (snd (g (b , d))))))) ⟩
    arrow (inl (fst (g (b , d))) , st (st (snd (g (b , d))))) ∎
  q =
    snd (g (b , st (st d)))   ≡⟨ cong (snd ∘ g) (ΣPathP (refl , st² d)) ⟩
    snd (g (b , d))           ≡⟨ sym (st² _) ⟩
    st (st (snd (g (b , d)))) ∎

prev-op : (x : dArrows) → prev (op x) ≡ op (next x)
prev-op (inl a , d) = refl
prev-op (inr b , d) = refl

-- iterate
iterate : ℤ → dArrows → dArrows
iterate zero x = x
iterate (suc n) x = next (iterate n x)
iterate (predl n) x = prev (iterate n x)
iterate (predr n) x = prev (iterate n x)
iterate (predl-suc n i) x = prev-next (iterate n x) i
iterate (suc-predr n i) x = next-prev (iterate n x) i

abstract
  iterate-+ : (m n : ℤ) (e : dArrows) → iterate n (iterate m e) ≡ iterate (m ℤ.+ n) e
  iterate-+ m n e = ℤ.elim
    (λ n → iterate n (iterate m e) ≡ iterate (m ℤ.+ n) e)
    (cong (λ m → iterate m e) (sym (ℤ.+-zero m)))
    (λ n p → cong next p ∙ sym (cong (λ k → iterate k e) (ℤ.+-suc m n)))
    (λ n p → cong prev p ∙ sym (cong (λ k → iterate k e) (ℤ.+-pred m n)))
    (λ n p → cong prev p ∙ sym (cong (λ k → iterate k e) (ℤ.+-predr m n)))
    (λ n p → toPathP (Ends-isSet _ _ _ _))
    (λ n p → toPathP (Ends-isSet _ _ _ _))
    n

iterate-op : (n : ℤ) (e : dArrows) → iterate n (op e) ≡ op (iterate (ℤ.neg n) e)
iterate-op n e = ℤ.elim
  (λ n → iterate n (op e) ≡ op (iterate (ℤ.neg n) e))
  refl
  (λ n p → cong next p ∙ next-op _)
  (λ n p → cong prev p ∙ prev-op _)
  (λ n p → cong prev p ∙ prev-op _)
  (λ n p → toPathP (Ends-isSet _ _ _ _))
  (λ n p → toPathP (Ends-isSet _ _ _ _))
  n

iterate-neg : (n : ℤ) (e : dArrows) → iterate (ℤ.neg n) e ≡ op (iterate n (op e))
iterate-neg n e = sym (op-op _) ∙ cong op (sym (iterate-op n e))

iterate-neg-op : (n : ℤ) (e : dArrows) → iterate (ℤ.neg n) (op e) ≡ op (iterate n e)
iterate-neg-op n e = iterate-neg n (op e) ∙ cong (op ∘ (iterate n)) (op-op e)

-- parity

next-A-switch : {x : dArrows} → in-left (arrow x) → in-right (arrow (next x))
next-A-switch (is-inl a) = is-inr _

next-B-switch : {x : dArrows} → in-right (arrow x) → in-left (arrow (next x))
next-B-switch (is-inr b) = is-inl _

prev-A-switch : {x : dArrows} → in-left (arrow x) → in-right (arrow (prev x))
prev-A-switch (is-inl x) = is-inr _

prev-B-switch : {x : dArrows} → in-right (arrow x) → in-left (arrow (prev x))
prev-B-switch (is-inr x) = is-inl _

iterate-A-even : {x : dArrows} → in-left (arrow x)  → {n : ℤ} → ℤ.is-even n → in-left  (arrow (iterate n x))
iterate-A-odd  : {x : dArrows} → in-left (arrow x)  → {n : ℤ} → ℤ.is-odd  n → in-right (arrow (iterate n x))
iterate-B-even : {x : dArrows} → in-right (arrow x) → {n : ℤ} → ℤ.is-even n → in-right (arrow (iterate n x))
iterate-B-odd  : {x : dArrows} → in-right (arrow x) → {n : ℤ} → ℤ.is-odd  n → in-left  (arrow (iterate n x))
iterate-A-even (is-inl x) even-zero = is-inl x
iterate-A-even (is-inl x) (even-suc p) = next-B-switch (iterate-A-odd (is-inl x) p)
iterate-A-even (is-inl x) (even-predl p) = prev-B-switch (iterate-A-odd (is-inl x) p)
iterate-A-even (is-inl x) (even-predr p) = prev-B-switch (iterate-A-odd (is-inl x) p)
iterate-A-odd (is-inl x)  (odd-suc p) = next-A-switch (iterate-A-even (is-inl x) p)
iterate-A-odd (is-inl x)  (odd-predl p) = prev-A-switch (iterate-A-even (is-inl x) p)
iterate-A-odd (is-inl x)  (odd-predr p) = prev-A-switch (iterate-A-even (is-inl x) p)
iterate-B-even (is-inr b) even-zero = is-inr b
iterate-B-even (is-inr b) (even-suc p) = next-A-switch (iterate-B-odd (is-inr b) p)
iterate-B-even (is-inr b) (even-predl p) = prev-A-switch (iterate-B-odd (is-inr b) p)
iterate-B-even (is-inr b) (even-predr p) = prev-A-switch (iterate-B-odd (is-inr b) p)
iterate-B-odd (is-inr b) (odd-suc p) = next-B-switch (iterate-B-even (is-inr b) p)
iterate-B-odd (is-inr b) (odd-predl p) = prev-B-switch (iterate-B-even (is-inr b) p)
iterate-B-odd (is-inr b) (odd-predr p) = prev-B-switch (iterate-B-even (is-inr b) p)

---
--- Chains and direction
---

reachable : dArrows → dArrows → Type ℓ
reachable e e' = Σ ℤ (λ n → iterate n e ≡ e')

is-reachable : dArrows → dArrows → Type ℓ
is-reachable e e' = ∥ reachable e e' ∥

reachable-is-reachable : (e e' : dArrows) → reachable e e' → is-reachable e e'
reachable-is-reachable e e' r = ∣ r ∣

-- reachability
-- note that this is not a proposition, so that we often have to truncate
reachable-arr : Arrows → Arrows → Type ℓ
reachable-arr a b = Σ ℤ (λ n → arrow (iterate n (fw a)) ≡ b)

reachable-op : {e e' : dArrows} → reachable (op e') (op e) → reachable e e'
reachable-op {e} {e'} (n , r)  = n , (
  iterate n e                                ≡⟨ cong (iterate n) (sym (op-op e)) ⟩
  iterate n (op (op e))                      ≡⟨ iterate-op n (op e) ⟩
  op (iterate (ℤ.neg n) (op e))              ≡⟨ cong op (cong (iterate (ℤ.neg n)) (sym r)) ⟩
  op (iterate (ℤ.neg n) (iterate n (op e'))) ≡⟨ cong op (iterate-+ n (ℤ.neg n) (op e')) ⟩
  op (iterate (n ℤ.+ ℤ.neg n) (op e'))       ≡⟨ cong (λ n → op (iterate n (op e'))) (+neg≡0 n) ⟩
  op (iterate ℤ.zero (op e'))                ≡⟨ refl ⟩
  op (op e')                                 ≡⟨ op-op e' ⟩
  e'                                         ∎)

reachable→reachable-arr : {e e' : dArrows} → reachable e e' → reachable-arr (arrow e) (arrow e')
reachable→reachable-arr {a , src} {e'} (n , r) = n , cong arrow r
reachable→reachable-arr e@{a , tgt} {e'} (n , r) = ℤ.neg n , p
  where
  abstract
    p =
      arrow (iterate (ℤ.neg n) (fw (arrow (a , tgt)))) ≡⟨ cong arrow (iterate-op (ℤ.neg n) e) ⟩
      arrow (op (iterate (ℤ.neg (ℤ.neg n)) e))         ≡⟨ cong (λ n → arrow (op (iterate n e))) (ℤ.neg-neg n) ⟩
      arrow (op (iterate n e))                         ≡⟨ refl ⟩
      arrow (iterate n e)                              ≡⟨ cong arrow r ⟩
      arrow e'                                         ∎

reachable-arr→reachable : {a b : Arrows} → reachable-arr a b → reachable (fw a) (fw b) ⊎ reachable (fw a) (bw b)
reachable-arr→reachable {a} {b} (n , r) with Ends.case≡ (end (iterate n (fw a)))
... | inl p = inl (n , end≡ r p)
... | inr p = inr (n , end≡ r p)

is-reachable-arr : (a b : Arrows) → Type ℓ
is-reachable-arr a b = ∥ reachable-arr a b ∥

is-reachable-arr-isProp : (a b : Arrows) → isProp (is-reachable-arr a b)
is-reachable-arr-isProp a b = propTruncIsProp

reachable-refl : {e : dArrows} → reachable e e
reachable-refl = ℤ.zero , refl

reachable-sym : {e e' : dArrows} → reachable e e' → reachable e' e
reachable-sym {e} {e'} (n , r) = ℤ.neg n , (
  iterate (ℤ.neg n) e'            ≡⟨ cong (iterate (ℤ.neg n)) (sym r) ⟩
  iterate (ℤ.neg n) (iterate n e) ≡⟨ iterate-+ n (ℤ.neg n) e ⟩
  iterate (n ℤ.+ ℤ.neg n) e       ≡⟨ cong (λ n → iterate n e) (+neg≡0 n) ⟩
  iterate ℤ.zero e                ≡⟨ refl ⟩
  e                               ∎)

reachable-trans : {e e' e'' : dArrows} → reachable e e' → reachable e' e'' → reachable e e''
reachable-trans {e} (n , r) (n' , r') = n ℤ.+ n' , sym (iterate-+ n n' e) ∙ cong (iterate n') r ∙ r'

reachable-is-equiv : isEquivRel reachable
isEquivRel.reflexive reachable-is-equiv _ = reachable-refl
isEquivRel.symmetric reachable-is-equiv _ _ r = reachable-sym r
isEquivRel.transitive reachable-is-equiv _ _ _ r r' = reachable-trans r r'

reachable-symop : {e e' : dArrows} → reachable (op e) (op e') → reachable e e'
reachable-symop r = reachable-sym (reachable-op r)

reachable-next : (e : dArrows) → reachable e (next e)
reachable-next e = ℤ.one , refl

reachable-prev : (e : dArrows) → reachable (prev e) e
reachable-prev e = ℤ.one , next-prev e

reachable-zero : {e e' : dArrows} (r : reachable e e') → fst r ≡ zero → e ≡ e'
reachable-zero {e} (n , r) l≡0 = subst (λ n → e ≡ iterate n e) (sym l≡0) refl ∙ r

is-reachable-refl : {e : dArrows} → is-reachable e e
is-reachable-refl {e} = ∣ isEquivRel.reflexive reachable-is-equiv e ∣

is-reachable-path : {e e' : dArrows} → e ≡ e' → is-reachable e e'
is-reachable-path {e} p = subst (is-reachable e) p is-reachable-refl

is-reachable-sym : {e e' : dArrows} → is-reachable e e' → is-reachable e' e
is-reachable-sym {e} {e'} r = ∥∥.rec propTruncIsProp (λ r → ∣ isEquivRel.symmetric reachable-is-equiv e e' r ∣) r

is-reachable-trans : {e e' e'' : dArrows} → is-reachable e e' → is-reachable e' e'' → is-reachable e e''
is-reachable-trans r r' = ∥∥.rec propTruncIsProp (λ r → ∥∥.rec propTruncIsProp (λ r' → ∣ isEquivRel.transitive reachable-is-equiv _ _ _ r r' ∣) r') r

is-reachable-is-equiv : isEquivRel is-reachable
isEquivRel.reflexive is-reachable-is-equiv e = is-reachable-refl
isEquivRel.symmetric is-reachable-is-equiv e e' r = is-reachable-sym r
isEquivRel.transitive is-reachable-is-equiv e e' e'' r r' = is-reachable-trans r r'

-- useful variant of reachable-op
reachable→op : {e e' : dArrows} → reachable e e' → reachable (op e) (op e')
reachable→op {e} {e'} r = isEquivRel.symmetric reachable-is-equiv _ _ (reachable-op (subst (reachable (op (op e))) (sym (op-op e')) (subst (λ e → reachable e e') (sym (op-op e)) r)))

-- reachable-arr-is-equiv : isEquivRel reachable-arr
-- isEquivRel.reflexive reachable-arr-is-equiv a = ℤ.zero , (sym (arrow-fw a))
-- isEquivRel.symmetric reachable-arr-is-equiv a b (n , p) = ℤ.neg n , {!!}
-- isEquivRel.transitive reachable-arr-is-equiv a b c (n , p) (n' , p') with case≡ (end (iterate n (fw a)))
-- ... | inl u = n ℤ.+ n' , p' ∙ cong arrow (cong (iterate n') (end≡ (arrow-fw b ∙ p) (end-fw b ∙ sym u))) ∙ cong arrow (iterate-+ n n' (fw a))
-- ... | inr u = n ℤ.+ n' , {!!} ∙ cong arrow (iterate-+ n n' (fw a))

reachable-arr-refl : {a : Arrows} → reachable-arr a a
reachable-arr-refl {a} = ℤ.zero , refl

reachable-arr-path : {a b : Arrows} → a ≡ b → reachable-arr a b
reachable-arr-path {a} p = subst (reachable-arr a) p reachable-arr-refl

reachable-arr-sym : {a b : Arrows} → reachable-arr a b → reachable-arr b a
reachable-arr-sym {a} {b} r with reachable-arr→reachable r
... | inl r' = fst r'' , cong arrow (snd r'')
  where
  r'' : reachable (fw b) (fw a)
  r'' = isEquivRel.symmetric reachable-is-equiv _ _ r'
... | inr r' = fst r'' , cong arrow (snd r'')
  where
  r'' : reachable (op (bw b)) (op (fw a))
  r'' = isEquivRel.symmetric reachable-is-equiv _ _ (reachable→op r')

reachable-arr-trans : {a b c : Arrows} → reachable-arr a b → reachable-arr b c → reachable-arr a c
reachable-arr-trans {a} {b} {c} r s with reachable-arr→reachable r
... | inl (n , r') = n ℤ.+ (fst s) , cong arrow (sym (iterate-+ n (fst s) (fw a))) ∙ cong arrow (cong (iterate (fst s)) r') ∙ snd s
... | inr (n , r') = n ℤ.+ ℤ.neg (fst s) , cong arrow (sym (iterate-+ n (ℤ.neg (fst s)) (fw a))) ∙ cong arrow (cong (iterate (ℤ.neg (fst s))) r') ∙ cong arrow (iterate-neg (fst s) (bw b)) ∙ snd s

reachable-arr-is-equiv : isEquivRel reachable-arr
isEquivRel.reflexive reachable-arr-is-equiv a = reachable-arr-refl
isEquivRel.symmetric reachable-arr-is-equiv a b r = reachable-arr-sym r
isEquivRel.transitive reachable-arr-is-equiv a b c r s = reachable-arr-trans r s

is-reachable-arr-refl : {a : Arrows} → is-reachable-arr a a
is-reachable-arr-refl = ∣ reachable-arr-refl ∣

is-reachable-arr-path : {a b : Arrows} → a ≡ b → is-reachable-arr a b
is-reachable-arr-path {a} p = subst (is-reachable-arr a) p is-reachable-arr-refl

is-reachable-arr-sym : {a b : Arrows} → is-reachable-arr a b → is-reachable-arr b a
is-reachable-arr-sym {a} {b} r = ∥∥.rec propTruncIsProp (λ r → ∣ isEquivRel.symmetric reachable-arr-is-equiv a b r ∣) r

is-reachable-arr-trans : {a b c : Arrows} → is-reachable-arr a b → is-reachable-arr b c → is-reachable-arr a c
is-reachable-arr-trans r r' = ∥∥.rec propTruncIsProp (λ r → ∥∥.rec propTruncIsProp (λ r' → ∣ reachable-arr-trans r r' ∣) r') r

is-reachable-arr-is-equiv : isEquivRel is-reachable-arr
isEquivRel.reflexive is-reachable-arr-is-equiv _ = is-reachable-arr-refl
isEquivRel.symmetric is-reachable-arr-is-equiv _ _ r = is-reachable-arr-sym r
isEquivRel.transitive is-reachable-arr-is-equiv _ _ _ r r' = is-reachable-arr-trans r r'

is-reachable→is-reachable-arr : {e e' : dArrows} → is-reachable e e' → is-reachable-arr (arrow e) (arrow e')
is-reachable→is-reachable-arr r = ∥∥.map reachable→reachable-arr r

-- making the reveal functions compute takes too much time
abstract
  -- we can always find the reachability proof when there exists one (this is
  -- because ℤ is searchable)
  -- NB: we need both A to be a set and discrete
  reachable-arr-reveal : {a b : Arrows} → is-reachable-arr a b → reachable-arr a b
  reachable-arr-reveal {a} {b} r = transport (Σ-ap₁ (ua (invEquiv ℤ≃ℕ)))
      (ℕ.find _ (λ _ → Arrows-isSet _ _) (λ n → Arrows-discrete _ _) (transport (cong ∥_∥ (Σ-ap (ua ℤ≃ℕ) (λ n → cong (λ n → arrow (iterate n (fw a)) ≡ b) (sym (funExt⁻ (lem ℤ≃ℕ) n))))) r))
    where
    lem : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} (e : A ≃ B) → transport (ua (invEquiv e)) ∘ transport (ua e) ≡ idfun A
    lem {_} {A} {B} e =
      transport (ua (invEquiv e)) ∘ transport (ua e) ≡⟨ funExt (λ x → sym (transportComposite (ua e) (ua (invEquiv e)) x)) ⟩
      transport (ua e ∙ ua (invEquiv e))             ≡⟨ cong transport (sym (uaCompEquiv e (invEquiv e))) ⟩
      transport (ua (compEquiv e (invEquiv e)))      ≡⟨ cong (transport ∘ ua) (invEquiv-is-rinv e) ⟩
      transport (ua (idEquiv A))                     ≡⟨ cong transport uaIdEquiv ⟩
      transport refl                                 ≡⟨ funExt transportRefl ⟩
      idfun A                                        ∎

  -- same as above (plus we can test the ends...)
  reachable-reveal : {a b : dArrows} → is-reachable a b → reachable a b
  reachable-reveal {a} {b} r = transport (Σ-ap₁ (ua (invEquiv ℤ≃ℕ)))
       (ℕ.find _ (λ _ → Ends-isSet _ _) (λ n → Ends-discrete _ _) (transport (cong ∥_∥ (Σ-ap (ua ℤ≃ℕ) (λ n → cong (λ n → iterate n a ≡ b) (sym (funExt⁻ (lem ℤ≃ℕ) n))))) r))
    where
    lem : {ℓ : Level} {A : Type ℓ} {B : Type ℓ} (e : A ≃ B) → transport (ua (invEquiv e)) ∘ transport (ua e) ≡ idfun A
    lem {_} {A} {B} e =
      transport (ua (invEquiv e)) ∘ transport (ua e) ≡⟨ funExt (λ x → sym (transportComposite (ua e) (ua (invEquiv e)) x)) ⟩
      transport (ua e ∙ ua (invEquiv e))             ≡⟨ cong transport (sym (uaCompEquiv e (invEquiv e))) ⟩
      transport (ua (compEquiv e (invEquiv e)))      ≡⟨ cong (transport ∘ ua) (invEquiv-is-rinv e) ⟩
      transport (ua (idEquiv A))                     ≡⟨ cong transport uaIdEquiv ⟩
      transport refl                                 ≡⟨ funExt transportRefl ⟩
      idfun A                                        ∎

-- -- the chain of an end (i.e. rougly a pointed chain)
-- chain-end : Ends → Type ℓ
-- chain-end e = Σ Ends (λ e' → ∥ reachable e e' ∥)

-- -- the chain of an arrow
-- chain : Arrows → Type ℓ
-- chain a = Σ Arrows λ b → ∥ reachable-arr a b ∥

-- chain-isSet : (a : Arrows) → isSet (chain a)
-- chain-isSet a = isSetΣ Arrows-isSet λ _ → isProp→isSet propTruncIsProp

-- reachable-arr arrows have a unique orientation
unique-orientation : {e₀ e e' : dArrows} → reachable e₀ e → reachable e₀ e' → arrow e ≡ arrow e' → e ≡ e'
unique-orientation {_} {e} {e'} r r' p =
  let rr' : reachable e e'
      rr' = reachable-trans (reachable-sym r) r'
  in
  -- up to exchanging e and e', we can always suppose that the length from e to e' is positive
  case fst rr' ℤ.≟ zero of λ {
    (lt l<0) →
      let ln : Σ ℕ (λ n → fst (reachable-sym rr') ≡ fromℕ n)
          ln = pos-fromℕ (≤-neg (ℤ.≤-trans (≤-≡ (neg-neg _)) (<→≤ l<0)))
      in
      sym (unique-end (fst ln) (reachable-sym rr') (snd ln) (sym p)) ;
    (eq l≡0) → reachable-zero rr' l≡0 ;
    (gt l>0) →
      let ln : Σ ℕ (λ n → fst rr' ≡ fromℕ n)
          ln = pos-fromℕ (<→≤ l>0)
      in
      unique-end (fst ln) rr' (snd ln) p
    }
  where
  -- the property on loops, shown by induction on the length of the loop
  unique-end : {e e' : Ends} (l : ℕ) (r : reachable e e') → fst r ≡ fromℕ l → arrow e ≡ arrow e' → e ≡ e'
  unique-end {e} {e'} zero r lr p = reachable-zero r lr
  -- impossible because of parity
  unique-end {e} {e'} (suc zero) (n , r) lr p = {!!}
  -- let's shorten the loop
  unique-end {e} {e'} (suc (suc l)) r lr p with Ends.case≡ (end e) | Ends.case≡ (end e')
  ... | inl es | inl e's = end≡ p (es ∙ sym e's)
  ... | inr et | inr e't = end≡ p (et ∙ sym e't)
  ... | inl es | inr e't = ⊥.rec (op≢ _ (sym npee' ∙ unique-end l r'' l'' (cong arrow npee'))) 
    where
      ee' : e ≡ op e'
      ee' = end≡ p (es ∙ sym (cong st e't))
      npee' : next e ≡ op (prev e')
      npee' = cong next ee' ∙ next-op e'
      r'' : reachable (next e) (prev e')
      r'' = reachable-trans (reachable-sym (reachable-next e)) (reachable-trans r (reachable-sym (reachable-prev e')))
      l'' : fst r'' ≡ fromℕ l
      l'' =
        fst r''                                 ≡⟨ refl ⟩
        -one ℤ.+ (fst r ℤ.+ -one)               ≡⟨ cong (λ n → -one ℤ.+ (n ℤ.+ -one)) lr ⟩
        -one ℤ.+ (suc (suc (fromℕ l)) ℤ.+ -one) ≡⟨ -1+suc _ ⟩
        suc (fromℕ l) ℤ.+ -one                  ≡⟨ suc+-1 _ ⟩
        fromℕ l                                 ∎
  ... | inr et | inl e's = {!!} -- similar to previous case

-- the type of directed chains
-- NB: quotienting by the propositional truncation or the relation itself does not change anything...
dChains : Type ℓ
dChains = dArrows / λ a b → is-reachable a b

dChains-isSet : isSet dChains
dChains-isSet = squash/

-- elements of a directed chain
delements : dChains → Type ℓ
delements c = fiber [_] c

delements-isSet : (c : dChains) → isSet (delements c)
delements-isSet c = isSetΣ Ends-isSet λ _ → isProp→isSet (dChains-isSet _ _)

abstract
  delement-is-reachable-arr : {o : Ends} (a : delements [ o ]) → is-reachable o (fst a)
  delement-is-reachable-arr {o} (a , r) = effective (λ _ _ → propTruncIsProp) is-reachable-is-equiv o a (sym r)

  delement-reachable-arr : {o : Ends} (a : delements [ o ]) → reachable o (fst a)
  delement-reachable-arr a = reachable-reveal (delement-is-reachable-arr a)

delements-element : {c : dChains} (a : delements c) → delements [ fst a ] ≡ delements c
delements-element a = cong delements (snd a)

-- the type of all chains
-- NB: quotienting by the propositional truncation or the relation itself does not change anything...
Chains : Type ℓ
Chains = Arrows / λ a b → is-reachable-arr a b

Chains-isSet : isSet Chains
Chains-isSet = squash/

-- elements of a chain
elements : Chains → Type ℓ
elements c = fiber [_] c

elements-isSet : (c : Chains) → isSet (elements c)
elements-isSet c = isSetΣ Arrows-isSet (λ _ → isProp→isSet (Chains-isSet _ _))

-- every element of a chain is reachable-arr
-- note that we need the relation to be effective here, and thus have a set
-- NB: this is the kind of place where we use the fact that we quotient under the propositional truncation in order to have effectivity
abstract
  delements-is-reachable : {c : dChains} (a b : delements c) → is-reachable (fst a) (fst b)
  delements-is-reachable {c} (a , p) (b , q) = effective (λ _ _ → propTruncIsProp) is-reachable-is-equiv a b (p ∙ sym q)

  element-is-reachable-arr : {o : Arrows} (a : elements [ o ]) → is-reachable-arr o (fst a)
  element-is-reachable-arr {o} (a , p) = effective (λ _ _ → propTruncIsProp) is-reachable-arr-is-equiv o a (sym p)

  element-reachable-arr : {o : Arrows} (a : elements [ o ]) → reachable-arr o (fst a)
  element-reachable-arr a = reachable-arr-reveal (element-is-reachable-arr a)

  element-chain : {o : Arrows} (a : elements [ o ]) → [_] {R = is-reachable-arr} o ≡ [ fst a ]
  element-chain {o} a = eq/ _ _ (element-is-reachable-arr a)

  -- two elements of a chains are reachable-arr (this is a variant of the above)
  elements-is-reachable-arr : {c : Chains} (a b : elements c) → is-reachable-arr (fst a) (fst b)
  elements-is-reachable-arr (a , p) (b , q) = effective (λ _ _ → propTruncIsProp) is-reachable-arr-is-equiv a b (p ∙ sym q)

  elements-reachable-arr : {c : Chains} (a b : elements c) → reachable-arr (fst a) (fst b)
  elements-reachable-arr a b = reachable-arr-reveal (elements-is-reachable-arr a b)

elements-element : {c : Chains} (a : elements c) → elements [ fst a ] ≡ elements c
elements-element a = cong elements (snd a)

-- end reached by an arrow
element-end : {o : Arrows} (a : elements [ o ]) → Ends
element-end {o} a = iterate (fst (element-reachable-arr a)) (fw o)

-- the end reached by an arrow is reachable-arr
element-end-reachable-arr : {a : Arrows} (e : elements [ a ]) → reachable (fw a) (element-end e)
element-end-reachable-arr {a} e = fst (element-reachable-arr e) , refl

arrow-element-end : {o : Arrows} (a : elements [ o ]) → arrow (element-end a) ≡ fst a
arrow-element-end {o} a = snd (element-reachable-arr a)

element-end-is-left : {o : Arrows} (a : elements [ o ]) → in-left (fst a) → in-left (arrow (element-end a))
element-end-is-left a l = subst in-left (sym (arrow-element-end a)) l

element-end-is-right : {o : Arrows} (a : elements [ o ]) → in-right (fst a) → in-right (arrow (element-end a))
element-end-is-right a r = subst in-right (sym (arrow-element-end a)) r

-- picking an element in a chain canonically provides an orientation to all other elements
orientation : {o : Arrows} (a : elements [ o ]) → End
orientation a = end (element-end a)

orientation-reachable-arr : {o : Arrows} (a : elements [ o ]) → reachable (fw o) (orient (fst a) (orientation a))
orientation-reachable-arr {o} a with element-reachable-arr a
... | n , r = n , sym p
  where
  p =
    orient (fst a) (end (iterate n (orient o src)))                            ≡⟨ cong (λ a → orient a _) (sym r) ⟩
    orient (arrow (iterate n (orient o src))) (end (iterate n (orient o src))) ≡⟨ refl ⟩
    iterate n (orient o src)                                                   ∎

delements→elements : {o : dArrows} → delements [ o ] → elements [ arrow o ]
delements→elements {o} (a , p) = arrow a , eq/ _ _ (is-reachable→is-reachable-arr rao)
  where
  rao : is-reachable a o
  rao = subst (λ a → is-reachable a o) (transportRefl a) (delements-is-reachable (subst delements p (a , refl)) (o , refl))

elements→delements : {o : Arrows} → elements [ o ] → delements [ fw o ]
elements→delements {o} a = element-end a , p
  where
  abstract
    p = sym (eq/ _ _ ∣ element-end-reachable-arr a ∣)

-- This shows that we have a canonical orientation once we fix the fwing point
delements≃elements : {o : Arrows} → delements [ fw o ] ≃ elements [ o ]
delements≃elements {o} = isoToEquiv i
  where
  i : Iso (delements [ fw o ]) (elements [ o ])
  Iso.fun i = delements→elements
  Iso.inv i = elements→delements
  Iso.rightInv i a = ΣProp≡ (λ _ → Chains-isSet _ _) (arrow-element-end _)
  Iso.leftInv i a = ΣProp≡ (λ _ → dChains-isSet _ _) (unique-orientation (element-end-reachable-arr (delements→elements a)) (delement-reachable-arr a) (arrow-element-end (delements→elements a)))

canonical-orientation : {o : Arrows} → delements [ fw o ] ≡ elements [ o ]
canonical-orientation {o} = ua delements≃elements

-- -- picking an element in a chain canonically provides an orientation to all other elements
-- orientation : {c : Chains} (o : elements c) (a : elements c) → End
-- orientation o a with elements-reachable-arr o a
-- ... | n , _ = end (iterate n (fw (fst o)))

-- orientation-reachable-arr : {c : Chains} (o : elements c) (a : elements c) → reachable (fw (fst o)) (orient (fst a) (orientation o a))
-- orientation-reachable-arr o a with elements-reachable-arr o a
-- ... | n , r = n , end≡ (r ∙ sym (arrow-orient _ _)) (sym (end-orient (fst a) (end (iterate n (fw (fst o))))))

-- elements in A in the chain
chainA : Chains → Type ℓ
chainA c = Σ (elements c) (in-left ∘ fst)

-- elements in B in the chain
chainB : Chains → Type ℓ
chainB c = Σ (elements c) (in-right ∘ fst)

chainB-isSet : (c : Chains) → isSet (chainB c)
chainB-isSet c = isSetΣ (elements-isSet c) λ _ → isProp→isSet (in-right-isProp _)

-- we have a bijection between the elements in the chain
chain-A≃B : Chains → Type ℓ
chain-A≃B c = chainA c ≃ chainB c

chain-A≃B-isSet : (c : Chains) → isSet (chain-A≃B c)
chain-A≃B-isSet c = isOfHLevel≃ 2 (isSetΣ (elements-isSet c) (λ _ → isProp→isSet (in-left-isProp _))) (isSetΣ (elements-isSet c) λ _ → isProp→isSet (in-right-isProp _))
