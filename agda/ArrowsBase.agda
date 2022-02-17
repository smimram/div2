{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []
open import Z as ℤ
open import Ends

--- Definitions on arrows which do not depend on the hypothesis that A and B are
--- sets

module ArrowsBase {ℓ} {A B : Type ℓ} (isom : A × End ≃ B × End) where

f : A × End → B × End
f = equivFun isom

g : B × End → A × End
g = invEq isom

g-f : (x : A × End) → g (f x) ≡ x
g-f = secEq isom

f-g : (x : B × End) → f (g x) ≡ x
f-g = retEq isom

Arrows : Type ℓ
Arrows = A ⊎ B

Ends : Type ℓ
Ends = Arrows × End

-- an end seen as a directed arrow
dArrows = Ends

arrow : dArrows → Arrows
arrow = fst

end : dArrows → End
end = snd

end≡ : {e e' : Ends} → arrow e ≡ arrow e' → end e ≡ end e' → e ≡ e'
end≡ p q = ΣPathP (p , q)

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

next≃ : dArrows ≃ dArrows
next≃ = isoToEquiv i
  where
  i : Iso dArrows dArrows
  Iso.fun i = next
  Iso.inv i = prev
  Iso.rightInv i = next-prev
  Iso.leftInv i = prev-next

-- iterate
iterate : ℤ → dArrows → dArrows
iterate zero x = x
iterate (suc n) x = next (iterate n x)
iterate (predl n) x = prev (iterate n x)
iterate (predr n) x = prev (iterate n x)
iterate (predl-suc n i) x = prev-next (iterate n x) i
iterate (suc-predr n i) x = next-prev (iterate n x) i

---
--- Reachability
---

reachable : dArrows → dArrows → Type ℓ
reachable e e' = Σ ℤ (λ n → iterate n e ≡ e')

is-reachable : dArrows → dArrows → Type ℓ
is-reachable e e' = ∥ reachable e e' ∥

---
--- Chains
---

-- the type of directed chains
-- NB: quotienting by the propositional truncation or the relation itself does not change anything...
dChains : Type ℓ
dChains = dArrows / is-reachable

-- elements of a directed chain
delements : dChains → Type ℓ
delements c = fiber [_] c
