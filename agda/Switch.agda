{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
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
open import Sigma
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

open import Ends

module Switch {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom
open import Bracketing SA SB isom

---
--- Switched and slope chains
---

switch : Arrows → Type₀
switch a =
  (¬ (matched a)) ×
  Σ ℕ (λ n →
    let b = iterate (fromℕ n) (bw a) in
    -- b is in opposite direction
    (end b ≡ src) ×
    -- b is not bracketed
    (¬ (matched (arrow b))) ×
    -- all intermediate elements are bracketed
    ((k : ℕ) → suc k < n → matched (arrow (iterate (fromℕ (suc k)) (bw a))))
   )

switch-isProp : (a : Arrows) → isProp (switch a)
switch-isProp a (m , n , e , b , l) (m' , n' , e' , b' , l') i =
  isPropΠ (λ _ → isProp⊥) m m' i ,
  n≡n' i ,
  isSet→isSet' End-isSet e e' (cong (λ n → end (iterate (fromℕ n) (bw a))) n≡n') refl i ,
  b≡b' i ,
  l≡l' i
  where
  isZero : (n : ℕ) → (n ≡ ℕ.zero) ⊎ (Σ ℕ (λ k → n ≡ suc k))
  isZero ℕ.zero = inl refl
  isZero (suc n) = inr (n , refl)
  n≡n' : n ≡ n'
  n≡n' with n ≟ n'
  n≡n' | lt n<n' with isZero n
  n≡n' | lt n<n' | inl n≡0 = ⊥.rec (src≢tgt (sym (cong (λ n → end (iterate (fromℕ n) (bw a))) (sym n≡0) ∙ e)))
  n≡n' | lt n<n' | inr (n'' , n≡sn'') = ⊥.rec (b ma)
    where
    ma : matched (arrow (iterate (fromℕ n) (bw a)))
    ma = subst (λ n → matched (arrow (iterate (fromℕ n) (bw a)))) (sym n≡sn'') (l' n'' (subst (λ n → n < n') n≡sn'' n<n'))
  n≡n' | eq n≡n' = n≡n'
  n≡n' | gt n'<n with isZero n'
  n≡n' | gt n'<n | inl n'≡0 = ⊥.rec (src≢tgt (sym (cong (λ n' → end (iterate (fromℕ n') (bw a))) (sym n'≡0) ∙ e')))
  n≡n' | gt n'<n | inr (n'' , n'≡sn'') = ⊥.rec (b' ma)
    where
    ma : matched (arrow (iterate (fromℕ n') (bw a)))
    ma = subst (λ n' → matched (arrow (iterate (fromℕ n') (bw a)))) (sym n'≡sn'') (l n'' (subst (λ n' → n' < n) n'≡sn'' n'<n))
  b≡b' : PathP (λ j → ¬ (matched (arrow (iterate (fromℕ (n≡n' j)) (bw a))))) b b'
  b≡b' = toPathP (isPropΠ (λ _ → isProp⊥) _ _)
  l≡l' : PathP (λ i → ((k : ℕ) → suc k < n≡n' i → matched (arrow (iterate (fromℕ (suc k)) (bw a))))) l l'
  l≡l' = toPathP (isPropΠ2 (λ k _ → matched-isProp (arrow (iterate (fromℕ (suc k)) (bw a)))) _ _)

-- the chain of an arrow is switched
switched-end : dArrows → Type ℓ
switched-end e₀ = Σ ℤ (λ n →
  let e = iterate n e₀ in
    -- we have to suppose that this is left, otherwise we have two witnesses
    -- (one in A, one in B) and we don't have a proposition anymore
    in-left (arrow e) × switch (arrow e)
  )

-- being switched is a proposition
switched-end-isProp : (a : dArrows) → isProp (switched-end a)
switched-end-isProp a (n , l , s) (n' , l' , s') with n ℤ.≟ n'
... | lt n<n' = {!!} -- combinatorial argument
... | eq n≡n' = ΣPathP (n≡n' , (toPathP (ΣPathP (in-left-isProp _ _ _ , switch-isProp _ _ _))))
... | gt n'<n = {!!} -- here also

-- being switched is independent of the starting point
switched-end-indep : {a b : dArrows} (r : reachable a b) → switched-end a ≡ switched-end b
switched-end-indep {a} {b} (nr , r) = ua (isoToEquiv i)
  where
  i : Iso (switched-end a) (switched-end b)
  Iso.fun i (n , l , s) = (ℤ.neg nr ℤ.+ n) , subst (in-left ∘ arrow) (sym p) l , subst switch (cong arrow (sym p)) s
    where
      p =
        iterate (ℤ.neg nr ℤ.+ n) b              ≡⟨ cong (iterate (ℤ.neg nr ℤ.+ n)) (sym r) ⟩
        iterate (ℤ.neg nr ℤ.+ n) (iterate nr a) ≡⟨ iterate-+ nr _ _ ⟩
        iterate (nr ℤ.+ (ℤ.neg nr ℤ.+ n)) a     ≡⟨ cong (λ n → iterate n a) (ℤ.+-assoc nr _ _) ⟩
        iterate ((nr ℤ.+ ℤ.neg nr) ℤ.+ n) a     ≡⟨ cong (λ m → iterate (m ℤ.+ n) a) (n-n≡0 nr) ⟩
        iterate (ℤ.zero ℤ.+ n) a                ≡⟨ cong (λ n → iterate n a) (ℤ.zero-+ n) ⟩
        iterate n a                             ∎
  Iso.inv i (n , l , s) = (nr ℤ.+ n) , subst (in-left ∘ arrow) p l , subst switch (cong arrow p) s
    where
      p =
        iterate n b              ≡⟨ cong (iterate n) (sym r) ⟩
        iterate n (iterate nr a) ≡⟨ iterate-+ nr n a ⟩
        iterate (nr ℤ.+ n) a     ∎
  Iso.rightInv i (n , l , s) = ΣProp≡ (λ _ → isProp× (in-left-isProp _) (switch-isProp _)) p
    where
      p =
        ℤ.neg nr ℤ.+ (nr ℤ.+ n) ≡⟨ ℤ.+-assoc (ℤ.neg nr) _ _ ⟩
        (ℤ.neg nr ℤ.+ nr) ℤ.+ n ≡⟨ cong₂ ℤ._+_ (neg+≡0 nr) refl ⟩
        ℤ.zero ℤ.+ n            ≡⟨ ℤ.zero-+ n ⟩
        n                       ∎
  Iso.leftInv i (n , l , s) = ΣProp≡ (λ _ → isProp× (in-left-isProp _) (switch-isProp _)) p
    where
      p =
        nr ℤ.+ (ℤ.neg nr ℤ.+ n) ≡⟨ ℤ.+-assoc nr _ _ ⟩
        (nr ℤ.+ ℤ.neg nr) ℤ.+ n ≡⟨ cong₂ ℤ._+_ (+neg≡0 nr) refl ⟩
        ℤ.zero ℤ.+ n            ≡⟨ ℤ.zero-+ n ⟩
        n                       ∎

switched-end-op : (a : dArrows) → switched-end (op a) ≡ switched-end a
switched-end-op a = ua (isoToEquiv i)
  where
  F : (a : dArrows) → switched-end (op a) → switched-end a
  F a (n , l , s) = ℤ.neg n , subst in-left p l , subst switch p s
    where
    p : arrow (iterate n (op a)) ≡ arrow (iterate (neg n) a)
    p = cong arrow (iterate-op n a)
  i : Iso (switched-end (op a)) (switched-end a)
  Iso.fun i = F a
  Iso.inv i s = F (op a) (subst switched-end (sym (op-op a)) s)
  Iso.rightInv i (n , l , s) = ΣProp≡ (λ _ → isProp× (in-left-isProp _) (switch-isProp _)) (ℤ.neg-neg n)
  Iso.leftInv i (n , l , s) = ΣProp≡ (λ _ → isProp× (in-left-isProp _) (switch-isProp _)) (ℤ.neg-neg n)

switched-end-chain : dChains → Type ℓ
switched-end-chain c = fst T
  where
  T : hProp ℓ
  T = [].elim (λ _ → isSetHProp) (λ a → switched-end a , switched-end-isProp a) (λ a b r → ΣProp≡ (λ _ → isPropIsProp) (switched-end-indep (reachable-reveal r))) c

switched : Arrows → Type ℓ
switched a = switched-end (fw a)

switched-isProp : (a : Arrows) → isProp (switched a)
switched-isProp a = switched-end-isProp (fw a)

switched-indep : {a b : Arrows} (r : reachable-arr a b) → switched a ≡ switched b
switched-indep {a} {b} r with reachable-arr→reachable r
... | inl r' = switched-end-indep r'
... | inr r' = switched-end-indep r' ∙ p
  where
  p =
    switched-end (bw b) ≡⟨ switched-end-op (fw b) ⟩
    switched-end (fw b) ∎

switched-chain-hProp : Chains → hProp ℓ
switched-chain-hProp c = [].elim (λ _ → isSetHProp) (λ a → switched a , switched-isProp a) indep c
  where
  abstract
    indep = (λ a b r → ΣProp≡ (λ _ → isPropIsProp) (switched-indep (reachable-arr-reveal r)))

switched-chain : Chains → Type ℓ
switched-chain c = fst (switched-chain-hProp c)

switched-chain-isProp : (c : Chains) → isProp (switched-chain c)
switched-chain-isProp c = snd (switched-chain-hProp c)

-- Given a switched chain, we have a canonical element: the switching element
switched-element : (c : Chains) → switched-chain c → elements c
-- switched-element c sw = [].elim (λ c → elements-isSet c) (λ a → {!!}) (λ a b r → toPathP {!!}) c
switched-element c = [].elim
  { B = λ c → switched-chain c → elements c }
  (λ c → isSetΠ (λ _ → elements-isSet c))
  el
  el-indep
  c
  where
    -- the element
    el : (a : Arrows) → switched-chain [ a ] → elements [ a ]
    el a (n , _) = arrow (iterate n (fw a)) , sym (eq/ _ _ ∣ n , refl ∣)
    -- the choice of the element is inependent of the fwing point
    el-indep : (a b : Arrows) (r : is-reachable-arr a b) → PathP (λ i → switched-chain (eq/ a b r i) → elements (eq/ a b r i)) (el a) (el b)
    el-indep a b r = toPathP (funExt (λ sw → ΣProp≡ (λ _ → Chains-isSet _ _) (p sw)))
      where
      p = λ (sw : switched-chain [ b ]) →
         transport (λ i → Arrows) (fst (el a (subst switched-chain (sym (eq/ a b r)) sw))) ≡⟨ transportRefl _ ⟩
         el a (subst switched-chain (sym (eq/ a b r)) sw) . fst ≡⟨ refl ⟩
         arrow (iterate (fst (subst switched-chain (sym (eq/ a b r)) sw)) (fw a)) ≡⟨ {!!} ⟩
         arrow (iterate (fst sw) (fw b)) ≡⟨ refl ⟩
         el b sw .fst ∎
 
-- all non-matched arrows are in the same direction
sequential : dArrows → Type₀
sequential o = ((m n : ℤ) →
    let a = iterate m o in
    let b = iterate n o in
    ¬ (matched (arrow a)) → ¬ (matched (arrow b)) → end a ≡ end b)

sequential-isProp : (a : dArrows) → isProp (sequential a)
sequential-isProp a = isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → End-isSet _ _

sequential-op : (a : dArrows) → sequential (op a) ≡ sequential a
sequential-op a = ua (isoToEquiv i)
  where
  F : (a : dArrows) → sequential (op a) → sequential a
  F a s n n' nm nm' = subst₂ _≡_ (p n a) (p n' a) (cong st (s (ℤ.neg n) (ℤ.neg n') (λ m → nm (subst (matched ∘ arrow)(iterate-neg-op n a) m)) λ m → nm' (subst (matched ∘ arrow) (iterate-neg-op n' a) m)))
    where
    p : (n : ℤ) (a : dArrows) → st (end (iterate (neg n) (op a))) ≡ end (iterate n a)
    p n a = cong (st ∘ end) (iterate-neg-op n a) ∙ st² (end (iterate n a))
  i : Iso (sequential (op a)) (sequential a)
  Iso.fun i = F a
  Iso.inv i s = F (op a) (subst sequential (sym (op-op a)) s)
  Iso.rightInv i s = sequential-isProp _ _ _
  Iso.leftInv i s = sequential-isProp _ _ _

¬switched⇒sequential : (a : Arrows) → ¬ (switched a) → sequential (fw a)
¬switched⇒sequential a ¬sw m n ¬m ¬n with toSingl (end (iterate m (fw a))) | toSingl (end (iterate n (fw a))) | m ℤ.≟ n
... | src , x | src , y | w = x ∙ sym y
... | src , x | tgt , y | lt w = ⊥.rec {!!}
... | src , x | tgt , y | eq w = ⊥.rec (subst fib (sym ((sym x) ∙ cong (λ k → snd (iterate k (a , src))) w ∙ y)) tt)
  where
    fib : End → Type₀
    fib src = ⊥ 
    fib tgt = ⊤
... | src , x | tgt , y | gt w = ⊥.rec {!!}
... | tgt , x | src , y | lt w = ⊥.rec {!!}
... | tgt , x | src , y | eq w = ⊥.rec (subst fib ((sym x) ∙ cong (λ k → snd (iterate k (a , src))) w ∙ y) tt)
  where
    fib : End → Type₀
    fib src = ⊥ 
    fib tgt = ⊤
... | tgt , x | src , y | gt w = ⊥.rec {!!}
... | tgt , x | tgt , y | w = x ∙ sym y


sequential-chain-hP : Chains → hProp ℓ-zero
sequential-chain-hP c = [].elim (λ _ → isSetHProp) (λ a → sequential (fw a) , sequential-isProp _) indep c
  where
  abstract
    indep : (a b : Arrows) (r : is-reachable-arr a b) → (sequential (fw a) , sequential-isProp (fw a)) ≡ (sequential (fw b) , sequential-isProp (fw b))
    indep a b r = ΣProp≡ (λ _ → isPropIsProp) (ua (isoToEquiv i)) -- TODO
      where
        i : Iso (sequential (fw a)) (sequential (fw b))
        i = iso h k sec ret
          where
          h : sequential (fw a) → sequential (fw b)
          h seqa m n ¬m ¬n = {!!} --vu que sequential (le type but)
          --est une prop on peut éliminer r pour obtenir un entier j pour lequel iterate j (fw a) = b.
          --par subst on peut donc se ramener à prouver
          --end (iterate m (iterate j (fw a))) ≡ end (iterate n (iterate j (fw a)))
          --et donc
          -- end (iterate m + j (fw a)) ≡ end (iterate n + j (fw a)))
          -- car iterate est une action.
          -- mais seqa (m + j) (n + j) ? ? fournit une preuve de ce fait.
          -- il reste à prouver les deux ?  qui correspondent à ¬ matched (arrow (iterate (n + j) (fw a)))
          -- et ¬ matched (arrow (iterate (m + j) (fw a))) mais :
          -- ¬ matched (arrow (iterate (m + j) (fw a)) = ¬ matched (arrow (iterate m (fw b)))
          -- et ¬ matched (arrow (iterate (n + j) (fw a)) = ¬ matched (arrow (iterate n (fw b)))
          -- encore parce que iterate j (fw a) = b
          -- donc ¬n et ¬m fournissent les preuves voulues
          k : sequential (fw b) → sequential (fw a)
          k seqb m n ¬m ¬n = {!!} --idem 
          sec : section h k
          sec = {!!}  --sequential est une prop donc trivial
          ret : retract h k
          ret = {!!} --sequential est une prop donc trivial
          
sequential-chain : Chains → Type₀
sequential-chain c = fst (sequential-chain-hP c)

sequential-chain-isProp : (c : Chains) → isProp (sequential-chain c)
sequential-chain-isProp c = snd (sequential-chain-hP c)

non-matched : dArrows → Type₀
non-matched a = Σ ℤ (λ n → ¬ (matched (arrow (iterate n a))))

-- when we are sequential if a and b are two reachable arrows then b can be reached with the same direction as a
sequential→same-orientation : {o : Arrows} → sequential (fw o) → (ma mb : non-matched (fw o)) →
                              reachable-arr (arrow (iterate (fst ma) (fw o))) (arrow (iterate (fst mb) (fw o))) →
                              reachable (iterate (fst ma) (fw o)) (orient (arrow (iterate (fst mb) (fw o))) (end (iterate (fst ma) (fw o))))
sequential→same-orientation {o} seq ma mb = re
  where
  na : ℤ
  na = fst ma
  nb : ℤ
  nb = fst mb
  a : dArrows
  a = iterate (fst ma) (fw o)
  b : dArrows
  b = iterate (fst mb) (fw o)
  ra : reachable (fw o) a
  ra = na , refl
  rb : reachable (fw o) b
  rb = nb , refl
  rab : reachable a b
  rab = reachable-trans (reachable-sym ra) rb
  eab : end a ≡ end b
  eab = seq na nb (snd ma) (snd mb)
  -- in a more readable way...
  re : reachable-arr (arrow a) (arrow b) → reachable a (orient (arrow b) (end a))
  re r = subst (reachable a ∘ orient (arrow b)) (sym eab) rab

non-matched-indep : {a b : dArrows} (r : reachable a b) → non-matched b → non-matched a
non-matched-indep {a} (n , r) (m , nm) = n ℤ.+ m , N
  where
  abstract
    N = λ im → nm (subst (matched ∘ fst) (sym (iterate-+ n m a) ∙ cong (iterate m) r) im )

non-matched-op : (a : dArrows) → non-matched (op a) ≡ non-matched a
non-matched-op a = ua (isoToEquiv i)
  where
  i : Iso (non-matched (op a)) (non-matched a)
  Iso.fun i (n , r) = ℤ.neg n , (λ m → r (subst (matched ∘ fst) (sym (iterate-op n a)) m))
  Iso.inv i (n , r) = ℤ.neg n , (λ m → r (subst (matched ∘ fst) (sym (iterate-op n (op a)) ∙ cong (iterate n) (op-op a)) m))
  Iso.rightInv i (n , r) = ΣProp≡ (λ _ → isProp¬ _) (ℤ.neg-neg n)
  Iso.leftInv i (n , r) = ΣProp≡ (λ _ → isProp¬ _) (ℤ.neg-neg n)

non-matched-indep² : {a b : dArrows} (r : reachable a b) (nm : non-matched b) → non-matched-indep (reachable-sym r) (non-matched-indep r nm) ≡ nm
non-matched-indep² (n , r) (m , nm) = ΣProp≡ (λ _ → isProp¬ _) (ℤ.+-assoc (ℤ.neg n) n m ∙ cong (λ k → k ℤ.+ m) (ℤ.neg+≡0 n) ∙ ℤ.zero-+ m)

is-non-matched : dArrows → Type₀
is-non-matched a = ∥ non-matched a ∥

is-non-matched-isProp : (a : dArrows) → isProp (is-non-matched a)
is-non-matched-isProp a = propTruncIsProp

non-matched-chain-hP : Chains → hProp ℓ-zero
non-matched-chain-hP c = [].elim (λ _ → isSetHProp) (λ a → is-non-matched (fw a) , is-non-matched-isProp (fw a)) indep c
  where
  abstract
    indep : (a b : Arrows) (r : is-reachable-arr a b) → (is-non-matched (fw a) , is-non-matched-isProp (fw a)) ≡ (is-non-matched (fw b) , is-non-matched-isProp (fw b))
    indep a b r = ΣProp≡ (λ _ → isPropIsProp) (ua (isoToEquiv i))
      where
      i : Iso (is-non-matched (fw a)) (is-non-matched (fw b))
      i = iso h k sec ret
        where
        h : is-non-matched (fw a) → is-non-matched (fw b)
        h ¬a = ∣ {!!} , {!!} ∣ -- le type but
        --est une prop on peut éliminer r pour obtenir un entier j pour lequel iterate j (fw b) = a.
        --on peut également eliminer ¬a pour la même raison. on a donc un entier i tel que
        --¬ matched (arrow (iterate i (fw a)))  
        --par subst on obtient une preuve de ¬ matched (arrow (iterate i (iterate j (fw b)))
        --donc de ¬ matched (arrow (iterate (i+j) (fw b)) car iterate est une action
        --ainsi on met (i + j) dans le premier trou et la preuve obtenue plus tot dans le second
        k : is-non-matched (fw b) → is-non-matched (fw a)
        k ¬b = ∣ {!!} , {!!} ∣ --idem 
        sec : section h k
        sec = {!!}  --is-non-matched est une prop donc trivial
        ret : retract h k
        ret = {!!} --is-non-matched est une prop donc trivial

non-matched-chain : (c : Chains) → Type₀
non-matched-chain c = fst (non-matched-chain-hP c)

non-matched-chain-isProp : (c : Chains) → isProp (non-matched-chain c)
non-matched-chain-isProp c = snd (non-matched-chain-hP c)

slope : dArrows → Type₀
slope a = sequential a × is-non-matched a

slope-chain : Chains → Type₀
slope-chain c = sequential-chain c × non-matched-chain c

slope-chain-isProp : (c : Chains) → isProp (slope-chain c)
slope-chain-isProp c = isProp× (sequential-chain-isProp c) (non-matched-chain-isProp c)
