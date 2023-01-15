{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open BinaryRelation using (isEquivRel)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Z as ℤ hiding (_<_ ; _≤_ ; _≟_)
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ hiding (_>_)
open import Nat as ℕ
open import Misc
open import Cubical.HITs.PropositionalTruncation as ∥∥
open import Cubical.HITs.SetQuotients as []

open import Ends

module Bracketing {ℓ} {A B : Type ℓ} (SA : isSet A) (SB : isSet B) (isom : A × End ≃ B × End) where

open import Arrows SA SB isom

---
--- Well-bracketed chains
---

opening : ℤ
opening = ℤ.one

closing : ℤ
closing = ℤ.neg ℤ.one

-- Weight of an arrow, contrarily to Conway's paper, the convention is: → is
-- opening and ← is closing
weight : dArrows → ℤ
weight (_ , src) = opening
weight (_ , tgt) = closing

-- -- every bracket is either opening or closing and thus brings one in the total
-- -- count
-- weight-one : (x : Ends) → (weight x ≡ ℤ.one) ⊎ (weight x ≡ ℤ.neg ℤ.one)
-- weight-one (_ , src) = inl refl
-- weight-one (_ , tgt) = inr refl

-- weight-fw : (a : Arrows) → weight (fw a) ≡ opening
-- weight-fw _ = refl

weight-op : (e : dArrows) → weight (op e) ≡ ℤ.neg (weight e)
weight-op (x , src) = refl
weight-op (x , tgt) = refl

-- number of opening and closing brackets within the next n arrows
height : (n : ℕ) → dArrows → ℤ
height ℕ.zero  x = ℤ.zero
height (suc n) x = height n x ℤ.+ weight (iterate (fromℕ n) x)

abstract
  -- height is compatible with concatenation
  height-+ : (m n : ℕ) (e : Ends) → height (m ℕ.+ n) e ≡ height m e ℤ.+ height n (iterate (fromℕ m) e)
  height-+ m ℕ.zero e = cong (λ k → height k e) (ℕ.+-zero m) ∙ sym (ℤ.+-zero (height m e))
  height-+ m (suc n) e =
    height (m ℕ.+ suc n) e                                                                               ≡⟨ cong (λ k → height k e) (ℕ.+-suc m n) ⟩
    height (suc (m ℕ.+ n)) e                                                                             ≡⟨ refl ⟩
    height (m ℕ.+ n) e ℤ.+ weight (iterate (fromℕ (m ℕ.+ n)) e)                                          ≡⟨ cong (λ k → k ℤ.+ weight (iterate (fromℕ (m ℕ.+ n)) e)) (height-+ m n e) ⟩
    (height m e ℤ.+ height n (iterate (fromℕ m) e)) ℤ.+ weight (iterate (fromℕ (m ℕ.+ n)) e)             ≡⟨ ℤ.cong-+-r (height m e ℤ.+ height n (iterate (fromℕ m) e)) (cong (λ k → weight (iterate k e)) (fromℕ-+ m n)) ⟩
    (height m e ℤ.+ height n (iterate (fromℕ m) e)) ℤ.+ weight (iterate (fromℕ m ℤ.+ fromℕ n) e)         ≡⟨ ℤ.cong-+-r (height m e ℤ.+ height n (iterate (fromℕ m) e)) (cong weight (sym (iterate-+ (fromℕ m) (fromℕ n) e))) ⟩
    (height m e ℤ.+ height n (iterate (fromℕ m) e)) ℤ.+ weight (iterate (fromℕ n) (iterate (fromℕ m) e)) ≡⟨ sym (ℤ.+-assoc (height m e) _ _) ⟩
    height m e ℤ.+ (height n (iterate (fromℕ m) e) ℤ.+ weight (iterate (fromℕ n) (iterate (fromℕ m) e))) ∎

abstract
  -- the height of the opposite path
  height-op : (n : ℕ) (e : Ends) → height (suc n) (op (iterate (fromℕ n) e)) ≡ ℤ.neg (height (suc n) e)
  height-op ℕ.zero e = weight-op e
  height-op (suc n) e =
    let N = suc n in
    height (suc N) (op (iterate (fromℕ N) e)) ≡⟨ cong (λ k → height k (op (iterate (fromℕ N) e))) (sym (ℕ.+1-suc N)) ⟩
    height (N ℕ.+ 1) (op (iterate (fromℕ N) e)) ≡⟨ height-+ N 1 (op (iterate (fromℕ N) e)) ⟩
    height N (op (iterate (fromℕ N) e)) ℤ.+ height 1 (iterate (fromℕ N) (op (iterate (fromℕ N) e))) ≡⟨ refl ⟩
    height N (op (iterate (fromℕ (suc n)) e)) ℤ.+ weight (iterate (fromℕ N) (op (iterate (fromℕ N) e))) ≡⟨ {!!} ⟩ -- TODO

    height N (op (iterate (fromℕ n) e)) ℤ.+ weight (op (iterate (fromℕ N) e)) ≡⟨ cong₂ ℤ._+_ (height-op n e) (weight-op (iterate (fromℕ N) e)) ⟩
    ℤ.neg (height N e) ℤ.+ ℤ.neg (weight (iterate (fromℕ N) e))               ≡⟨ sym (neg-+ (height N e) _) ⟩
    ℤ.neg (height N e ℤ.+ weight (iterate (fromℕ N) e))                       ≡⟨ refl ⟩
    ℤ.neg (height (suc N) e)                                                  ∎

-- height-iterate : (x : Ends) → (n : ℕ) → fst (height n x) ℕ.+ snd (height n x) ≡ suc n
-- height-iterate x ℕ.zero = weight-one x
-- height-iterate x (suc n) =
 -- -- TODO: simple arithmetic
 -- fst (height n x ℤ.+ weight (next (iterate (fromℕ n) x))) ℕ.+ snd (height n x ℤ.+ weight (next (iterate (fromℕ n) x))) ≡⟨ {!!} ⟩
 -- (fst (height n x) ℕ.+ fst (weight (next (iterate (fromℕ n) x)))) ℕ.+ (snd (height n x) ℕ.+ snd (weight (next (iterate (fromℕ n) x)))) ≡⟨ {!!} ⟩
 -- suc (suc n) ∎

-- an arrow admits a matching arrow
matched : Arrows → Type₀
matched x = Σ ℕ (λ n →
  -- we take suc n to avoid considering the empty path as a match
  (height (suc n) (fw x) ≡ ℤ.zero) ×
  ((k : ℕ) → k < (suc n) → ¬ (height k (fw x) ≡ ℤ.zero))
  )

matched-isProp : (x : Arrows) → isProp (matched x)
matched-isProp x (n , z , p) (n' , z' , p') = ΣPathP (n≡n' , toPathP (ΣPathP (ℤ-isSet _ _ _ _ , isPropΠ3 (λ _ _ _ → isProp⊥) _ _)))
  where
  n≡n' : n ≡ n'
  n≡n' with n ≟ n'
  ... | lt n<n' = ⊥.elim (p' (suc n) (suc-≤-suc n<n') z)
  ... | eq n≡n' = n≡n'
  ... | gt n'<n = ⊥.elim (p (suc n') (suc-≤-suc n'<n) z')

-- matching end
match-end : {a : Arrows} → matched a → Ends
match-end {a} m = iterate (fromℕ (fst m)) (fw a)

-- matching arrow
match : {a : Arrows} → matched a → Arrows
match m = arrow (match-end m)

-- the matching arrow is reachable-arr
match-reachable-arr : {a : Arrows} (m : matched a) → reachable-arr a (match m)
match-reachable-arr m = fromℕ (fst m) , refl

match-above : {a : Arrows} (m : matched a) (n : ℕ) → n < fst m → height (suc n) (fw a) > ℤ.zero
match-above m zero n<m = 0<1
match-above {a} m (suc n) n<m with next (iterate (fromℕ n) (fw a))
... | _ , src = ℤ.≤-trans (match-above m n (<-trans ℕ.≤-refl n<m)) (ℤ.≤-trans (ℤ.≤-suc ℤ.≤-refl) (≤-path (sym (ℤ.+1-suc _))))
... | _ , tgt with (height n (fw a) ℤ.+ weight (iterate (fromℕ n) (fw a))) ℤ.≟ ℤ.one
... | lt h<1 = {!!} -- impossible because the previous height would have to be negative too
... | eq h≡1 = ⊥.elim (snd (snd m) (suc n) {!!} {!!}) -- impossible because the resulting height is zero
... | gt h>1 = {!!} -- fine
  where
  ind = match-above m n (<-trans ℕ.≤-refl n<m)

-- the matching arrow is closing
match-closing : {a : Arrows} (m : matched a) → match-end m ≡ bw (match m)
match-closing {a} m@(ℕ.zero , z , ¬z) =
  -- when n=0 the weight is 1 and thus we cannot have a match
  ⊥.elim {A = λ _ → match-end m ≡ bw (match m)} (ℤ.1≢0 (sym (ℤ.zero-+ _) ∙ z))
match-closing {a} m@(suc n , z , ¬z) with ℤ.discrete (height (suc n) (fw a)) ℤ.zero
... | yes p = ⊥.elim (¬z (suc n) ℕ.≤-refl p)
... | no ¬p =
  end≡ refl lem
    where
    -- if the end is src then the height cannot go from non-zero to zero
    lem : end (next (iterate (fromℕ n) (fw a))) ≡ tgt
    lem with Ends.case≡ (end (next (iterate (fromℕ n) (fw a))))
    ... | inl pe = ⊥.rec {!!}
    ... | inr pe = pe

-- matching is a symmetric relation
matched-sym : {a : Arrows} (m : matched a) → matched (match m)
matched-sym {a} m@(n , z , ¬z) = n , z' , λ k k<sn → ¬z' k (pred-≤-pred k<sn)
  where
  z' : height (suc n) (fw (match m)) ≡ ℤ.zero
  z' =
    height (suc n) (fw (match m))                  ≡⟨ refl ⟩
    height (suc n) (op (bw (match m)))           ≡⟨ cong (height (suc n)) (cong op (sym (match-closing m))) ⟩
    height (suc n) (op (match-end m))                 ≡⟨ refl ⟩
    height (suc n) (op (iterate (fromℕ n) (fw a))) ≡⟨ height-op n (fw a) ⟩
    ℤ.neg (height (suc n) (fw a))                  ≡⟨ cong ℤ.neg z ⟩
    ℤ.neg ℤ.zero                                      ≡⟨ refl ⟩
    ℤ.zero                                            ∎
  -- if the height was zero, the height plus a non-zero complement would be zero which is impossible
  ¬z' : (k : ℕ) → k ≤ n → ¬ (height k (fw (match (n , z , ¬z))) ≡ ℤ.zero)
  ¬z' k k≤n p = {!!}

match² : {a : Arrows} (m : matched a) → match (matched-sym m) ≡ a
match² {a} m@(n , z , ¬z) =
  match (matched-sym (n , z , ¬z))                                  ≡⟨ refl ⟩
  arrow (iterate (fromℕ n) (fw (match m)))                          ≡⟨ refl ⟩
  arrow (iterate (fromℕ n) (fw (arrow (match-end m))))              ≡⟨ cong (λ e → arrow (iterate (fromℕ n) (fw (arrow e)))) (match-closing m) ⟩
  arrow (iterate (fromℕ n) (fw (arrow (bw (match m)))))             ≡⟨ refl ⟩
  arrow (iterate (fromℕ n) (op (bw (match m))))                     ≡⟨ sym (cong (λ e → arrow (iterate (fromℕ n) (op e))) (match-closing m)) ⟩
  arrow (iterate (fromℕ n) (op (match-end m)))                      ≡⟨ refl ⟩
  arrow (iterate (fromℕ n) (op (iterate (fromℕ n) (fw a))))         ≡⟨ cong arrow (iterate-op (fromℕ n) _) ⟩
  arrow (op (iterate (ℤ.neg (fromℕ n)) (iterate (fromℕ n) (fw a)))) ≡⟨ refl ⟩
  arrow (iterate (ℤ.neg (fromℕ n)) (iterate (fromℕ n) (fw a)))      ≡⟨ cong arrow (iterate-+ (fromℕ n) (ℤ.neg (fromℕ n)) (fw a)) ⟩
  arrow (iterate (fromℕ n ℤ.- fromℕ n) (fw a))                      ≡⟨ cong (λ n → arrow (iterate n (fw a))) (n-n≡0 (fromℕ n)) ⟩
  arrow (iterate ℤ.zero (fw a))                                     ≡⟨ refl ⟩
  arrow (fw a)                                                      ≡⟨ refl ⟩
  a                                                                 ∎

-- match-indep : {a b : Arrows} → reachable-arr a b → match

well-bracketed-end : Ends → Type₀
well-bracketed-end e = (n : ℤ) → matched (arrow (iterate n e))

well-bracketed-end-isProp : (a : Ends) → isProp (well-bracketed-end a)
well-bracketed-end-isProp a = isPropΠ (λ n → matched-isProp _)

-- being well-bracketed is independent of the starting point
well-bracketed-end-indep : (a b : Ends) → reachable a b → well-bracketed-end a ≡ well-bracketed-end b
well-bracketed-end-indep a b (nr , r) = ua (isoToEquiv i)
  where
  i : Iso (well-bracketed-end a) (well-bracketed-end b)
  Iso.fun i f n = subst (matched ∘ arrow) p (f (nr ℤ.+ n))
    where
    p =
      iterate (nr ℤ.+ n) a     ≡⟨ sym (iterate-+ nr n a) ⟩
      iterate n (iterate nr a) ≡⟨ cong (iterate n) r ⟩
      iterate n b              ∎
  Iso.inv i f n = subst (matched ∘ arrow) p (f (ℤ.neg nr ℤ.+ n))
    where
    p =
      iterate (ℤ.neg nr ℤ.+ n) b              ≡⟨ sym( cong (iterate (ℤ.neg nr ℤ.+ n)) r) ⟩
      iterate (ℤ.neg nr ℤ.+ n) (iterate nr a) ≡⟨ iterate-+ nr _ a ⟩
      iterate (nr ℤ.+ (ℤ.neg nr ℤ.+ n)) a     ≡⟨ cong (λ n → iterate n a) (ℤ.+-assoc nr _ _) ⟩
      iterate ((nr ℤ.+ ℤ.neg nr) ℤ.+ n) a     ≡⟨ cong (λ m → iterate (m ℤ.+ n) a) (ℤ.n-n≡0 nr) ⟩
      iterate (ℤ.zero ℤ.+ n) a                ≡⟨ cong (λ n → iterate n a) (ℤ.zero-+ n) ⟩
      iterate n a                             ∎
  Iso.rightInv i f = funExt (λ n → matched-isProp _ _ _)
  Iso.leftInv  i f = funExt (λ n → matched-isProp _ _ _)

-- the type of well-bracketed directed chains
well-bracketed-dchain : (c : dChains) → Type₀
well-bracketed-dchain c = fst T
  where
  wb : Ends → hProp ℓ-zero
  wb a = well-bracketed-end a , well-bracketed-end-isProp a
  T : hProp ℓ-zero
  T = [].elim (λ _ → isSetHProp) wb (λ a b r → Σ≡Prop (λ _ → isPropIsProp) (well-bracketed-end-indep a b (reachable-reveal r))) c

-- being well-bracketed is independent of the direction
well-bracketed-end-op : (a : Ends) → well-bracketed-end (op a) ≡ well-bracketed-end a
well-bracketed-end-op a = ua (isoToEquiv i)
  where
  i : Iso (well-bracketed-end (op a)) (well-bracketed-end a)
  Iso.fun i f n = subst matched p (f (ℤ.neg n))
    where
    p =
      arrow (iterate (ℤ.neg n) (op a)) ≡⟨ cong arrow (iterate-neg-op n a) ⟩
      arrow (op (iterate n a))         ≡⟨ refl ⟩
      arrow (iterate n a)              ∎
  Iso.inv i f n = subst matched p (f (ℤ.neg n))
    where
    p =
      arrow (iterate (ℤ.neg n) a)   ≡⟨ cong arrow (iterate-neg n a) ⟩
      arrow (op (iterate n (op a))) ≡⟨ refl ⟩
      arrow (iterate n (op a))      ∎
  Iso.rightInv i f = funExt (λ n → matched-isProp _ _ _)
  Iso.leftInv  i f = funExt (λ n → matched-isProp _ _ _)

-- the chain of a directed arrow is well-bracketed
well-bracketed : Arrows → Type₀
well-bracketed a = well-bracketed-end (fw a)

well-bracketed-isProp : (a : Arrows) → isProp (well-bracketed a)
well-bracketed-isProp a = well-bracketed-end-isProp (fw a)

-- being well-bracketed is independent of the starting point
well-bracketed-indep : (a b : Arrows) → reachable-arr a b → well-bracketed a ≡ well-bracketed b
well-bracketed-indep a b r with reachable-arr→reachable r
... | inl r' = well-bracketed-end-indep (fw a) (fw b) r'
... | inr r' = well-bracketed-end-indep (fw a) (bw b) r' ∙ well-bracketed-end-op (fw b)

well-bracketed-chain-hProp : (c : Chains) → hProp ℓ-zero
well-bracketed-chain-hProp c = [].elim (λ _ → isSetHProp) (λ a → well-bracketed a , well-bracketed-isProp a) indep c
  where
  abstract
    indep = (λ a b r → Σ≡Prop (λ _ → isPropIsProp) (well-bracketed-indep a b (reachable-arr-reveal r)))

-- the chain of an arrow is well-bracketed
well-bracketed-chain : (c : Chains) → Type₀
well-bracketed-chain c = fst (well-bracketed-chain-hProp c)

well-bracketed-chain-isProp : (c : Chains) → isProp (well-bracketed-chain c)
well-bracketed-chain-isProp c = snd (well-bracketed-chain-hProp c)

-- matched arrows are at even distance (it is stated odd because matched takes
-- the successor of the number)
matched-odd : {a : Arrows} (m : matched a) → ℕ.is-odd (fst m)
matched-odd {a} (n , z , ¬z) with ℕ.parity n
... | inr odd = odd
... | inl even = ⊥.elim (ℤ.even-or-odd (height n (fw a)) (lem-even (fw a) n even , even-suc-inv (height n (fw a)) (subst ℤ.is-even (ℤ.+1-suc (height n (fw a))) {!!})))
  where
  even-hw : (n : ℕ) (o o' : Ends) → ℤ.is-odd (height n o) → ℤ.is-even (height n o ℤ.+ weight o')
  even-hw n o (o' , src) odd = subst ℤ.is-even (sym (ℤ.+1-suc _)) (even-suc odd)
  even-hw n o (o' , tgt) odd = subst ℤ.is-even (sym (ℤ.-1-pred _)) (even-predl odd)
  odd-hw : (n : ℕ) (o o' : Ends) → ℤ.is-even (height n o) → ℤ.is-odd (height n o ℤ.+ weight o')
  odd-hw n o (o' , src) even = subst ℤ.is-odd (sym (ℤ.+1-suc _)) (odd-suc even)
  odd-hw n o (o' , tgt) even = subst ℤ.is-odd (sym (ℤ.-1-pred _)) (odd-predl even)
  lem-even : (o : Ends) (n : ℕ) → ℕ.is-even n → ℤ.is-even (height n o)
  lem-odd  : (o : Ends) (n : ℕ) → ℕ.is-odd n → ℤ.is-odd (height n o)
  lem-even o zero p = even-zero
  lem-even o (suc n) p = even-hw n o (iterate (fromℕ n) o) (lem-odd o n (odd-pred p))
  lem-odd o zero p = ⊥.elim (¬odd-zero p)
  lem-odd o (suc n) p = odd-hw n o (iterate (fromℕ n) o) (lem-even o n (even-pred p))

-- match swaps the A/B component
match-lr : {a : Arrows} (m : matched a) → in-left a → in-right (match m)
match-lr m (is-inl a) = iterate-A-odd (is-inl a) (is-oddℕ (matched-odd m))

match-rl : {a : Arrows} (m : matched a) → in-right a → in-left (match m)
match-rl m (is-inr b) = iterate-B-odd (is-inr b) (is-oddℕ (matched-odd m))

wb-reachable-arr-matched : {a b : Arrows} → well-bracketed a → is-reachable-arr a b → matched b
wb-reachable-arr-matched wb r = ∥∥.elim (λ _ → matched-isProp _) (λ r → subst matched (snd r) (wb (fst r))) r

matching-equiv : {c : Chains} → well-bracketed-chain c → chain-A≃B c
matching-equiv {c} = [].elim
  {P = λ c → well-bracketed-chain c → chain-A≃B c}
  (λ o → isSetΠ (λ _ → chain-A≃B-isSet _))
  e
  (λ a b r → e-indep r)
  c
  where
  i : {a : Arrows} → well-bracketed a → Iso (chainA [ a ]) (chainB [ a ])
  Iso.fun (i wb) (b , l) = (match m , sym (eq/ _ _ ∣ match-reachable-arr m ∣₁) ∙ snd b) , match-lr m l
    where
    m : matched (fst b)
    m = wb-reachable-arr-matched wb (element-is-reachable-arr b)
  Iso.inv (i wb) (b , r) = (match m , sym (eq/ _ _ ∣ match-reachable-arr m ∣₁) ∙ snd b) , match-rl m r
    where
    m = wb-reachable-arr-matched wb (element-is-reachable-arr b)
  Iso.rightInv (i wb) (b , r) = Σ≡Prop (λ _ → in-right-isProp _) (Σ≡Prop (λ _ → Chains-isSet _ _) lem)
    where
    m = wb-reachable-arr-matched wb (element-is-reachable-arr b)
    -- this is essentially match² m
    lem =
      match (wb-reachable-arr-matched wb (element-is-reachable-arr (match m , (sym (eq/ _ _ ∣ match-reachable-arr m ∣₁) ∙ snd b)))) ≡⟨ cong match (matched-isProp (match m) (wb-reachable-arr-matched wb (element-is-reachable-arr (match m , (sym (eq/ _ _ ∣ match-reachable-arr m ∣₁) ∙ snd b)))) (matched-sym m)) ⟩
      match (matched-sym m) ≡⟨ match² m ⟩
      fst b ∎
  Iso.leftInv (i wb) (b , l) = Σ≡Prop (λ _ → in-left-isProp _) (Σ≡Prop (λ _ → Chains-isSet _ _) lem)
    where
    m = wb-reachable-arr-matched wb (element-is-reachable-arr b)
    lem = cong match (matched-isProp (match m) (wb-reachable-arr-matched wb (element-is-reachable-arr (match m , sym (eq/ _ _ ∣ match-reachable-arr m ∣₁) ∙ snd b))) (matched-sym m)) ∙ match² m
  e : (a : Arrows) → well-bracketed-chain [ a ] → chain-A≃B [ a ]
  e a wb = isoToEquiv (i wb)
  e-indep : {a b : Arrows} (r : is-reachable-arr a b) → PathP (λ i → cong (λ c → well-bracketed-chain c → chain-A≃B c) (eq/ a b r) i) (e a) (e b)
  e-indep {a} {b} r = toPathP (funExt (λ wb → equivEq (funExt λ { (x , l) → Σ≡Prop (λ _ → in-right-isProp _) (Σ≡Prop (λ _ → Chains-isSet _ _) (lem r wb x l)) })))
    where
    -- matching is independent of starting point
    match-indep : {a b c : Arrows} (r : is-reachable-arr a b) (wb' : well-bracketed a) (r' : is-reachable-arr a c) (wb'' : well-bracketed b) (r'' : is-reachable-arr b c) → match (wb-reachable-arr-matched wb' r') ≡ match (wb-reachable-arr-matched wb'' r'')
    match-indep {a} {b} {c} r wb' r' wb'' r'' = cong match (matched-isProp c (wb-reachable-arr-matched wb' r') (wb-reachable-arr-matched wb'' r''))
    lem : {a b : Arrows} (r : is-reachable-arr a b) (wb : well-bracketed-chain [ b ]) (c : elements [ b ]) (l : in-left (fst c)) →
          transport (λ _ → Arrows) (fst (fst (fst (e a (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb)) (transport (λ j → chainA (eq/ a b r (~ j))) (c , l)))))
          ≡ e b wb .fst (c , l) .fst .fst
    lem {a} {b} r wb c l =
      let
          wb' : well-bracketed a
          wb' = transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb
          r' : is-reachable-arr a (fst c)
          r' = subst (is-reachable-arr a) (transportRefl (fst c)) (element-is-reachable-arr (fst (transport (λ j → chainA (eq/ a b r (~ j))) (c , l))))
          wb'' : well-bracketed a
          wb'' = transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb
          r'' : is-reachable-arr a (transport (λ _ → A ⊎ B) (fst c))
          r'' = element-is-reachable-arr (fst (transport (λ j → chainA (eq/ a b r (~ j))) (c , l)))
          r''≡r' : PathP (λ i → cong (is-reachable-arr a) (transportRefl (fst c)) i) r'' r'
          r''≡r' = isOfHLevel→isOfHLevelDep 1 (is-reachable-arr-isProp a) r'' r' (transportRefl (fst c))
          wb''≡wb' : wb'' ≡ wb'
          wb''≡wb' = well-bracketed-isProp a wb'' wb'
          rm''≡rm' : PathP (λ i → cong matched (transportRefl (fst c)) i) (wb-reachable-arr-matched wb'' r'') (wb-reachable-arr-matched wb' r')
          rm''≡rm' = congP₂ {A = λ i → well-bracketed a} {B = λ i _ → is-reachable-arr a (transportRefl (fst c) i)} {C = λ i wb r → matched (transportRefl (fst c) i)}
                     (λ i wb r → wb-reachable-arr-matched (wb''≡wb' i) (r''≡r' i)) wb''≡wb' r''≡r'
          p : match (wb-reachable-arr-matched wb' r') ≡ match (wb-reachable-arr-matched wb'' r'')
          p = sym (congP (λ i → match) rm''≡rm')
      in
      transport (λ _ → Arrows) (fst (fst (fst (e a (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb)) (transport (λ j → chainA (eq/ a b r (~ j))) (c , l))))) ≡⟨ transportRefl _ ⟩
      fst (fst (fst (e a (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb)) (transport (λ j → chainA (eq/ a b r (~ j))) (c , l)))) ≡⟨ refl ⟩
      e a (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb) .fst (transport (λ j → chainA (eq/ a b r (~ j))) (c , l)) .fst .fst ≡⟨ refl ⟩
      match (wb-reachable-arr-matched (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb) (element-is-reachable-arr (fst ((transport (λ j → chainA (eq/ a b r (~ j))) (c , l)))))) ≡⟨
        subst
          (λ X → X ≡ match (wb-reachable-arr-matched wb (element-is-reachable-arr c)))
          p
          (match-indep r
            (transport (λ j → well-bracketed-chain (eq/ a b r (~ j))) wb)
            (subst (is-reachable-arr a) (transportRefl _) (element-is-reachable-arr (fst ((transport (λ j → chainA (eq/ a b r (~ j))) (c , l))))))
            wb
            (element-is-reachable-arr c))
        ⟩ -- essentially match-indep plus some transportRefl (lots of noise for not much...)
      match (wb-reachable-arr-matched wb (element-is-reachable-arr c)) ≡⟨ refl ⟩
      e b wb .fst (c , l) .fst .fst ∎

