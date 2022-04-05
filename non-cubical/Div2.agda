{-# OPTIONS --without-K --rewriting #-}

open import HoTT.Foundations.Prelude
open import HoTT.Foundations.Function
open import HoTT.Foundations.Equiv
open import HoTT.Foundations.Isomorphism
open import HoTT.Foundations.HLevels
open import HoTT.Relation.Nullary
open import HoTT.Relation.Nullary.DecidableEq
open import HoTT.Relation.Binary
open import HoTT.Data.Empty as ⊥
open import HoTT.Data.Unit
-- open import HoTT.Data.Nat as ℕ
open import HoTT.Data.Sigma
open import HoTT.Data.Sum
open import HoTT.HITs.PropositionalTruncation renaming (rec to ∥∥-rec)
open import HoTT.HITs.SetQuotients
open import Misc
open import Nat as ℕ

open import Z as ℤ hiding (op)
open import DiffIntNaive as ℤ' renaming (ℤ to ℤ' ; isSetℤ to isSetℤ')

-- ends of arrows : from src to tgt
data End : Set where
  src : End
  tgt : End

DiscreteEnd : Discrete End
DiscreteEnd src src = yes refl
DiscreteEnd src tgt = no (λ p → subst (λ { src → ⊤ ; tgt → ⊥ }) p tt)
DiscreteEnd tgt src = no (λ p → subst (λ { src → ⊥ ; tgt → ⊤ }) p tt)
DiscreteEnd tgt tgt = yes refl

isSetEnd : isSet End
isSetEnd = Discrete→isSet DiscreteEnd

-- swap source and target
st : End → End
st src = tgt
st tgt = src

-- double swap is identity
st² : (e : End) → st (st e) ≡ e
st² src = refl
st² tgt = refl

module _ {ℓ} {A B : Type ℓ} {isom : Iso (A × End) (B × End)} where
  f : A × End → B × End
  f = Iso.fun isom

  g : B × End → A × End
  g = Iso.inv isom

  g-f : (x : A × End) → g (f x) ≡ x
  g-f = Iso.leftInv isom

  f-g : (x : B × End) → f (g x) ≡ x
  f-g = Iso.rightInv isom

  -- swap source and target of an end
  st' : {A : Type ℓ} → A × End → A × End
  st' (x , e) = x , st e

  st'² : {A : Type ℓ} (x : A × End) → st' (st' x) ≡ x
  st'² (a , src) = refl
  st'² (a , tgt) = refl

  Arrows : Type ℓ
  Arrows = A ⊎ B

  Ends : Type ℓ
  Ends = (A × End) ⊎ (B × End)

  arrow : Ends → Arrows
  arrow (inl (a , _)) = inl a
  arrow (inr (b , _)) = inr b

  end : Ends → End
  end (inl (_ , e)) = e
  end (inr (_ , e)) = e

  -- the other end of an arrow
  op : Ends → Ends
  op (inl (a , e)) = inl (a , st e)
  op (inr (b , e)) = inr (b , st e)

  -- make the arrow point in the → direction (we begin from the source)
  start : Arrows → Ends
  start (inl a) = inl (a , src)
  start (inr b) = inr (b , src)

  -- make the arrow point in the ← direction (we begin from the end)
  costart : Arrows → Ends
  costart (inl a) = inl (a , tgt)
  costart (inr b) = inr (b , tgt)

  arrow-start : (a : Arrows) → arrow (start a) ≡ a
  arrow-start (inl a) = refl
  arrow-start (inr b) = refl

  -- next arrow: we always suppose that we are at the beginning of an arrow
  next : Ends → Ends
  next (inl x) = inr (f (st' x))
  next (inr x) = inl (g (st' x))

  prev : Ends → Ends
  prev (inl x) = inr (st' (f x))
  prev (inr x) = inl (st' (g x))

  prev-next : (x : Ends) → prev (next x) ≡ x
  prev-next (inl (a , e)) = cong (inl ∘ st') (g-f (a , st e)) ∙ cong inl (st'² (a , e))
  prev-next (inr (a , e)) = cong (inr ∘ st') (f-g (a , st e)) ∙ cong inr (st'² (a , e))

  next-prev : (x : Ends) → next (prev x) ≡ x
  next-prev (inl (a , e)) = cong inl (cong g (st'² (f (a , e))) ∙ g-f (a , e))
  next-prev (inr (a , e)) = cong inr (cong f (st'² (g (a , e))) ∙ f-g (a , e))

  -- -- iterate
  -- iterate : (n : ℤ) → Ends → Ends
  -- iterate zero x = x
  -- iterate (suc n) x = next (iterate n x)
  -- iterate (predl n) x = prev (iterate n x)
  -- iterate (predr n) x = prev (iterate n x)
  -- iterate (pred-suc n i) x = prev-next (iterate n x) i
  -- iterate (suc-predr n i) x = next-prev (iterate n x) i

  iterate : (n : ℤ) → Ends → Ends
  iterate n = ℤ.rec
    (λ x → x)
    (λ n i x → next (i x))
    (λ n i x → prev (i x))
    (λ n i x → prev (i x))
    (λ n i → funExt λ x → prev-next (i x))
    (λ n i → funExt λ x → next-prev (i x))
    n

  -- iterate-comp : (m n : ℤ) (e : Ends) → iterate m (iterate n e) ≡ iterate (m ℤ.+ n) e
  -- iterate-comp ℤ.zero n e = refl
  -- iterate-comp (suc m) n e = cong next (iterate-comp m n e)
  -- iterate-comp (predl m) n e = cong prev (iterate-comp m n e)
  -- iterate-comp (predr m) n e = cong prev (iterate-comp m n e)
  -- iterate-comp (pred-suc m i) n e = {!!}
  -- iterate-comp (suc-predr m i) n e = {!!}

  iterate-comp : (m n : ℤ) (e : Ends) → iterate m (iterate n e) ≡ iterate (m ℤ.+ n) e
  iterate-comp m n e = ℤ.elim
    (λ m → (n : ℤ) (e : Ends) → iterate m (iterate n e) ≡ iterate (m ℤ.+ n) e)
    (λ n e → refl)
    (λ m p n e → cong next (p n e))
    (λ m p n e → cong prev (p n e))
    (λ m p n e → cong prev (p n e))
    (λ m p → funExt2 λ n e → {!!})
    {!!}
    m n e

  -- left / right lemmas

  in-left-arrow : (e : Ends) → in-left (arrow e) → in-left e
  in-left-arrow (inl x) _ = is-inl x

  in-right-arrow : (e : Ends) → in-right (arrow e) → in-right e
  in-right-arrow (inr x) _ = is-inr x

  -- parity

  next-A-switch : {x : Ends} → in-left x → in-right (next x)
  next-A-switch (is-inl x) = is-inr (f (st' x))

  next-B-switch : {x : Ends} → in-right x → in-left (next x)
  next-B-switch (is-inr x) = is-inl (g (st' x))

  prev-A-switch : {x : Ends} → in-left x → in-right (prev x)
  prev-A-switch (is-inl x) = is-inr (st' (f x))

  prev-B-switch : {x : Ends} → in-right x → in-left (prev x)
  prev-B-switch (is-inr x) = is-inl (st' (g x))  

  iterate-A-even : {x : Ends} → in-left x  → {n : ℤ} → ℤ.is-even n → in-left  (iterate n x)
  iterate-A-odd  : {x : Ends} → in-left x  → {n : ℤ} → ℤ.is-odd  n → in-right (iterate n x)
  iterate-B-even : {x : Ends} → in-right x → {n : ℤ} → ℤ.is-even n → in-right (iterate n x)
  iterate-B-odd  : {x : Ends} → in-right x → {n : ℤ} → ℤ.is-odd  n → in-left  (iterate n x)
  iterate-A-even (is-inl x) even-zero = is-inl x
  iterate-A-even (is-inl x) (even-suc p) = next-B-switch (iterate-A-odd (is-inl x) p)
  iterate-A-even (is-inl x) (even-predl p) = prev-B-switch (iterate-A-odd (is-inl x) p)
  iterate-A-even (is-inl x) (even-predr p) = prev-B-switch (iterate-A-odd (is-inl x) p)
  iterate-A-odd (is-inl x)  (odd-suc p) = next-A-switch (iterate-A-even (is-inl x) p)
  iterate-A-odd (is-inl x)  (odd-predl p) = prev-A-switch (iterate-A-even (is-inl x) p)
  iterate-A-odd (is-inl x)  (odd-predr p) = prev-A-switch (iterate-A-even (is-inl x) p)
  iterate-B-even = {!!} -- TODO: same thing here
  iterate-B-odd = {!!}

  ---
  --- Chains and direction
  ---

  reachable-end : (e e' : Ends) → Type ℓ
  reachable-end e e' = Σ ℤ (λ n → e' ≡ iterate n e)

  -- reachability
  -- note that this is not a proposition, so that we often have to truncate
  reachable : (a b : Arrows) → Type ℓ
  reachable a b = Σ ℤ (λ n → b ≡ arrow (iterate n (start a)))

  is-reachable : (a b : Arrows) → Type ℓ
  is-reachable a b = ∥ reachable a b ∥

  reachable-is-equiv : BinaryRelation.isEquivRel reachable
  BinaryRelation.isEquivRel.reflexive reachable-is-equiv a = ℤ.zero , (sym (arrow-start a))
  BinaryRelation.isEquivRel.symmetric reachable-is-equiv a b (n , p) = ℤ.op n , {!!}
  BinaryRelation.isEquivRel.transitive reachable-is-equiv = {!!}

  is-reachable-is-equiv : BinaryRelation.isEquivRel is-reachable
  BinaryRelation.isEquivRel.reflexive is-reachable-is-equiv a = ∣ ℤ.zero , sym (arrow-start a) ∣
  BinaryRelation.isEquivRel.symmetric is-reachable-is-equiv a b r = ∥∥-rec propTruncIsProp {!!} r
  BinaryRelation.isEquivRel.transitive is-reachable-is-equiv = {!!}

  -- we can always find the reachability proof when there exists one (this is
  -- because ℤ is searchable)
  -- TODO: we might need the fact that ends form a set here?
  reachable-reveal : {a b : Arrows} → is-reachable a b → reachable a b
  reachable-reveal = {!!}

  -- the chain of an end
  chain-end : Ends → Type ℓ
  chain-end e = Σ Ends (reachable-end e)

  -- the chain of an arrow
  chain : Arrows → Type ℓ
  chain a = Σ Arrows λ b → ∥ reachable a b ∥

  -- the type of all chains
  Chains : Type ℓ
  Chains = Arrows / λ a b → ∥ reachable a b ∥

  -- elements of a chain
  elements : Chains → Type ℓ
  elements c = fiber [_] c

  -- every element of a chain is reachable
  element-reachable : {a : Arrows} (e : elements [ a ]) → reachable a (fst e)
  element-reachable {a} (b , p) = reachable-reveal (effective (λ _ _ → propTruncIsProp) is-reachable-is-equiv a b (sym p))

  -- end reached by an arrow
  element-end : {a : Arrows} (e : elements [ a ]) → Ends
  element-end {a} e = iterate n (start a)
    where
    n : ℤ
    n = fst (element-reachable e)

  -- the end reached by an arrow is reachable
  element-end-reachable : {a : Arrows} (e : elements [ a ]) → reachable-end (start a) (element-end e)
  element-end-reachable {a} e = fst (element-reachable e) , refl

  -- elements in A in the chain
  chainA : Chains → Type ℓ
  chainA c = Σ (elements c) λ x → in-left (fst x)

  -- elements in B in the chain
  chainB : Chains → Type ℓ
  chainB c = Σ (elements c) λ x → in-right (fst x)

  -- we have a bijection between the elements in the chain
  chain-bij : Chains → Type ℓ
  chain-bij c = Iso (chainA c) (chainB c)



  ---
  --- Well-bracketed chains
  ---

  opening : ℤ'
  opening = 1 , 0

  closing : ℤ'
  closing = 0 , 1

  -- weight of an arrow
  -- remark: → is closing and ← is opening
  weight : Ends → ℤ'
  weight (inl (_ , tgt)) = opening
  weight (inl (_ , src)) = closing
  weight (inr (_ , tgt)) = opening
  weight (inr (_ , src)) = closing

  weight-one : (x : Ends) → fst (weight x) ℕ.+ snd (weight x) ≡ 1
  weight-one (inl (_ , src)) = refl
  weight-one (inl (_ , tgt)) = refl
  weight-one (inr (_ , src)) = refl
  weight-one (inr (_ , tgt)) = refl

  -- number of opening and closing brackets
  height : (n : ℕ) → Ends → ℤ'
  height ℕ.zero x = weight x
  height (suc n) x = height n x ℤ'.+ weight (iterate (fromℕ (suc n)) x)

  height-iterate : (x : Ends) → (n : ℕ) → fst (height n x) ℕ.+ snd (height n x) ≡ suc n
  height-iterate x ℕ.zero = weight-one x
  height-iterate x (suc n) =
   -- TODO: simple arithmetic
   fst (height n x ℤ'.+ weight (next (iterate (fromℕ n) x))) ℕ.+ snd (height n x ℤ'.+ weight (next (iterate (fromℕ n) x))) ≡⟨ {!!} ⟩
   (fst (height n x) ℕ.+ fst (weight (next (iterate (fromℕ n) x)))) ℕ.+ (snd (height n x) ℕ.+ snd (weight (next (iterate (fromℕ n) x)))) ≡⟨ {!!} ⟩
   suc (suc n) ∎

  -- an arrow admits a matching arrow
  matched : Arrows → Type₀
  matched x = Σ ℕ (λ n → (height n (costart x) ≡ ℤ'.zero) × ((k : ℕ) → k < n → ¬ (height k (costart x) ≡ ℤ'.zero)))

  matched-isProp : (x : Arrows) → isProp (matched x)
  matched-isProp x (n , z , p) (n' , z' , p') = ΣPathP (n≡n' , (ΣPathP ({!!} , {!!})))
  -- i = n≡n' i , z≡z' i , p≡p' i
    where
    n≡n' : n ≡ n'
    n≡n' with n ≟ n'
    ... | lt n<n' = ⊥.elim (p' n n<n' z)
    ... | eq n≡n' = n≡n'
    ... | gt n'<n = ⊥.elim (p n' n'<n z')
    -- z≡z' : PathP (λ i → height (n≡n' i) (costart x) ≡ ℤ'.zero) z z'
    -- z≡z' = isSet→isSet' isSetℤ' z z' (cong (λ n → height n (costart x)) n≡n') refl
    -- p≡p' : PathP (λ i → (k : ℕ) → k < n≡n' i → ¬ (height k (costart x) ≡ ℤ'.zero)) p p'
    -- p≡p' = toPathP (isPropΠ3 (λ _ _ _ → isProp⊥) _  _)

  -- matching end
  match-end : {a : Arrows} → matched a → Ends
  match-end {a} m = iterate (fromℕ (fst m)) (costart a)

  -- matching arrow
  match : {a : Arrows} → matched a → Arrows
  match m = arrow (match-end m)

  -- the matching arrow is closing
  match-closing : {a : Arrows} (m : matched a) → match-end m ≡ start (match m)
  match-closing m = {!!}

  -- matching is a symmetric relation
  matched-sym : {a : Arrows} (m : matched a) → matched (match m)
  matched-sym (n , h , nh) = n , {!!} , λ k k<n → {!!}

  -- the chain of an arrow is well-bracketed
  well-bracketed : Arrows → Type₀
  well-bracketed x = (n : ℤ) → matched (arrow (iterate n (start x)))

  well-bracketed-isProp : (a : Arrows) → isProp (well-bracketed a)
  well-bracketed-isProp a = isPropΠ (λ n → matched-isProp (arrow (iterate n (start a))))

  well-bracketed-chain : Type ℓ
  well-bracketed-chain = Σ Chains λ c → (a : elements c) → matched (fst a)

  matched-odd : {a : Arrows} (m : matched a) → ℕ.is-odd (fst m)
  matched-odd = {!!}

  -- matching-fun-A' : {a : A} (m : matched (inl a)) → Σ (B × End) (λ b → inr b ≡ iterate (fromℕ (fst m)) (costart (inl a)))
  -- matching-fun-A' {a} m = get-right (iterate-A-odd (is-inl (a , tgt)) (is-oddℕ (matched-odd m))) , get-right-≡ (iterate-A-odd (is-inl (a , tgt)) (is-oddℕ (matched-odd m)))

  matching-fun-A-end : {a : A} → matched (inl a) → B × End
  matching-fun-A-end {a} m = get-right (iterate-A-odd (is-inl (a , tgt)) (is-oddℕ (matched-odd m)))

  matching-fun-A : {a : A} → matched (inl a) → B
  matching-fun-A m = fst (matching-fun-A-end m)

  matching-fun-B-end : {b : B} → matched (inr b) → A × End
  matching-fun-B-end {b} m = get-left (iterate-B-odd (is-inr (b , tgt)) (is-oddℕ (matched-odd m)))

  matching-fun-B : {b : B} → matched (inr b) → A
  matching-fun-B m = fst (matching-fun-B-end m)

  matching-fun-A-match-end : {a : A} (m : matched (inl a)) → inr (matching-fun-A-end m) ≡ match-end m
  matching-fun-A-match-end {a} m with coprod-case (match-end m)
  matching-fun-A-match-end {a} m | inl (a' , match≡a') with is-right (iterate-A-odd (is-inl (a , tgt)) (is-oddℕ (matched-odd m)))
  matching-fun-A-match-end {a} m | inl (a' , match≡a') | b , b≡match = ⊥.elim (disjoint-coprod (sym match≡a' ∙ b≡match))
  matching-fun-A-match-end {a} m | inr (b , match≡b) = inr-get-right (subst in-right (sym match≡b) (is-inr b))

  matching-fun-A-match : {a : A} (m : matched (inl a)) → inr (matching-fun-A m) ≡ match m
  matching-fun-A-match m = cong arrow (matching-fun-A-match-end m)

  -- NB: same as above
  matching-fun-B-match : {b : B} (m : matched (inr b)) → inl (matching-fun-B m) ≡ match m
  matching-fun-B-match m = {!!}

  match-A-inv : {a : A} (m : matched (inl a)) → matching-fun-B {matching-fun-A m} (subst matched (sym (matching-fun-A-match m)) (matched-sym m)) ≡ a
  match-A-inv {a} m = 
    matching-fun-B (subst matched (sym (matching-fun-A-match m)) (matched-sym m)) ≡⟨ {!!} ⟩
    a ∎

  match-B-inv : {b : B} (m : matched (inr b)) → matching-fun-A {matching-fun-B m} (subst matched (sym (matching-fun-B-match m)) (matched-sym m)) ≡ b
  match-B-inv m = {!!}

  ---
  --- Swappers
  ---

  -- -- swapper: function exchanging an arrow with the next one
  -- -- NB: this definition does not work because it depends on the parity of the "start"
  -- swapper-end : (e : Ends) → chain-end e → chain-end e
  -- swapper-end e (e' , n , r) with parity n
  -- ... | inl _ = next e' , suc  n , cong next r
  -- ... | inr _ = prev e' , pred n , cong prev r

  -- -- this is an involution
  -- swapper-end² : (e : Ends) (x : chain-end e) → swapper-end e (swapper-end e x) ≡ x
  -- swapper-end² e (e' , n , r) with parity n
  -- swapper-end² e (e' , n , r) | inl _ with parity (suc n)
  -- -- -- swapper-end² e (e' , n , r) | inl _ | inl _ = {!!} -- this case cannot happen, (if n is even then suc n cannot be even too, see even-or-odd), but I could not manage to show this even with inspect. The new "as" construct of Agda 2.6.3 might help there
  -- swapper-end² e (e' , n , r) | inl _ | inr _ = λ i → (prev-next e' i) , (pred-suc n i) ,  λ j → prev-next (r j) i
  -- swapper-end² e (e' , n , r) | inr _ with parity (pred n)
  -- swapper-end² e (e' , n , r) | inr _ | inl _ = λ i →
    -- -- TODO: this one is difficult.........
    -- next-prev e' i , suc-pred n i , {!!}
  -- swapper-end² e (e' , n , r) | inr _ | inr _ = {!!} -- impossible case because of parity

  -- swapper: function exchanging an arrow with the next one
  swapper-end : (e : Ends) → chain-end e → chain-end e
  swapper-end e (inl a , n , r) = next (inl a) , suc n  , cong next r
  swapper-end e (inr b , n , r) = prev (inr b) , pred n , cong prev r

  -- this is an involution
  swapper-end² : (e : Ends) (x : chain-end e) → swapper-end e (swapper-end e x) ≡ x
  swapper-end² e (inl a , n , r) =
    swapper-end e (swapper-end e (inl a , n , r)) ≡⟨ refl ⟩
    swapper-end e (next (inl a) , suc n , cong next r) ≡⟨ refl ⟩
    swapper-end e (inr (f (st' a)) , suc n , cong next r) ≡⟨ refl ⟩
    (prev (inr (f (st' a))) , pred (suc n) , cong prev (cong next r)) ≡⟨ refl ⟩
    (inl (st' (g (f (st' a)))) , pred (suc n) , cong prev (cong next r)) ≡⟨ ΣPathP (prev-next (inl a) , ΣPathP (lem , {!!})) ⟩
    (inl a , n , r) ∎
    where
      -- pred-suc n
      lem : fst (subst (reachable-end e) (cong (inl ∘ st') (g-f (st' a)) ∙ cong inl (st'² a)) (pred (suc n) , cong prev (cong next r))) ≡ n
      lem =
        fst (subst (reachable-end e) (cong (inl ∘ st') (g-f (st' a)) ∙ cong inl (st'² a)) (pred (suc n) , cong prev (cong next r))) ≡⟨ {!!} ⟩
        fst (subst (reachable-end e) (cong (inl ∘ st') (g-f (st' a)) ∙ cong inl (st'² a)) (pred (suc n) , cong prev (cong next r))) ≡⟨ {!!} ⟩
        n ∎
  swapper-end² e (inr b , n , r) = {!!}

  -- -- swapper exchanges polarity
  -- swapper-end-lr : (e : Ends) (x : chain-end e) → in-left (fst x) → in-right (fst (swapper-end e x))
  -- swapper-end-lr e (.(inl a) , n , r) (is-inl a) with parity n
  -- ... | inl _ = next-A-switch (is-inl _)
  -- ... | inr _ = prev-A-switch (is-inl _)

  -- swapper-end-rl : (e : Ends) (x : chain-end e) → in-right (fst x) → in-left (fst (swapper-end e x))
  -- swapper-end-rl e (.(inr b) , n , r) (is-inr b) with parity n
  -- ... | inl _ = next-B-switch (is-inr _)
  -- ... | inr _ = prev-B-switch (is-inr _)

  -- -- given an element of a chain, we can make a bijection on the chain by sending each element to the next one
  -- swapperA : (s : Arrows) (a : A) → reachable s (inl a) → B
  -- swapperA s a (n , l) = fst (get-right (swapper-end-lr (start s) (iterate n (start s) , n , refl) (in-left-arrow (iterate n (start s)) (subst in-left l (is-inl a)))))

  -- swapperA-def : (s : Arrows) (a : A) (r : reachable s (inl a)) → inr (swapperA s a r) ≡ arrow (iterate (fst r) (start s))
  -- swapperA-def s a (n , r) = {!!}

  -- swapperA-reachable : (s : Arrows) (a : A) (r : reachable s (inl a)) → reachable s (inr (swapperA s a r))
  -- swapperA-reachable s a (n , r) = {!!}

  -- swapperB : (s : Arrows) (b : B) → reachable s (inr b) → A
  -- swapperB s b (n , l) = fst (get-left (swapper-end-rl (start s) (iterate n (start s) , n , refl) (in-right-arrow (iterate n (start s)) (subst in-right l (is-inr b)))))

  -- swapperAB : (s : Arrows) (a : A) (r : reachable s (inl a)) → swapperB s (swapperA s a r) {!!} ≡ a
  -- swapperAB s a r = {!!}



  -- new try with chains

  swapper : (s : Arrows) → elements [ s ] → elements [ s ]
  swapper s e with element-end e
  ... | inl a = arrow (next (inl a)) , eq/ (arrow (next (inl a))) s ∣ {!!} ∣
  ... | inr b = {!!}

  -- swapper-chain : (s : Arrows) → chain-bij [ s ]
  -- swapper-chain s = i
    -- where
    -- i : chain-bij [ s ]
    -- Iso.fun i (a , l) = (arrow (fst (swapper-end (start s) {!!})) , {!!}) , {!!}
    -- Iso.inv i = {!!}
    -- Iso.rightInv i = {!!}
    -- Iso.leftInv i = {!!}

  ---
  --- Switched and slope chains
  ---

  switch : Arrows → Type₀
  switch a =
    (¬ (matched a)) ×
    Σ ℕ (λ n →
      let b = iterate (fromℕ n) (start a) in
      -- b is in opposite direction
      (end b ≡ tgt) ×
      -- b is not bracketed
      (¬ (matched (arrow b))) ×
      -- all intermediate elements are bracketed
      ((k : ℕ) → suc k < n → matched (arrow (iterate (fromℕ (suc k)) (start a))))
     )

  switch-isProp : (a : Arrows) → isProp (switch a)
  -- switch-isProp a (m , n , e , b , l) (m' , n' , e' , b' , l') i =
    -- isPropΠ (λ _ → isProp⊥) m m' i ,
    -- n≡n' i ,
    -- isSet→isSet' isSetEnd e e' (cong (λ n → end (iterate (fromℕ n) (start a))) n≡n') refl i ,
    -- b≡b' i ,
    -- l≡l' i
    -- where
    -- isZero : (n : ℕ) → (n ≡ ℕ.zero) ⊎ (Σ ℕ (λ k → n ≡ suc k))
    -- isZero ℕ.zero = inl refl
    -- isZero (suc n) = inr (n , refl)
    -- n≡n' : n ≡ n'
    -- n≡n' with n ≟ n'
    -- n≡n' | lt n<n' with isZero n
    -- n≡n' | lt n<n' | inl n≡0 = {!!}
    -- n≡n' | lt n<n' | inr (n' , n≡sn') = ⊥.elim (b {!l' n' ?!})
    -- n≡n' | eq n≡n' = n≡n'
    -- n≡n' | gt n'<n = ⊥.elim {!!}
    -- b≡b' : PathP (λ j → ¬ (matched (arrow (iterate (fromℕ (n≡n' j)) (start a))))) b b'
    -- b≡b' = toPathP (isPropΠ (λ _ → isProp⊥) _ _)
    -- l≡l' : PathP (λ i → ((k : ℕ) → suc k < n≡n' i → matched (arrow (iterate (fromℕ (suc k)) (start a))))) l l'
    -- l≡l' = toPathP (isPropΠ2 (λ k _ → matched-isProp (arrow (iterate (fromℕ (suc k)) (start a)))) _ _)
  switch-isProp = {!!}

  -- the chain of an arrow is switched
  -- TODO: as is this is not a proposition because we have two witnesses: we
  -- would have to choose one
  switched : Arrows → Type ℓ
  switched x = Σ ℤ (λ n →
    let e = iterate n (start x) in
      -- we have to suppose that this is left, otherwise we have two witnesses (one in A, one in B) and we don't have a proposition anymore
      in-left e ×
      switch (arrow e)
    )

  switched-isProp : (a : Arrows) → isProp (switched a)
  switched-isProp a = {!!}

  -- all non-matched arrows in the same direction
  sequential : Ends → Type₀
  sequential x = ((m n : ℤ) →
      let y = iterate m x in
      let z = iterate n x in
      ¬ (matched (arrow y)) → ¬ (matched (arrow z)) → end y ≡ end z)

  ¬switched⇒sequential : (a : Arrows) → ¬ (switched a) → sequential (start a)
  ¬switched⇒sequential = {!!}
  -- ¬switched⇒sequential a ¬sw m n ¬m ¬n with end (iterate m (start a)) | end (iterate n (start a)) | m ≟ n
  -- -- ... | u | v | w = ?

  -- we have a slope: there is a non matched element and every other element is in the same direction
  slope : Ends → Type₀
  slope x = ∥ Σ ℤ (λ n → ¬ (matched (arrow (iterate n x)))) ∥ × sequential x

  slope-isProp : (x : Ends) → isProp (slope x)
  slope-isProp x (s , t) (s' , t') = ΣPathP (squash s s' , {!isPropΠ2 (λ _ _ → isPropΠ2 λ _ _ → isSetEnd _ _) t t'!})

  ---
  --- The bijection
  ---

  data Tricho (a : Arrows) : Type ℓ where
    wb : well-bracketed a → Tricho a
    sw : switched a       → Tricho a
    sl : slope (start a)  → Tricho a

  open import Classical

  tricho : (a : Arrows) → Tricho a
  tricho a with LEM (well-bracketed-isProp a)
  ... | inl iswb = wb iswb
  ... | inr ¬wb with LEM (switched-isProp a)
  ... | inl issw = sw issw
  ... | inr ¬sw  = sl (¬∀⇒∃¬ (λ n → matched-isProp _) ¬wb , ¬switched⇒sequential a ¬sw)

  isomorphism : Iso A B
  Iso.fun isomorphism a with tricho (inl a)
  ... | wb iswb = matching-fun-A (iswb ℤ.zero)
  ... | sw issw = {!!}
  ... | sl issl = {!!}
  Iso.inv isomorphism = {!!}
  Iso.rightInv isomorphism = {!!}
  Iso.leftInv isomorphism = {!!}
