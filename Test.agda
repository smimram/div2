{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.List

sum : (l : List ℕ) → ℕ
sum [] = 0
sum (x ∷ l) = x + sum l

sum++ : (l l' : List ℕ) → sum (l ++ l') ≡ sum l + sum l'
sum++ [] l' = refl
sum++ (x ∷ l) l' = cong (λ n → x + n) (sum++ l l') ∙ +-assoc x (sum l) (sum l')

-- trying to prove this simple non-obvious lemma
sum-rev : (l : List ℕ) → sum (rev l) ≡ sum l
sum-rev [] = refl
sum-rev (x ∷ l) = sum++ (rev l) (x ∷ []) ∙ +-comm (sum (rev l)) (x + 0) ∙ sym (+-assoc x 0 (sum (rev l))) ∙ cong (λ n → x + n) (sum-rev l)
