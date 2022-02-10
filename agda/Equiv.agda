{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

--- pre/post composition by equivalence is itself an equivalence
equivBiact : {ℓ : Level} {A A' B B' : Type ℓ} → A ≃ A' → B ≃ B' → (A ≃ B) ≃ (A' ≃ B')
equivBiact {_} {A} {A'} {B} {B'} fe ge = isoToEquiv i
  where
  _·_ = compEquiv
  i : Iso (A ≃ B) (A' ≃ B')
  Iso.fun i e = compEquiv (compEquiv (invEquiv fe) e) ge
  Iso.inv i e = compEquiv (compEquiv fe e) (invEquiv ge)
  Iso.rightInv i e =
    ((invEquiv fe) · ((fe · e) · (invEquiv ge))) · ge ≡⟨ cong (λ x → x · ge) (compEquiv-assoc (invEquiv fe) (fe · e) (invEquiv ge)) ⟩
    (((invEquiv fe) · (fe · e)) · (invEquiv ge)) · ge ≡⟨ cong (λ x → (x · (invEquiv ge)) · ge) (compEquiv-assoc (invEquiv fe) fe e) ⟩
    ((((invEquiv fe) · fe) · e) · (invEquiv ge)) · ge ≡⟨ cong (λ x → ((x · e) · (invEquiv ge)) · ge) (invEquiv-is-linv fe) ⟩
    ((idEquiv _ · e) · (invEquiv ge)) · ge            ≡⟨ cong (λ x → (x · (invEquiv ge)) · ge) (compEquivIdEquiv e) ⟩
    (e · (invEquiv ge)) · ge                          ≡⟨ sym (compEquiv-assoc e (invEquiv ge) ge) ⟩
    e · ((invEquiv ge) · ge)                          ≡⟨ cong (λ g → e · g) (invEquiv-is-linv ge) ⟩
    e · idEquiv _                                     ≡⟨ compEquivEquivId e ⟩
    e                                                 ∎
  Iso.leftInv i e =
    (fe · (((invEquiv fe) · e) · ge)) · (invEquiv ge) ≡⟨ cong (λ x → x · (invEquiv ge)) (compEquiv-assoc fe ((invEquiv fe) · e) ge) ⟩
    ((fe · ((invEquiv fe) · e)) · ge) · (invEquiv ge) ≡⟨ cong (λ x → (x · ge) · (invEquiv ge)) (compEquiv-assoc fe (invEquiv fe) e) ⟩
    (((fe · (invEquiv fe)) · e) · ge) · (invEquiv ge) ≡⟨ cong (λ x → ((x · e) · ge) · (invEquiv ge)) (invEquiv-is-rinv fe) ⟩
    ((idEquiv _ · e) · ge) · (invEquiv ge)            ≡⟨ cong (λ x → (x · ge) · (invEquiv ge)) (compEquivIdEquiv e) ⟩
    (e · ge) · (invEquiv ge)                          ≡⟨ sym (compEquiv-assoc e ge (invEquiv ge)) ⟩
    e · (ge · (invEquiv ge))                          ≡⟨ cong (λ x → e · x) (invEquiv-is-rinv ge) ⟩
    e · idEquiv _                                     ≡⟨ compEquivEquivId e ⟩
    e                                                 ∎

