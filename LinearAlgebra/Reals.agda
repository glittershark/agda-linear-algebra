{-# OPTIONS --guardedness #-}

module LinearAlgebra.Reals where

open import Algebra.Apartness
open import Codata.Guarded.Stream
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Properties as ℕ using ()
open import Data.Product.Base
open import Data.Rational as ℚ
  using (ℚ; 1ℚ; 0ℚ; ≢-nonZero; NonZero; >-nonZero; <-nonZero; Positive; ∣_∣)
open import Data.Rational.Properties
open import Data.Real.Base
open import Data.Real.Properties
open import Function using (case_of_)
open import Level using (0ℓ)
open import LinearAlgebra.Definitions
open import Relation.Binary
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

1ℝ : ℝ
1ℝ = fromℚ 1ℚ

record _#_ (a b : ℝ) : Set 0ℓ where
  field
    ε : ℚ
    ε-pos : Positive ε
    N : ℕ
    diverges : ∀ n → n ℕ.≥ N → ∣ a ‼ n ℚ.- b ‼ n ∣ ℚ.≥ ε

#-irrefl : Irreflexive _≈_ _#_
#-irrefl {x} {y} x≈y x#y = <-irrefl refl (begin-strict
    ε
  ≤⟨ diverges N (ℕ.≤-reflexive refl) ⟩
     ∣ x ‼ N ℚ.- y ‼ N ∣
  <⟨ proj₂ x≈yε {{!!}} {!refl!} ⟩
    ε
  ∎)
  where
    open ≤-Reasoning
    open _#_ x#y
    instance ε-Pos = ε-pos
    x≈yε = x≈y ε

#-cotrans : Cotransitive _#_
#-cotrans {x} {y} x#y z = {!!}

#-sym : Symmetric _#_
#-sym {x} {y} apart = record
  { ε = ε
  ; N = N
  ; ε-pos = ε-pos
  ; diverges = λ n n≥N →
    begin
      ε
    ≤⟨ diverges n n≥N ⟩
      ∣ (x ‼ n) ℚ.- (y ‼ n) ∣
    ≡⟨ d-sym (x ‼ n) (y ‼ n) ⟩
      ∣ (y ‼ n) ℚ.- (x ‼ n) ∣
    ∎
  }
  where
    open _#_ apart
    open ≤-Reasoning

#-isApartnessRelation : IsApartnessRelation _≈_ _#_
#-isApartnessRelation = record
  { irrefl = #-irrefl
  ; sym = #-sym
  ; cotrans = #-cotrans
  }

--     instance ε-NonZero : NonZero ε
--              ε-NonZero = >-nonZero {!!}
--     εₐ = 1ℚ/ ε
--     instance ε-pos : Positive εₐ
--              ε-pos = {!!}
--     [a] = isCauchy a εₐ

RealField : Field _ _
RealField = record
  { Carrier = ℝ
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _∙_ = _*_
  ; 0# = 0ℝ
  ; 1# = 1ℝ
  ; 0≟_ = {!!}
  ; ⁻_ = -_
  ; 1/_ = {! 1/_ !}
  ; +-isAbelianGroup = {!!}
  ; ∙-isCommutativeMonoid = {!!}
  ; ∙-inv = {!!}
  ; ∙-distrib-+ = {!!}
  }
