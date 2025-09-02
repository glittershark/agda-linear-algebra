{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.VectorSpace.Structures where

open import Algebra
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Apartness
open import Algebra.Module
open import Relation.Binary.Core using (Rel)
open import Level using (_⊔_)

module _ {s ℓ₁ ℓ₂} (overField : HeytingField s ℓ₁ ℓ₂) where
  open HeytingField overField renaming (_≈_ to _≈ₛ_; Carrier to Scalar; _+_ to _+ₛ_; _*_ to _*ₛ_; -_ to -ₛ_)

  record IsVectorSpace {v ℓ₃} {Vector : Set v} (_≈_ : Rel Vector ℓ₃)
                       (_+_ : Op₂ Vector) (-_ : Op₁ Vector) (_*ₗ_ : Opₗ Scalar Vector)
                       (_*ᵣ_ : Opᵣ Scalar Vector) (0𝕍 : Vector) : Set (v ⊔ s ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    scalarCommutativeRing : CommutativeRing s ℓ₁
    scalarCommutativeRing =
      record
      { Carrier = Scalar
      ; _≈_ = _≈ₛ_
      ; _+_ = _+ₛ_
      ; _*_ = _*ₛ_
      ; -_ = -ₛ_
      ; 0# = 0#
      ; 1# = 1#
      ; isCommutativeRing = isCommutativeRing
      }
    field
      isModule : IsModule scalarCommutativeRing _≈_ _+_ 0𝕍 -_ _*ₗ_ _*ᵣ_
