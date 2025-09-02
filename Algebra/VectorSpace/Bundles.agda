{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.VectorSpace.Bundles where
open import Algebra.Apartness
open import Algebra.Core
open import Algebra.Module
open import Algebra.VectorSpace.Structures
open import Level
open import Relation.Binary.Core using (Rel)

record VectorSpaceOver {s ℓ₁ ℓ₂} (scalarField : HeytingField s ℓ₁ ℓ₂) v ℓ₃ : Set (suc (v ⊔ s ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  open HeytingField scalarField renaming (_≈_ to _≈ₛ_; Carrier to Scalar; _+_ to _+ₛ_; _*_ to _*ₛ_; -_ to -ₛ_)

  infix  8 -_
  infixl 7 _*ₗ_ _*ᵣ_
  infixl 6 _+_
  infix  4 _≈_
  field
    Vector : Set v
    _≈_           : Rel Vector ℓ₃
    _+_           : Op₂ Vector
    -_            : Op₁ Vector
    _*ₗ_          : Opₗ Scalar Vector
    _*ᵣ_          : Opᵣ Scalar Vector
    0𝕍            : Vector
    isVectorSpace : IsVectorSpace scalarField _≈_ _+_ -_ _*ₗ_ _*ᵣ_ 0𝕍

record VectorSpace s v ℓ₁ ℓ₂ ℓ₃ : Set (suc (v ⊔ s ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  infix  8 -_ -ₛ_
  infixl 7 _*ₗ_ _*ᵣ_
  infixl 6 _+_
  infix  4 _≈_
  field
    Vector : Set v
    Scalar : Set s
    _≈ₛ_  : Rel Scalar ℓ₁
    _#ₛ_  : Rel Scalar ℓ₂
    _≈_  : Rel Vector ℓ₃
    _+_  : Op₂ Vector
    _+ₛ_  : Op₂ Scalar
    _*ₛ_  : Op₂ Scalar
    -_   : Op₁ Vector
    -ₛ_   : Op₁ Scalar
    0# : Scalar
    1# : Scalar
    _*ₗ_ : Opₗ Scalar Vector
    _*ᵣ_ : Opᵣ Scalar Vector
    0𝕍   : Vector
    isHeytingField : IsHeytingField _≈ₛ_ _#ₛ_ _+ₛ_ _*ₛ_ -ₛ_ 0# 1#

  scalarField : HeytingField s ℓ₁ ℓ₂
  scalarField =
    record
    { Carrier = Scalar
    ; _≈_ = _≈ₛ_
    ; _#_ = _#ₛ_
    ; _+_ = _+ₛ_
    ; _*_ = _*ₛ_
    ; -_ = -ₛ_
    ; 0# = 0#
    ; 1# = 1#
    ; isHeytingField = isHeytingField
    }

  field
    isVectorSpace : IsVectorSpace scalarField _≈_ _+_ -_ _*ₗ_ _*ᵣ_ 0𝕍

  vectorSpaceOver : VectorSpaceOver scalarField v ℓ₃
  vectorSpaceOver =
    record
    { Vector = Vector
    ; _≈_ = _≈_
    ; _+_ = _+_
    ; -_ = -_
    ; _*ₗ_ = _*ₗ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0𝕍 = 0𝕍
    ; isVectorSpace = isVectorSpace
    }
