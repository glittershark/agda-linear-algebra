module Algebra.VectorSpace.Operations where

open import Algebra.Apartness
open import Algebra.VectorSpace.Bundles
open import Level

-- Linear maps
record _⇒_ {c ℓ₁ ℓ₂} {S : HeytingField c ℓ₁ ℓ₂} (Vs₁ Vs₂ : VectorSpaceOver S c c) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  open VectorSpaceOver Vs₁ renaming (Vector to V₁; _*ₗ_ to _*ₗ₁_; _+_ to _+₁_)
  open VectorSpaceOver Vs₂ renaming (Vector to V₂; _*ₗ_ to _*ₗ₂_; _+_ to _+₂_; _≈_ to _≈₂_)
  field
    T : V₁ → V₂
    linear : ∀ s v₁ v₂ → T (s *ₗ₂ v₁ +₂ v₂) ≈₂ s *ₗ₂ T v₁ +₂ T v₂
