module LinearAlgebra where

open import Algebra hiding (_DistributesOver_; LeftIdentity; RightIdentity)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Level hiding (zero)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Function
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
import Algebra.Definitions
import Relation.Binary.Reasoning.Setoid
open import Relation.Binary.Bundles using (Setoid)

PartialInverse
  : ∀ {a ℓ} {A : Set a}
  → (0# : A)
  → (1# : A)
  → (_≈_ : Rel A ℓ)
  → (_∙_ : Op₂ A)
  → (1/_ : (a : A) → {¬ (a ≈ 0#)} → A)
  → Set _
PartialInverse {A = A} 0# 1# _≈_ _∙_ 1/_
  = ∀ (a : A) → {nonzero : ¬ (a ≈ 0#)} → (((1/ a) {nonzero}) ∙ a) ≈ 1#

record Field c ℓ : Set (suc (c ⊔ ℓ))  where
  infixl 6 _+_
  infixl 7 _∙_
  infix 4 _≈_
  infix 8 1/_

  field
    Carrier  : Set c
    _≈_      : Rel Carrier ℓ
    _+_      : Op₂ Carrier
    _∙_      : Op₂ Carrier

    0#       : Carrier
    1#       : Carrier

    ⁻_       : Op₁ Carrier
    1/_      : (a : Carrier) → { ¬ a ≈ 0# } → Carrier

  _/_ : (x y : Carrier) → {¬ y ≈ 0#} → Carrier
  (x / y) {nonzero} = x ∙ ((1/ y) {nonzero})


  open Algebra.Definitions (_≈_)

  field
    +-isAbelianGroup : IsAbelianGroup _≈_ _+_ 0# ⁻_
    ∙-isCommutativeMonoid : IsCommutativeMonoid _≈_ _∙_ 1#
    ∙-inv : PartialInverse 0# 1# _≈_ _∙_ 1/_
    ∙-distrib-+ : _∙_ DistributesOver _+_

  open IsAbelianGroup +-isAbelianGroup public
    renaming
    ( assoc         to +-assoc
    ; ∙-cong        to +-cong
    ; ∙-congˡ       to +-congˡ
    ; ∙-congʳ       to +-congʳ
    ; identity      to +-identity
    ; identityˡ     to +-identityˡ
    ; identityʳ     to +-identityʳ
    ; isMagma       to +-isMagma
    ; isUnitalMagma to +-isUnitalMagma
    ; isSemigroup   to +-isSemigroup
    ; isCommutativeMagma to +-isCommutativeMagma
    ; isCommutativeSemigroup to +-isCommutativeSemigroup
    )

  open IsCommutativeMonoid ∙-isCommutativeMonoid public
    renaming
    ( isCommutativeMagma to ∙-isCommutativeMagma
    ; isCommutativeSemigroup to ∙-isCommutativeSemigroup
    )
    hiding
    ( isPartialEquivalence; reflexive; setoid; refl; sym )

module FieldTheorems {c} {ℓ} (f : Field c ℓ) where
  open Field f
  open Algebra.Definitions (_≈_)
  open import Data.Product

  A : Set c
  A = Carrier

  open Relation.Binary.Reasoning.Setoid (setoid)

  +-inj : ∀ a b c → a + b ≈ c + b → a ≈ c
  +-inj a b c plus-eq = begin
    a           ≈⟨ sym (+-identityʳ a) ⟩
    a + 0#      ≈⟨ +-cong refl (sym (inverseʳ b)) ⟩
    a + (b - b) ≈⟨ sym (+-assoc _ _ _) ⟩
    (a + b) - b ≈⟨ +-cong plus-eq refl ⟩
    (c + b) - b ≈⟨ +-assoc _ _ _ ⟩
    c + (b - b) ≈⟨ +-cong refl (inverseʳ b) ⟩
    c + 0#      ≈⟨ +-identityʳ c ⟩
    c           ∎

  0-isUniqueˡ : (0′ : A) → LeftIdentity 0′ _+_ → (0′ ≈ 0#)
  0-isUniqueˡ 0′ identityˡ = begin
    0′      ≈⟨ sym (+-identityʳ 0′) ⟩
    0′ + 0# ≈⟨ identityˡ 0# ⟩
    0# ∎

  0-isUniqueʳ : (0′ : A) → RightIdentity 0′ _+_ → (0′ ≈ 0#)
  0-isUniqueʳ 0′ identityʳ = begin
    0′      ≈⟨ sym (+-identityˡ 0′) ⟩
    0# + 0′ ≈⟨ identityʳ 0# ⟩
    0# ∎

record VectorSpace c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 6 _+_
  infixl 7 _*_
  infix 4 _≈_

  field
    ScalarField : Field c ℓ
    Vector : Set c

  open Field ScalarField hiding (Carrier) renaming (_+_ to _+ₛ_)

  Scalar : Set c
  Scalar = Field.Carrier ScalarField

  field
    _≈_ : Rel Vector (c ⊔ ℓ)
    _+_ : Op₂ Vector
    ⁻_  : Op₁ Vector
    0𝕍  : Vector

    -- TODO: better operator?
    _*_ : Scalar → Vector → Vector

    +-isAbelianGroup : IsAbelianGroup _≈_ _+_ 0𝕍 ⁻_
    *-identity : ∀ v → 1# * v ≈ v
    ∙-*-assoc : ∀ s₁ s₂ v → (s₁ ∙ s₂) * v ≈ s₁ * (s₂ * v)
    *-distribˡ-+ : ∀ s v₁ v₂ → s * (v₁ + v₂) ≈ s * v₁ + s * v₂
    *-distribʳ-+ : ∀ s₁ s₂ v → (s₁ +ₛ s₂) * v ≈ s₁ * v + s₂ * v

-- TODO: rename
module _ where
    open import Data.Nat using (NonZero; ℕ)
    open import Data.Vec
    import Data.Vec.Relation.Binary.Equality.Setoid

    Fⁿ : ∀ {c ℓ} → Field c ℓ → (n : ℕ) → .⦃ NonZero n ⦄ → VectorSpace _ _
    Fⁿ scalarField n =
      let open Field scalarField renaming (Carrier to F) in
      record
      { ScalarField = scalarField
      ; Vector = Vec F n
      ; _≈_ = Data.Vec.Relation.Binary.Equality.Setoid._≋_ (setoid)
      ; _+_ = zipWith _+_
      ; ⁻_ = map ⁻_
      ; 0𝕍 = replicate n 0#
      ; _*_ = λ s → map (s ∙_)
      ; +-isAbelianGroup = {!!}
      ; *-identity = {!!}
      ; *-distribˡ-+ = {!!}
      ; *-distribʳ-+ = {!!}
      }

module ℚ where
  open import Data.Rational using (ℚ)
  open import Data.Rational.Base as ℚ hiding (1/_)
  open import Data.Rational.Properties
  open import Relation.Binary.PropositionalEquality
  import Data.Nat as ℕ
  open import Data.Integer.Base as ℤ
    using (ℤ; +_; +0; +[1+_]; -[1+_])
    hiding (module ℤ)

  1/_ : (a : ℚ) → {¬ a ≡ 0ℚ} → ℚ
  1/_ a {nonzero} = let instance a-NonZero = ≢-nonZero nonzero in ℚ.1/ a

  ∙-inv : PartialInverse 0ℚ 1ℚ _≡_ _*_ 1/_
  ∙-inv a {nonzero} = let instance a-NonZero = ≢-nonZero nonzero in *-inverseˡ a

  ℚ-field : Field _ _
  ℚ-field = record
    { Carrier = ℚ
    ; _≈_ = _≡_
    ; _+_ = _+_
    ; _∙_ = _*_
    ; 0# = 0ℚ
    ; 1# = 1ℚ
    ; ⁻_ = -_
    ; 1/_ = 1/_
    ; +-isAbelianGroup = +-0-isAbelianGroup
    ; ∙-isCommutativeMonoid = *-1-isCommutativeMonoid
    ; ∙-inv = ∙-inv
    ; ∙-distrib-+ = *-distrib-+
    }
