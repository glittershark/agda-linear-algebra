module LinearAlgebra.Definitions where

open import Algebra
  hiding
  ( _DistributesOver_; LeftIdentity; RightIdentity; Congruent₁; _DistributesOverˡ_
  ; _DistributesOverʳ_; LeftZero; RightZero)
import Algebra.Definitions
import Algebra.Consequences.Setoid as Consequences
import Algebra.Properties.AbelianGroup as AbelianGroupProperties
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
import Relation.Binary.Reasoning.Setoid
open import Data.Maybe using (Maybe)
open import Level hiding (zero)
open import Tactic.RingSolver
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)
open import Data.Product using (_,_; proj₁; proj₂)

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
    0≟_      : ∀ x → Maybe (0# ≈ x)

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
    ; isCommutativeMonoid to +-isCommutativeMonoid
    ; ⁻¹-cong to ⁻-cong
    ; comm to +-comm
    )

  +-abelianGroup : AbelianGroup c ℓ
  +-abelianGroup =
    record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; _∙_ = _+_
    ; ε = 0#
    ; _⁻¹ = ⁻_
    ; isAbelianGroup = +-isAbelianGroup
    }

  open AbelianGroupProperties +-abelianGroup public
    renaming
    ( ε⁻¹≈ε            to -0#≈0#
    ; ∙-cancelˡ        to +-cancelˡ
    ; ∙-cancelʳ        to +-cancelʳ
    ; ∙-cancel         to +-cancel
    ; ⁻¹-involutive    to -‿involutive
    ; ⁻¹-injective     to -‿injective
    ; ⁻¹-anti-homo-∙   to -‿anti-homo-+
    ; identityˡ-unique to +-identityˡ-unique
    ; identityʳ-unique to +-identityʳ-unique
    ; identity-unique  to +-identity-unique
    ; inverseˡ-unique  to +-inverseˡ-unique
    ; inverseʳ-unique  to +-inverseʳ-unique
    ; ⁻¹-∙-comm        to ⁻‿+-comm
    )

  open IsCommutativeMonoid ∙-isCommutativeMonoid public
    renaming
    ( isCommutativeMagma to ∙-isCommutativeMagma
    ; isCommutativeSemigroup to ∙-isCommutativeSemigroup
    ; comm to ∙-comm
    ; assoc to ∙-assoc
    ; identity to ∙-identity
    )
    hiding
    ( isPartialEquivalence; isEquivalence; reflexive; setoid; refl; sym )

  distribˡ : _∙_ DistributesOverˡ _+_
  distribˡ = proj₁ ∙-distrib-+

  distribʳ : _∙_ DistributesOverʳ _+_
  distribʳ = proj₂ ∙-distrib-+

  zeroˡ : LeftZero 0# _∙_
  zeroˡ =  Consequences.assoc∧distribʳ∧idʳ∧invʳ⇒zeˡ setoid
    +-cong ∙-cong +-assoc distribʳ +-identityʳ inverseʳ

  zeroʳ : RightZero 0# _∙_
  zeroʳ = Consequences.assoc∧distribˡ∧idʳ∧invʳ⇒zeʳ setoid
    +-cong ∙-cong +-assoc distribˡ +-identityʳ inverseʳ

  zero : Algebra.Zero _≈_ 0# _∙_
  zero = zeroˡ , zeroʳ

  ⁻‿*-distribˡ : ∀ x y → (⁻ x) ∙ y ≈ ⁻ (x ∙ y)
  ⁻‿*-distribˡ x y = begin
    (⁻ x) ∙ y                       ≈⟨ +-identityʳ _ ⟨
    ((⁻ x) ∙ y) + 0#                ≈⟨ +-cong refl (inverseʳ _)  ⟨
    ((⁻ x) ∙ y) + (x ∙ y - x ∙ y)   ≈⟨ +-assoc _ _ _ ⟨
    ((⁻ x) ∙ y) + x ∙ y + ⁻ (x ∙ y) ≈⟨ +-cong (distribʳ _ _ _) refl ⟨
    ((⁻ x + x) ∙ y) + ⁻ (x ∙ y)     ≈⟨ +-cong (∙-cong (inverseˡ _) refl) refl ⟩
    (0# ∙ y) + ⁻ (x ∙ y)            ≈⟨ +-cong (zeroˡ _) refl ⟩
    0# + ⁻ (x ∙ y)                  ≈⟨ +-identityˡ _ ⟩
    (⁻ (x ∙ y))                     ∎
    where open Relation.Binary.Reasoning.Setoid (setoid)

  solver-ring : AlmostCommutativeRing c ℓ
  solver-ring =
    record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; _+_ = _+_
    ; _*_ = _∙_
    ; -_ = ⁻_
    ; 0# = 0#
    ; 0≟_ = 0≟_
    ; 1# = 1#
    ; isAlmostCommutativeRing =
      record
      { isCommutativeSemiring =
        record
        { isSemiring =
          record
          { isSemiringWithoutAnnihilatingZero =
            record
            { +-isCommutativeMonoid = +-isCommutativeMonoid
            ; *-cong = ∙-cong
            ; *-assoc = ∙-assoc
            ; *-identity = ∙-identity
            ; distrib = ∙-distrib-+
            }
          ; zero = zero
          }
        ; *-comm = ∙-comm
        }
      ; -‿cong = ⁻-cong
      ; -‿*-distribˡ = ⁻‿*-distribˡ
      ; -‿+-comm = ⁻‿+-comm
      }
    }
    where open Relation.Binary.Reasoning.Setoid (setoid)


record VectorSpaceOver {c} {ℓ} (ScalarField : Field c ℓ) : Set (suc (c ⊔ ℓ)) where
  infixl 6 _+_
  infixl 7 _*_
  infix 4 _≈_

  field
    Vector : Set c

  open Field ScalarField renaming (Carrier to Scalar; _+_ to _+ₛ_)

  field
    _≈_ : Rel Vector (c ⊔ ℓ)
    _+_ : Op₂ Vector
    ⁻_  : Op₁ Vector
    _*_ : Scalar → Vector → Vector
    0𝕍  : Vector

    +-isAbelianGroup : IsAbelianGroup _≈_ _+_ 0𝕍 ⁻_
    *-identity : ∀ v → 1# * v ≈ v
    ∙-*-assoc : ∀ s₁ s₂ v → (s₁ ∙ s₂) * v ≈ s₁ * (s₂ * v)
    *-distribˡ-+ : ∀ s v₁ v₂ → s * (v₁ + v₂) ≈ s * v₁ + s * v₂
    *-distribʳ-+ : ∀ s₁ s₂ v → (s₁ +ₛ s₂) * v ≈ s₁ * v + s₂ * v

record VectorSpace c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    ScalarField : Field c ℓ
    vectorSpaceOver : VectorSpaceOver ScalarField

  open VectorSpaceOver vectorSpaceOver public

-- Linear maps
record _⇒_ {c ℓ} {S : Field c ℓ} (Vs Ws : VectorSpaceOver S) : Set (suc (c ⊔ ℓ)) where
  open VectorSpaceOver Vs renaming (Vector to V; _*_ to _*̌_; _+_ to _+̌_)
  open VectorSpaceOver Ws renaming (Vector to W; _*_ to _*ʷ_; _+_ to _+ʷ_; _≈_ to _≈ʷ_)
  field
    T : V → W
    linear : ∀ s v₁ v₂ → T (s *̌ v₁ +̌ v₂) ≈ʷ s *ʷ T v₁ +ʷ T v₂
