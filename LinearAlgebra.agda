module LinearAlgebra where

open import Algebra hiding (_DistributesOver_; LeftIdentity; RightIdentity; Congruent₁)
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
    ( isPartialEquivalence; isEquivalence; reflexive; setoid; refl; sym )

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

-- TODO: rename
module Vector where
    open import Data.Nat using (NonZero; ℕ)
    open import Data.Vec
    import Data.Vec.Relation.Binary.Equality.Setoid
    open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW hiding (setoid; map)
    open import Data.Product using (_,_; proj₁; proj₂)
    open import Relation.Binary.PropositionalEquality as PropositionalEquality using (_≡_)
    import Data.Vec.Properties
    open import Function using (id)

    zipWith-mapₗ
      : ∀ {ℓ} {A : Set ℓ} {n} (as bs : Vec A n) (f : A -> A -> A) g
      → zipWith f (map g as) bs ≡ zipWith (λ a b → f (g a) b) as bs
    zipWith-mapₗ [] [] f g = _≡_.refl
    zipWith-mapₗ (a ∷ as) (b ∷ bs) f g =
      cong₂ _∷_ PropositionalEquality.refl (zipWith-mapₗ as bs f g)
      where open PropositionalEquality

    zipWith-mapᵣ
      : ∀ {ℓ} {A : Set ℓ} {n} (as bs : Vec A n) (f : A → A → A) g
      → zipWith f as (map g bs) ≡ zipWith (λ a b → f a (g b)) as bs
    zipWith-mapᵣ [] [] f g = _≡_.refl
    zipWith-mapᵣ (a ∷ as) (b ∷ bs) f g =
      cong₂ _∷_ PropositionalEquality.refl (zipWith-mapᵣ as bs f g)
      where open PropositionalEquality

    zipWith-same-list
      : ∀ {ℓ} {A : Set ℓ} {n} (as : Vec A n) (f : A → A → A)
      → zipWith f as as ≡ map (λ a → f a a) as
    zipWith-same-list [] f = PropositionalEquality.refl
    zipWith-same-list (a ∷ as) f = PropositionalEquality.cong₂ _∷_ PropositionalEquality.refl (zipWith-same-list as f)

    Fⁿ : ∀ {c ℓ} → Field c ℓ → (n : ℕ) → .⦃ NonZero n ⦄ → VectorSpace c ℓ
    Fⁿ scalarField n =
      record
      { ScalarField = scalarField
      ; Vector = Vec F n
      ; _≈_ = _≈_
      ; _+_ = zipWith _+_
      ; ⁻_ = map ⁻_
      ; 0𝕍 = replicate n 0#
      ; _*_ = λ s → map (s ∙_)
      ; +-isAbelianGroup =
        record
          { isGroup =
              record
              { isMonoid =
                record
                { isSemigroup =
                  record
                  { isMagma =
                    record
                    { isEquivalence = PW.isEquivalence +≈-isEquivalence _
                    ; ∙-cong = zipWith-cong (IsMagma.∙-cong +ₛ-isMagma)
                    }
                  ; assoc = zipWith-assoc +-assoc }
                ; identity = zipWith-identityˡ (proj₁ +-identity) , zipWith-identityʳ (proj₂ +-identity) }
              ; inverse = +-leftInverse , +-rightInverse
              ; ⁻¹-cong = λ x → map⁺ id (PW.map (IsGroup.⁻¹-cong isGroup) x)
              }
          ; comm = zipWith-comm (IsAbelianGroup.comm +ₛ-isAbelianGroup)
          }
      ; *-identity = map-id _ (identity .proj₁)
      ; ∙-*-assoc = ∙-*-assoc
      ; *-distribˡ-+ =  λ s v₁ v₂ → map-distrib-zipWith v₁ v₂ (_∙_ s) _+_ (∙-distrib-+ .proj₁ s)
      ; *-distribʳ-+ = *-distribʳ-+ 
      }
      where
        open Field scalarField
          renaming
            ( Carrier to F
            ; +-isAbelianGroup to +ₛ-isAbelianGroup
            ; isEquivalence to +≈-isEquivalence
            ; _≈_ to _≈ₛ_)
        _≈_ = Data.Vec.Relation.Binary.Equality.Setoid._≋_ (setoid)
        ≈-setoid = Data.Vec.Relation.Binary.Equality.Setoid.≋-setoid (setoid) n
        +ₛ-isMagma = (IsAbelianGroup.isMagma +ₛ-isAbelianGroup)

        +-leftInverse : ∀ x → zipWith _+_ (map ⁻_ x) x ≈ replicate n 0#
        +-leftInverse x = let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
          zipWith _+_ (map ⁻_ x) x             ≡⟨⟩
          zipWith (λ a b → a + b) (map ⁻_ x) x ≡⟨ zipWith-mapₗ x x _+_ ⁻_ ⟩
          zipWith (λ a b → ⁻ a + b) x x        ≡⟨ zipWith-same-list x _ ⟩
          map (λ a → ⁻ a + a) x                ≈⟨ map⁺ (λ {x = x₁} {y} z → (proj₁ inverse) x₁) (Setoid.refl ≈-setoid) ⟩
          map (λ _ → 0#) x                     ≡⟨ Data.Vec.Properties.map-const _ _ ⟩
          replicate n 0#                       ∎

        +-rightInverse : ∀ x → zipWith _+_ x (map ⁻_ x) ≈ replicate n 0#
        +-rightInverse x = let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
          zipWith _+_ x (map ⁻_ x)             ≡⟨⟩
          zipWith (λ a b → a + b) x (map ⁻_ x) ≡⟨ zipWith-mapᵣ x x _+_ ⁻_ ⟩
          zipWith (λ a b → a + ⁻ b) x x        ≡⟨ zipWith-same-list x _ ⟩
          map (λ a → a + ⁻ a) x                ≈⟨ map⁺ (λ {x = x₁} {y} z → (proj₂ inverse) x₁) (Setoid.refl ≈-setoid) ⟩
          map (λ _ → 0#) x                     ≡⟨ Data.Vec.Properties.map-const _ _ ⟩
          replicate n 0#                       ∎

        map-id : ∀ f → (∀ g → f g ≈ₛ g) → ∀ {n : ℕ} (xs : Vec _ n) → map f xs ≈ xs
        map-id f is-id [] = []
        map-id f is-id (x ∷ xs) = is-id x ∷ map-id f is-id xs

        map-distrib-zipWith
          : ∀ {n} (as bs : Vec _ n) f g
          → (∀ x y → f (g x y) ≈ₛ g (f x) (f y))
          → map f (zipWith g as bs) ≈ zipWith g (map f as) (map f bs)
        map-distrib-zipWith [] [] f g f-distrib-g = []
        map-distrib-zipWith (a ∷ as) (b ∷ bs) f g f-distrib-g =
          (f-distrib-g a b) ∷ map-distrib-zipWith as bs f g f-distrib-g

        *-distribʳ-+
          : ∀ {n} s₁ s₂ (v : Vec _ n)
          → map ((s₁ + s₂) ∙_) v ≈ zipWith _+_ (map (s₁ ∙_) v) (map (s₂ ∙_) v)
        *-distribʳ-+ s₁ s₂ [] = []
        *-distribʳ-+ s₁ s₂ (x ∷ v) = ∙-distrib-+ .proj₂ x s₁ s₂ ∷ *-distribʳ-+ s₁ s₂ v

        ∙-*-assoc
          : ∀ {n} (s₁ s₂ : F) (v : Vec F n)
          → map (s₁ ∙ s₂ ∙_) v ≈ map (s₁ ∙_) (map (s₂ ∙_) v)
        ∙-*-assoc s₁ s₂ [] = []
        ∙-*-assoc s₁ s₂ (x ∷ v) = (assoc s₁ s₂ x) ∷ (∙-*-assoc s₁ s₂ v)



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
