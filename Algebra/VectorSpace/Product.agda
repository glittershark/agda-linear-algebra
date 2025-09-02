module Algebra.VectorSpace.Product where

import Relation.Binary.Reasoning.Setoid
import Data.Vec.Properties
import Data.Vec.Relation.Binary.Equality.Setoid
open import Algebra hiding (Associative)
open import Algebra.Apartness
open import Algebra.VectorSpace.Bundles
open import Algebra.Module.Definitions
open import Data.Nat using (NonZero; ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW hiding (setoid; map)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as PropositionalEquality using (_≡_)
open import Relation.Binary.Bundles using (Setoid)
open import Level

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
zipWith-same-list (a ∷ as) f =
  cong₂ _∷_ PropositionalEquality.refl (zipWith-same-list as f)
  where open PropositionalEquality

Fⁿ : ∀ {c ℓ₁ ℓ₂} → (F : HeytingField c ℓ₁ ℓ₂) → (n : ℕ) → VectorSpaceOver F c (c ⊔ ℓ₁)
Fⁿ scalarField n =
  record
  { Vector = Vec F n
  ; _≈_ = _≈_
  ; _+_ = zipWith _+_
  ; -_ = map (-_)
  ; 0𝕍 = 0𝕍
  ; _*ₗ_ = _*ₗ_
  ; _*ᵣ_ = _*ᵣ_
  ; isVectorSpace =
    record
    { isModule =
      record
      { isBimodule =
         record
         { isBisemimodule =
           record
           { +ᴹ-isCommutativeMonoid =
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
               ; identity = zipWith-identityˡ (proj₁ +-identity) , zipWith-identityʳ (proj₂ +-identity)
               }
             ; comm = zipWith-comm (IsAbelianGroup.comm +ₛ-isAbelianGroup)
             }
           ; isPreleftSemimodule =
             record
             { *ₗ-cong = λ {x} {y} {u} {v} x≈y u≈v →
                 let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   (x *ₗ u)  ≈⟨ map-cong (*-cong x≈y) ≈-refl ⟩
                   (y *ₗ u)  ≈⟨ map-cong (*-cong ≈ₛ-refl) u≈v ⟩
                   (y *ₗ v)  ∎
             ; *ₗ-zeroˡ = λ x →
                 let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   (0# *ₗ x)        ≈⟨ map-cong (λ {x} _ → zeroˡ x) ≈-refl ⟩
                   map (λ _ → 0#) x ≡⟨ Data.Vec.Properties.map-const x 0#  ⟩
                   0𝕍               ∎
             ; *ₗ-distribʳ = *ₗ-distribʳ-+
             ; *ₗ-identityˡ = map-id (1# *_) (*-identity .proj₁)
             ; *ₗ-assoc = *ₗ-assoc
             ; *ₗ-zeroʳ = λ x →
                 let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   x *ₗ 0𝕍              ≡⟨ Data.Vec.Properties.map-replicate (_*_ x) 0# n ⟩
                   replicate n (x * 0#) ≈⟨ replicate-cong (zeroʳ x) ⟩
                   0𝕍                   ∎
             ; *ₗ-distribˡ =  *ₗ-distribˡ-+
             }
           ; isPrerightSemimodule =
             record
             { *ᵣ-cong = λ {x} {y} {u} {v} x≈y u≈v →
                 let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   (x *ᵣ u)  ≈⟨ map-cong (λ p → *-cong p ≈ₛ-refl) ≈-refl ⟩
                   (x *ᵣ u)  ≈⟨ map-cong (λ p → *-cong p u≈v) x≈y ⟩
                   (y *ᵣ v)  ∎
             ; *ᵣ-zeroʳ = λ x →
                 let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   (x *ᵣ 0#)        ≈⟨ map-cong (λ {x} _ → zeroʳ x) ≈-refl ⟩
                   map (λ _ → 0#) x ≡⟨ Data.Vec.Properties.map-const x 0#  ⟩
                   0𝕍               ∎ 
             ; *ᵣ-distribˡ = *ᵣ-distribˡ
             ; *ᵣ-identityʳ = map-id (_* 1#) (*-identity .proj₂)
             ; *ᵣ-assoc = *ᵣ-assoc
             ; *ᵣ-zeroˡ = λ x →
               let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
                   0𝕍 *ᵣ x              ≡⟨ Data.Vec.Properties.map-replicate (_* x) 0# n ⟩
                   replicate n (0# * x) ≈⟨ replicate-cong (zeroˡ x) ⟩
                   0𝕍                   ∎
             ; *ᵣ-distribʳ = *ₗ-distribʳ
             }
           ; *ₗ-*ᵣ-assoc = *ₗ-*ᵣ-assoc
           }
         ; -ᴹ‿cong = map-cong (IsGroup.⁻¹-cong (IsAbelianGroup.isGroup +ₛ-isAbelianGroup))
         ; -ᴹ‿inverse = +-leftInverse , +-rightInverse
         }
      ; *ₗ-*ᵣ-coincident = *ₗ-*ᵣ-coincident
      }
    }
  }
  where
    open HeytingField scalarField
      renaming
        ( Carrier to F
        ; +-isAbelianGroup to +ₛ-isAbelianGroup
        ; isEquivalence to +≈-isEquivalence
        ; _≈_ to _≈ₛ_
        ; refl to ≈ₛ-refl
        )

    0𝕍 = replicate n 0#
    _*ₗ_ = λ s → map (s *_)
    _*ᵣ_ = λ v s → map (_* s) v
    _≈_ = Data.Vec.Relation.Binary.Equality.Setoid._≋_ (setoid)
    ≈-setoid = Data.Vec.Relation.Binary.Equality.Setoid.≋-setoid (setoid) n
    open Setoid ≈-setoid renaming (refl to ≈-refl; trans to ≈-trans; sym to ≈-sym) hiding (_≈_)
    ≡⇒≈ : ∀ {x y} → x ≡ y → x ≈ y
    ≡⇒≈ PropositionalEquality.refl = ≈-refl
    +ₛ-isMagma = (IsAbelianGroup.isMagma +ₛ-isAbelianGroup)
    open IsAbelianGroup +ₛ-isAbelianGroup using (inverse)

    +-leftInverse : ∀ x → zipWith _+_ (map -_ x) x ≈ replicate n 0#
    +-leftInverse x = let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
      zipWith _+_ (map -_ x) x             ≡⟨⟩
      zipWith (λ a b → a + b) (map -_ x) x ≡⟨ zipWith-mapₗ x x _+_ (-_) ⟩
      zipWith (λ a b → - a + b) x x        ≡⟨ zipWith-same-list x (λ a → _+_ (- a)) ⟩
      map (λ a → - a + a) x                ≈⟨ map⁺ (λ {x = x₁} {y} z → (proj₁ inverse) x₁) (Setoid.refl ≈-setoid) ⟩
      map (λ _ → 0#) x                     ≡⟨ Data.Vec.Properties.map-const _ _ ⟩
      replicate n 0#                       ∎

    +-rightInverse : ∀ x → zipWith _+_ x (map -_ x) ≈ replicate n 0#
    +-rightInverse x = let open Relation.Binary.Reasoning.Setoid (≈-setoid) in begin
      zipWith _+_ x (map -_ x)             ≡⟨⟩
      zipWith (λ a b → a + b) x (map -_ x) ≡⟨ zipWith-mapᵣ x x _+_ (-_) ⟩
      zipWith (λ a b → a + - b) x x        ≡⟨ zipWith-same-list x _ ⟩
      map (λ a → a + - a) x                ≈⟨ map⁺ (λ {x = x₁} {y} z → (proj₂ inverse) x₁) (Setoid.refl ≈-setoid) ⟩
      map (λ _ → 0#) x                     ≡⟨ Data.Vec.Properties.map-const _ _ ⟩
      replicate n 0#                       ∎

    map-id : ∀ f → (∀ g → f g ≈ₛ g) → ∀ {n : ℕ} (xs : Vec _ n) → map f xs ≈ xs
    map-id f is-id [] = []
    map-id f is-id (x ∷ xs) = is-id x ∷ map-id f is-id xs

    map-cong
      : ∀ {f g}
      → (∀ {x y} → x ≈ₛ y → f x ≈ₛ g y)
      → {n : ℕ} {xs : Vec _ n} {ys : Vec _ n}
      → (xs ≈ ys)
      → map f xs ≈ map g ys
    map-cong f≈g {xs = []} {ys = []} xs≈ys = xs≈ys
    map-cong f≈g {xs = x ∷ xs} {ys = y ∷ ys} (x∼y ∷ xs≈ys) = f≈g x∼y ∷ map-cong f≈g xs≈ys

    replicate-cong : ∀ {x y} {n} → x ≈ₛ y → replicate n x ≈ replicate n y
    replicate-cong {n = 0} x≈y = []
    replicate-cong {n = ℕ.suc n} x≈y = x≈y ∷ replicate-cong x≈y

    map-distrib-zipWith
      : ∀ {n} (as bs : Vec _ n) f g
      → (∀ x y → f (g x y) ≈ₛ g (f x) (f y))
      → map f (zipWith g as bs) ≈ zipWith g (map f as) (map f bs)
    map-distrib-zipWith [] [] f g f-distrib-g = []
    map-distrib-zipWith (a ∷ as) (b ∷ bs) f g f-distrib-g =
      (f-distrib-g a b) ∷ map-distrib-zipWith as bs f g f-distrib-g

    *ₗ-distribʳ-+
      : ∀ {n} (v : Vec _ n) s₁ s₂
      → map ((s₁ + s₂) *_) v ≈ zipWith _+_ (map (s₁ *_) v) (map (s₂ *_) v)
    *ₗ-distribʳ-+ [] s₁ s₂ = []
    *ₗ-distribʳ-+ (x ∷ v) s₁ s₂ = distrib .proj₂ x s₁ s₂ ∷ *ₗ-distribʳ-+ v s₁ s₂

    *ₗ-distribˡ-+
      : ∀ {n} s (v₁ v₂ : Vec _ n)
      → (map (s *_) (zipWith _+_ v₁ v₂)) ≈ (zipWith _+_ (map (s *_) v₁) (map (s *_) v₂))
    *ₗ-distribˡ-+ s [] [] = []
    *ₗ-distribˡ-+ s (x₁ ∷ v₁) (x₂ ∷ v₂) = distrib .proj₁ s x₁ x₂ ∷ *ₗ-distribˡ-+ s v₁ v₂

    *ₗ-distribʳ
      : ∀ {n} s (v₁ v₂ : Vec _ n)
      → (map (_* s) (zipWith _+_ v₁ v₂)) ≈ (zipWith _+_ (map (_* s) v₁) (map (_* s) v₂))
    *ₗ-distribʳ s [] [] = []
    *ₗ-distribʳ s (x₁ ∷ v₁) (x₂ ∷ v₂) = (distrib .proj₂ s x₁ x₂) ∷ (*ₗ-distribʳ s v₁ v₂)

    *ᵣ-distribˡ : ∀ {n} (m : Vec _ n) x y → (map (_* (x + y)) m) ≈ (zipWith _+_ (map (_* x) m) (map (_* y) m))
    *ᵣ-distribˡ [] x y = []
    *ᵣ-distribˡ (m₁ ∷ m) x y = (distrib .proj₁ m₁ x y) ∷ *ᵣ-distribˡ m x y

    *ₗ-assoc
      : ∀ {n} (s₁ s₂ : F) (v : Vec F n)
      → map (s₁ * s₂ *_) v ≈ map (s₁ *_) (map (s₂ *_) v)
    *ₗ-assoc s₁ s₂ [] = []
    *ₗ-assoc s₁ s₂ (x ∷ v) = *-assoc s₁ s₂ x ∷ *ₗ-assoc s₁ s₂ v

    *ᵣ-assoc
      : ∀ {n} (v : Vec F n) (s₁ s₂ : F)
      → map (_* s₂) (map (_* s₁) v) ≈ map (_* (s₁ * s₂)) v
    *ᵣ-assoc [] s₁ s₂ = []
    *ᵣ-assoc (x ∷ v) s₁ s₂ = (*-assoc x s₁ s₂) ∷ (*ᵣ-assoc v s₁ s₂)

    *ₗ-*ᵣ-assoc : ∀ {n} x (m : Vec _ n) y → (map (_* y) (map (x *_) m)) ≈ map (x *_) (map (_* y) m)
    *ₗ-*ᵣ-assoc x [] y = []
    *ₗ-*ᵣ-assoc x (x₁ ∷ m) y = *-assoc x x₁ y ∷ *ₗ-*ᵣ-assoc x m y

    *ₗ-*ᵣ-coincident : ∀ {n} s (v : Vec _ n) → map (s *_) v ≈ map (_* s) v
    *ₗ-*ᵣ-coincident s [] = []
    *ₗ-*ᵣ-coincident s (x ∷ v) = *-comm s x ∷ *ₗ-*ᵣ-coincident s v


complexMult : ∀ {c ℓ} {F : HeytingField c ℓ} → (Fⁿ F 2) .VectorSpaceOver.Vector → Fⁿ F 2 ⇒ Fⁿ F 2
complexMult {F = F} (x₁ ∷ y₁ ∷ []) ._⇒_.T (x₂ ∷ y₂ ∷ []) =
  let open Field F in
  (x₁ ∙ x₂ - y₁ ∙ y₂) ∷ (x₁ ∙ y₂ + x₂ ∙ y₁) ∷ []
complexMult {F = F} (x₁ ∷ y₁ ∷ []) ._⇒_.linear s (x₂ ∷ y₂ ∷ []) (x₃ ∷ y₃ ∷ []) = x ∷ y ∷ []
  where
    open Field F renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
    open Relation.Binary.Reasoning.Setoid (setoid)
    x : x₁ ∙ (s ∙ x₂ + x₃) - y₁ ∙ (s ∙ y₂ + y₃)
      ≈ s ∙ (x₁ ∙ x₂ - y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
    x =
      begin
        x₁ ∙ (s ∙ x₂ + x₃) - y₁ ∙ (s ∙ y₂ + y₃)
      ≈⟨ +-cong (distribˡ _ _ _) ≈-refl ⟩
        x₁ ∙ (s ∙ x₂) + x₁ ∙ x₃ - y₁ ∙ (s ∙ y₂ + y₃)
      ≈⟨ +-assoc _ _ _ ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ (s ∙ y₂ + y₃))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (distribˡ _ _ _))) ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ (s ∙ y₂) + y₁ ∙ y₃))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (+-comm _ _))) ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ y₃ + y₁ ∙ (s ∙ y₂)))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (+-cong ≈-refl (∙-assoc _ _ _)))) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ y₃ + y₁ ∙ s ∙ y₂))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻‿+-comm _ _)) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + (⁻ (y₁ ∙ y₃) + ⁻ (y₁ ∙ s ∙ y₂)))
      ≈⟨ +-cong ≈-refl (+-assoc _ _ _) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ y₃) + ⁻ (y₁ ∙ s ∙ y₂))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (∙-cong (∙-comm _ _) ≈-refl))) ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ y₃) + ⁻ (s ∙ y₁ ∙ y₂))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (∙-assoc _ _ _))) ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ + ⁻ (y₁ ∙ y₃) + ⁻ (s ∙ (y₁ ∙ y₂)))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (∙-comm _ _))) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ y₃ + ⁻ ((y₁ ∙ y₂) ∙ s))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (∙-assoc y₁ y₂ s))) ⟩
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ y₃ + ⁻ (y₁ ∙ (y₂ ∙ s)))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻-cong (∙-assoc _ _ _))) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ y₃ + ⁻ (y₁ ∙ y₂ ∙ s))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (⁻‿*-distribˡ _ _)) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ y₃ + ⁻ (y₁ ∙ y₂) ∙ s)
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (∙-comm _ _)) ⟨
        x₁ ∙ (s ∙ x₂) + (x₁ ∙ x₃ - y₁ ∙ y₃ + s ∙ ⁻ (y₁ ∙ y₂))
      ≈⟨ +-cong ≈-refl (+-comm _ _) ⟩
        x₁ ∙ (s ∙ x₂) + (s ∙ ⁻ (y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃))
      ≈⟨ +-assoc _ _ _ ⟨
        (x₁ ∙ (s ∙ x₂)) + s ∙ ⁻ (y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
      ≈⟨ +-cong (+-cong (∙-assoc x₁ s x₂) ≈-refl) ≈-refl ⟨
        x₁ ∙ s ∙ x₂ + s ∙ ⁻ (y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
      ≈⟨ +-cong (+-cong (∙-cong (∙-comm x₁ s) ≈-refl) ≈-refl) ≈-refl ⟩
        s ∙ x₁ ∙ x₂ + s ∙ ⁻ (y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
      ≈⟨ +-cong (+-cong (∙-assoc s x₁ x₂) ≈-refl) ≈-refl ⟩
        s ∙ (x₁ ∙ x₂) + s ∙ ⁻ (y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
      ≈⟨ +-cong (distribˡ _ _ _) ≈-refl ⟨
        s ∙ (x₁ ∙ x₂ - y₁ ∙ y₂) + (x₁ ∙ x₃ - y₁ ∙ y₃)
      ∎
    y : x₁ ∙ (s ∙ y₂ + y₃) + (s ∙ x₂ + x₃) ∙ y₁
      ≈ s ∙ (x₁ ∙ y₂ + x₂ ∙ y₁) + (x₁ ∙ y₃ + x₃ ∙ y₁)
    y =
      begin
        x₁ ∙ (s ∙ y₂ + y₃) + (s ∙ x₂ + x₃) ∙ y₁
      ≈⟨ +-cong (distribˡ _ _ _) ≈-refl ⟩
        x₁ ∙ (s ∙ y₂) + x₁ ∙ y₃ + (s ∙ x₂ + x₃) ∙ y₁
      ≈⟨ +-cong ≈-refl (distribʳ _ _ _ ) ⟩
        x₁ ∙ (s ∙ y₂) + x₁ ∙ y₃ + (s ∙ x₂ ∙ y₁ + x₃ ∙ y₁)
      ≈⟨ +-cong (+-cong (∙-assoc _ _ _) ≈-refl) ≈-refl ⟨
        x₁ ∙ s ∙ y₂ + x₁ ∙ y₃ + (s ∙ x₂ ∙ y₁ + x₃ ∙ y₁)
      ≈⟨ +-cong (+-cong (∙-cong (∙-comm _ _) ≈-refl) ≈-refl) ≈-refl ⟩
        s ∙ x₁ ∙ y₂ + x₁ ∙ y₃ + (s ∙ x₂ ∙ y₁ + x₃ ∙ y₁)
      ≈⟨ +-assoc _ _ _ ⟩
        s ∙ x₁ ∙ y₂ + (x₁ ∙ y₃ + (s ∙ x₂ ∙ y₁ + x₃ ∙ y₁))
      ≈⟨ +-cong ≈-refl (+-comm _ _) ⟩
        s ∙ x₁ ∙ y₂ + (s ∙ x₂ ∙ y₁ + x₃ ∙ y₁ + x₁ ∙ y₃)
      ≈⟨ +-cong ≈-refl (+-assoc _ _ _) ⟩
        s ∙ x₁ ∙ y₂ + (s ∙ x₂ ∙ y₁ + (x₃ ∙ y₁ + x₁ ∙ y₃))
      ≈⟨ +-cong ≈-refl (+-cong (∙-assoc _ _ _) ≈-refl) ⟩
        s ∙ x₁ ∙ y₂ + (s ∙ (x₂ ∙ y₁) + (x₃ ∙ y₁ + x₁ ∙ y₃))
      ≈⟨ +-cong ≈-refl (+-cong ≈-refl (+-comm _ _)) ⟩
        s ∙ x₁ ∙ y₂ + (s ∙ (x₂ ∙ y₁) + (x₁ ∙ y₃ + x₃ ∙ y₁))
      ≈⟨ +-assoc _ _ _ ⟨
        s ∙ x₁ ∙ y₂ + s ∙ (x₂ ∙ y₁) + (x₁ ∙ y₃ + x₃ ∙ y₁)
      ≈⟨ +-cong (+-cong (∙-assoc s x₁ y₂) ≈-refl) ≈-refl ⟩
        s ∙ (x₁ ∙ y₂) + s ∙ (x₂ ∙ y₁) + (x₁ ∙ y₃ + x₃ ∙ y₁)
      ≈⟨ +-cong (distribˡ _ _ _) ≈-refl ⟨
        s ∙ (x₁ ∙ y₂ + x₂ ∙ y₁) + (x₁ ∙ y₃ + x₃ ∙ y₁)
      ∎
