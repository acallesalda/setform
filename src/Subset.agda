-- Properties involving susbets and membership
-- between sets.

module Subset where

open import Logic
open import ZAxioms

memberEq : (x y z : 𝓢) → x ∈ y ∧ y ≡ z → x ∈ z
memberEq x y z (x₁ , x₂) = subs _ x₂ x₁

-- Theorem 1, p. 21 (Suppes 1960)
notInEmpty : ∀ x → x ∉ ∅
notInEmpty x h  = (proj₂ _ empt) x h

prop-∅ : (x A : 𝓢) → x ∈ A → A ≢ ∅
prop-∅ x A x∈A h = notInEmpty x (subs _ h x∈A)

prop₂-∅ : (x : 𝓢) → ∃ (λ y → y ∈ x) → x ≢ ∅
prop₂-∅ x h₁ h₂ = cont _ (h₂ , prop-∅ _ _ aux-p)
  where
  aux : 𝓢
  aux = proj₁ h₁
  aux-p : aux ∈ x
  aux-p = proj₂ _ h₁

-- Theorem 3, p. 22 (Suppes 1960)
subsetOfItself : ∀ {x} → x ⊆ x
subsetOfItself _ t∈x = t∈x

-- Theorem 4, p. 22 (Suppes 1960)
equalitySubset :  (x y : 𝓢) → x ⊆ y ∧ y ⊆ x → x ≡ y
equalitySubset x y (x⊆y , y⊆x) = ext x y ((x⊆y x) , (y⊆x x))

-- Theorem 6, p. 23 (Suppes 1960)
trans-⊆ : (x y z : 𝓢) → x ⊆ y ∧ y ⊆ z → x ⊆ z
trans-⊆ x y z (x⊆y , y⊆z) t t∈x = y⊆z t (x⊆y t t∈x)

-- Theorem 7, p. 23 (Suppes 1960)
notContainedInItself : ∀ {x} → ¬ (x ⊂ x)
notContainedInItself (_ , x≢x) = x≢x refl

-- Theorem 8, p. 23 (Suppes 1960)
nonSymmetry-⊂ : (x y : 𝓢) (p : x ⊂ y) → ¬ (y ⊂ x)
nonSymmetry-⊂ x y (x⊆y , x≢y) (y⊆x , _) = x≢y (equalitySubset x y (x⊆y , y⊆x))

-- Theorem 10, p. 23 (Suppes 1960)
⊂→⊆ : ∀ {x y} → x ⊂ y → x ⊆ y
⊂→⊆ (x⊆y , _) z z∈x = x⊆y z z∈x

prop-⊆ : (x A B : 𝓢) → x ∈ A → A ⊆ B → x ∈ B
prop-⊆ x A B x₁ x₂ = i x₁
  where
  i : x ∈ A → x ∈ B
  i = x₂ _
