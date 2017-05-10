module Algebra where

open import Subset
open import Logic
open import ZAxioms

infix 6 _∪_
infix 6 _-_

-- Properties involving operations between sets, algebra of sets.

-- In this module some properties involving union, difference
-- and intersection of set are proved.

-- First, some properties of the union between sets, justified by the
-- union axiom.

_∪_ : 𝓢 → 𝓢 → 𝓢
x ∪ y = proj₁ (union x y)
{-# ATP definition _∪_ #-}

-- Theorem 20, p. 27 (Suppes 1960)
∪-d : (x y : 𝓢) → ∀ {z} → z ∈ x ∪ y ⇔ z ∈ x ∨ z ∈ y
∪-d x y = proj₂ _ (union x y)

-- ∧-projections of past theorem for convenience.
∪-d₁ : (A B : 𝓢) → ∀ {x} → x ∈ (A ∪ B) → x ∈ A ∨ x ∈ B
∪-d₁ A B = ∧-proj₁ (∪-d A B)

∪-d₂ : (A B : 𝓢) → ∀ {x} → x ∈ A ∨ x ∈ B → x ∈ (A ∪ B)
∪-d₂ A B = ∧-proj₂ (∪-d A B)

-- Theorem 21, p. 27 (Suppes 1960)
A∪B≡B∪A : (A B : 𝓢) → A ∪ B ≡ B ∪ A
A∪B≡B∪A A B = equalitySubset (A ∪ B) (B ∪ A) (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ (A ∪ B) → x ∈ (B ∪ A)
  p₁ x x₁ = ∪-d₂ B A (∨-sym _ _ (∪-d₁ A B x₁))
  p₂ : (x : 𝓢) → x ∈ (B ∪ A) → x ∈ (A ∪ B)
  p₂ x x₁ = ∪-d₂ A B (∨-sym _ _ (∪-d₁ B A x₁))

-- Theorem 23, p. 27 (Suppes 1960)
A∪A≡A : (A : 𝓢) → A ∪ A ≡ A
A∪A≡A A = equalitySubset (A ∪ A) A (p₁ , p₂)
  where
  p₁ : (x :  𝓢) → x ∈ (A ∪ A) → x ∈ A
  p₁ x x₁ = ∨-idem _ (∪-d₁ A A x₁)
  p₂ : (x : 𝓢) → x ∈ A → x ∈ (A ∪ A)
  p₂ x x₁ = ∪-d₂ A A (inj₁ x₁)

-- Theorem 25, p. 27 (Suppes 1960)
∪-prop : (A B : 𝓢) → A ⊆ A ∪ B
∪-prop A B t x = ∪-d₂ _ _ (inj₁ x)

⊆∪ : (x A B : 𝓢) → x ⊆ A ∧ x ⊆ B → x ⊆ A ∪ B
⊆∪ x A B (x₁ , x₂) t x₃ = trans-⊆ _ _ _ (x₁ , (∪-prop _ _)) _ x₃

∪-prop₂ : (x A B : 𝓢) → x ⊆ A ∨ x ⊆ B → x ⊆ A ∪ B
∪-prop₂ x A B (inj₁ x₁) t x₂ = ∪-d₂ _ _ (inj₁ (x₁ _ x₂))
∪-prop₂ x A B (inj₂ x₁) t x₂ = ∪-d₂ _ _ (inj₂ (x₁ _ x₂))

∪-prop₃ : (A B : 𝓢) → B ⊆ A ∪ B
∪-prop₃ A B t x = ∪-d₂ _ _ (inj₂ x)

-- Theorem 27, p. 27 (Suppes 1960)
∪-prop₄ : (x y A : 𝓢) → x ⊆ A → y ⊆ A → x ∪ y ⊆ A
∪-prop₄ x y A x⊆A y⊆A t t∈x∪y = ∨-idem _ p₂
  where
  p₁ : t ∈ x ∨ t ∈ y
  p₁ = ∪-d₁ _ _ t∈x∪y
  p₂ : t ∈ A ∨ t ∈ A
  p₂ = ∨-prop₅ p₁ (x⊆A _) (y⊆A _)

-- Properties about the intersection opertaion. Its existence is justified
-- as an axiom derived from the sub axiom schema.

-- Instantiation of the subset axiom schema needed for justifiying
-- the operation.
sub₂ : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ z ∈ x ∧ z ∈ y))
sub₂ x y = sub (λ z → z ∈ y) x

-- Theorem 12, p.25 (Suppes 1960)
∩-def : (x y : 𝓢) → ∀ {z} → z ∈ x ∩ y ⇔ z ∈ x ∧ z ∈ y
∩-def x y = proj₂ _ (sub₂ x y)

-- Projections of ∩-def, useful for avoiding repeating this
-- projections later.
∩-d₁ : (x A B : 𝓢)  → x ∈ (A ∩ B) → x ∈ A ∧ x ∈ B
∩-d₁ x A B = ∧-proj₁ (∩-def A B)

∩-d₂ : (x A B : 𝓢) → x ∈ A ∧ x ∈ B → x ∈ (A ∩ B)
∩-d₂ x A B = ∧-proj₂ (∩-def A B)

-- Theorem 13, p.26 (Suppes 1960)
∩-sym : (A B : 𝓢) → A ∩ B ≡ B ∩ A
∩-sym A B = equalitySubset (A ∩ B) (B ∩ A) (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ A ∩ B → x ∈ B ∩ A
  p₁ x x∈A∩B = ∩-d₂ x B A (x∈B , x∈A)
    where
    x∈A : x ∈ A
    x∈A = ∧-proj₁ (∩-d₁ x A B x∈A∩B)
    x∈B : x ∈ B
    x∈B = ∧-proj₂ (∩-d₁ x A B x∈A∩B)
  p₂ : (x :  𝓢) → x ∈ B ∩ A → x ∈ A ∩ B
  p₂ x x∈B∩A = ∩-d₂ x A B (x∈A , x∈B)
    where
    x∈A : x ∈ A
    x∈A = ∧-proj₂ (∩-d₁ x B A x∈B∩A)
    x∈B : x ∈ B
    x∈B = ∧-proj₁ (∩-d₁ x B A x∈B∩A)

-- Theorem 14, p. 26 (Suppes 1960).
∩-dist : (A B C : 𝓢) → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
∩-dist A B C = equalitySubset ((A ∩ B) ∩ C) (A ∩ (B ∩ C)) (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ (A ∩ B) ∩ C → x ∈ A ∩ (B ∩ C)
  p₁ x x₁ = ∩-d₂ x A (B ∩ C) (x∈A , x∈B∩C)
    where
    x∈B∩C : x ∈ B ∩ C
    x∈B∩C = ∩-d₂ x B C (x∈B , x∈C)
      where
      x∈A∩B : x ∈ A ∩ B
      x∈A∩B = ∧-proj₁ (∩-d₁ x (A ∩ B) _ x₁)
      x∈B : x ∈ B
      x∈B = ∧-proj₂ (∩-d₁ x _ B x∈A∩B)
      x∈C : x ∈ C
      x∈C = ∧-proj₂ (∩-d₁ x _ C x₁)
    x∈A : x ∈ A
    x∈A = ∧-proj₁ (∩-d₁ x A _ x∈A∩B)
      where
      x∈A∩B : x ∈ A ∩ B
      x∈A∩B = ∧-proj₁ (∩-d₁ x (A ∩ B) _ x₁)
  p₂ : (x : 𝓢) → x ∈ A ∩ (B ∩ C) → x ∈ (A ∩ B) ∩ C
  p₂ x x₁ = ∩-d₂ x (A ∩ B) C (x∈A∩B , x∈C)
    where
    x∈A∩B : x ∈ A ∩ B
    x∈A∩B = ∩-d₂ x A B (x∈A , x∈B)
      where
      x∈A : x ∈ A
      x∈A = ∧-proj₁ (∩-d₁ x A _ x₁)
      x∈B∩C : x ∈ B ∩ C
      x∈B∩C = ∧-proj₂ (∩-d₁ x _ (B ∩ C) x₁)
      x∈B : x ∈ B
      x∈B = ∧-proj₁ (∩-d₁ x B _ x∈B∩C)
    x∈C : x ∈ C
    x∈C = ∧-proj₂ (∩-d₁ x _ C x∈B∩C)
      where
      x∈B∩C : x ∈ B ∩ C
      x∈B∩C = ∧-proj₂ (∩-d₁ x _ (B ∩ C) x₁)

-- Theorem 15, p. 26 (Suppes).
∩-itself : (A : 𝓢) → A ∩ A ≡ A
∩-itself A = equalitySubset (A ∩ A) A (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ A ∩ A → x ∈ A
  p₁ x x₁ = ∧-proj₁ (∩-d₁ _ A _ x₁)
  p₂ : (x :  𝓢) → x ∈ A → x ∈ A ∩ A
  p₂ x x₁ = ∩-d₂ _ A A (x₁ , x₁)

-- Theorem 17, p. 26 (Suppes 1960).
A∩B⊆A : (A B : 𝓢) → A ∩ B ⊆ A
A∩B⊆A A B _ p = ∧-proj₁ (∩-d₁ _ A _ p)

-- Properties involving the difference between sets. The existence of this
-- sets is also justified as an instance of the subset axiom schema.

-- Instantiation of the subset schema that will justify the operation
-- of difference between sets.
sub₃ : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ z ∈ x ∧ z ∉ y))
sub₃ x y = sub (λ z → z ∉ y) x

_-_ : 𝓢 → 𝓢 → 𝓢
x - y = proj₁ (sub₃ x y)

-- Theorem 31, p.28 (Suppes 1960).
dif-def : (x y : 𝓢) → ∀ {z} → z ∈ (x - y) ⇔ z ∈ x ∧ z ∉ y
dif-def x y = proj₂ _ (sub₃ x y)

-- Again both ∧-projections of the past theorem.
dif-d₁ : (A B z : 𝓢) → z ∈ A - B → z ∈ A ∧ z ∉ B
dif-d₁ A B z = ∧-proj₁ (dif-def A B)

dif-d₂ : (A B z : 𝓢) → z ∈ A ∧ z ∉ B → z ∈ A - B
dif-d₂ A B z = ∧-proj₂ (dif-def A B)

-- Theorem 33, p. 29 (Suppes 1960).
∩- : (A B : 𝓢) → A ∩ (A - B) ≡ A - B
∩- A B = equalitySubset (A ∩ (A - B)) (A - B) (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ A ∩ (A - B) → x ∈ A - B
  p₁ x x∈∩- = dif-d₂ A B x (x∈A , x∉B)
    where
    x∈A : x ∈ A
    x∈A = ∧-proj₁ (∩-d₁ x A _ x∈∩-)
    x∈A-B : x ∈ A - B
    x∈A-B = ∧-proj₂ (∩-d₁ x _ (A - B) x∈∩-)
    x∉B : x ∉ B
    x∉B = ∧-proj₂ (dif-d₁ A B x x∈A-B)
  p₂ : (x : 𝓢) → x ∈ A - B → x ∈ A ∩ (A - B)
  p₂ x x∈A-B = ∩-d₂ x A (A - B) ((∧-proj₁ (dif-d₁ A B x x∈A-B)) , x∈A-B)
