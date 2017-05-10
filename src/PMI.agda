------------------------------------------
-- Mathematical induction derived from Z
------------------------------------------

module PMI where

open import Logic
open import ZAxioms
open import Algebra
open import Subset
open import Pairs

-- Axiom of infinity
postulate
  infinity : ∃ (λ I → ∅ ∈ I ∧ ∀ x → x ∈ I → x ∪ singleton x ∈ I)

succ : 𝓢 → 𝓢
succ x = x ∪ singleton x

-- Inductive property
Inductive : 𝓢 → Set
Inductive A = ∅ ∈ A ∧ ((x : 𝓢) → x ∈ A → succ x ∈ A)

-- An inductive set.
I : 𝓢
I = proj₁ infinity

formulaN : 𝓢 → Set
formulaN x = (A : 𝓢) → Inductive A → x ∈ A

fullN : ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ z ∈ I ∧ formulaN z)
fullN = sub formulaN I

ℕ : 𝓢
ℕ = proj₁ fullN

x∈ℕ→x∈InductiveSet : (x : 𝓢) → x ∈ ℕ → (A : 𝓢) → Inductive A → x ∈ A
x∈ℕ→x∈InductiveSet x h = ∧-proj₂ (∧-proj₁ (proj₂ _ fullN) h)

-- PMI version from Ivorra Castillo (n.d.), Teorema 8.13.
PMI : (A : 𝓢) → A ⊆ ℕ → ∅ ∈ A → ((n : 𝓢) → n ∈ A → succ n ∈ A) → A ≡ ℕ
PMI A h₁ h₂ h₃ = equalitySubset A ℕ (prf₁ , prf₂)
  where
    prf₁ : (z : 𝓢) → z ∈ A → z ∈ ℕ
    prf₁ z h = h₁ z h
    inductiveA : Inductive A
    inductiveA = h₂ , h₃
    prf₂ : (z : 𝓢) → z ∈ ℕ → z ∈ A
    prf₂ z h = x∈ℕ→x∈InductiveSet z h A inductiveA

-- References
--
-- Suppes, Patrick (1960). Axiomatic Set Theory.
-- The University Series in Undergraduate Mathematics.
-- D. Van Nostrand Company, inc.
--
-- Enderton, Herbert B. (1977). Elements of Set Theory.
-- Academic Press Inc.
--
-- Ivorra Castillo, Carlos (n.d.). Lógica y Teoría de
-- Conjuntos. https://www.uv.es/ivorra/
