---------------------------------------------
-- Consequences of the axiom of regularity
---------------------------------------------
{-# OPTIONS --allow-unsolved-meta #-}

module Regularity where

open import Logic
open import Algebra
open import Subset
open import ZAxioms
open import Pairs

-- Theorem 105, p. 54
A∉A : (A : 𝓢) → A ∉ A
A∉A A h = cont _ (p₄ , notEmpty)
  where
  A∈Aₛ : A ∈ singleton A
  A∈Aₛ = singletonp₂ A

  A∈Aₛ∩A : A ∈ (singleton A ∩ A)
  A∈Aₛ∩A = ∩-d₂ _ _ _ (A∈Aₛ , h)

  notEmpty : (singleton A ∩ A) ≢ ∅
  notEmpty = prop-∅ A _ A∈Aₛ∩A

  Aₛ≢∅ : singleton A ≢ ∅
  Aₛ≢∅ x = prop-∅ _ _ A∈Aₛ x

  reg-step : ∃ (λ x → x ∈ singleton A ∧ ((y : 𝓢) → y ∈ x → y ∉ singleton A))
  reg-step = reg (singleton A) Aₛ≢∅

  aux : 𝓢
  aux = proj₁ reg-step

  aux-p : aux ∈ singleton A ∧ ((y : 𝓢) → y ∈ aux → y ∉ singleton A)
  aux-p = proj₂ _ reg-step

  p : aux ∈ singleton A
  p = ∧-proj₁ aux-p

  aux∈auxₛ : aux ∈ singleton aux
  aux∈auxₛ = singletonp₂ aux

  prop : A ∈ singleton aux → A ∩ singleton aux ≡ ∅
  prop = singletonp₄ A aux

  prop₂ : aux ≡ A
  prop₂ = singletonp _ p

  imp : A ∩ singleton aux ≡ ∅
  imp = prop (subs (λ w → w ∈ singleton aux) (prop₂) aux∈auxₛ)

  p₃ : singleton aux ∩ A ≡ ∅
  p₃ = subs (λ w → w ≡ ∅) (∩-sym _ _) imp

  p₄ : singleton A ∩ A ≡ ∅
  p₄ = subs (λ w → singleton w ∩ A ≡ ∅) prop₂ p₃

reg-cons : (A B : 𝓢) → ¬ (A ∈ B ∧ B ∈ A)
reg-cons A B h = {!!}
  where
  p₁ : A ∈ A ₚ B
  p₁ = pair-d₂ _ _ (inj₁ refl)

  p₂ : A ∈ B
  p₂ = ∧-proj₁ h

  p₃ : A ∈ A ₚ B ∩ B
  p₃ = ∩-d₂ _ _ _ (p₁ , p₂)

  p₄ : (A ₚ B) ≢ ∅
  p₄ = prop-∅ _ _ p₁

  reg-step : ∃ (λ x → x ∈ A ₚ B ∧ ((y : 𝓢) → y ∈ x → y ∉ A ₚ B))
  reg-step = {!!}

  x : 𝓢
  x = proj₁ reg-step

  x-p : x ∈ A ₚ B ∧ ((y : 𝓢) → y ∈ x → y ∉ A ₚ B)
  x-p = proj₂ _ reg-step

  p₆ : (A ₚ B ∩ x) ≡ ∅
  p₆ = {!!}

  p₇ : x ∈ A ₚ B
  p₇ = ∧-proj₁ x-p

  p₈ : x ≡ A ∨ x ≡ B
  p₈ = pair-d₁ _ _ p₇

-- References
--
-- Suppes, Patrick (1960). Axiomatic Set Theory.
-- The University Series in Undergraduate Mathematics.
-- D. Van Nostrand Company, inc.
--
-- Enderton, Herbert B. (1977). Elements of Set Theory.
-- Academic Press Inc.
