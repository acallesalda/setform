-----------------------------------
-- First order logic
-----------------------------------

module Logic where

infix 4 _,_
infix 3 ¬_
infix 1 _∧_
infix 1 _∨_
infix 0 _⇔_

-- Some First order logic I need.

-- ∧ data type (conjunction).

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : ∀ {A B} → A ∧ B → A
∧-proj₁ (a , _) = a

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , b) = b

-- ∨ data type (disjunction), with many useful properties.

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

∨-e : (A B C : Set) → A ∨ B → (A → C) → (B → C) → C
∨-e A B C (inj₁ a) i₁ i₂ = i₁ a
∨-e A B C (inj₂ b) i₁ i₂ = i₂ b

∨-sym : (A B : Set) → A ∨ B → B ∨ A
∨-sym A B (inj₁ a) = inj₂ a
∨-sym A B (inj₂ b) = inj₁ b

trivial : (A : Set) → A → A
trivial _ A = A

∨-idem : (A : Set) → A ∨ A → A
∨-idem A (inj₁ a) = a
∨-idem A (inj₂ a) = a

∨-prop₁ : {A B C : Set} → (A ∨ B → C) → A → C
∨-prop₁ i a = i (inj₁ a)

∨-prop₂ : {A B C : Set} → (A ∨ B → C) → B → C
∨-prop₂ i b = i (inj₂ b)

∨-prop₃ : {A B C : Set} → A ∨ B → (A → C) → C ∨ B
∨-prop₃ (inj₁ x) i = inj₁ (i x)
∨-prop₃ (inj₂ x) i = inj₂ x

∨-prop₄ : {A B C : Set} → A ∨ B → (B → C) → A ∨ C
∨-prop₄ (inj₁ x) x₁ = inj₁ x
∨-prop₄ (inj₂ x) x₁ = inj₂ (x₁ x)

∨-prop₅ : {A B C D : Set} → A ∨ B → (A → C) → (B → D) → C ∨ D
∨-prop₅ (inj₁ a) a→c b→d = inj₁ (a→c a)
∨-prop₅ (inj₂ b) a→c b→d = inj₂ (b→d b)

∨-∧ : {A B : Set} → (A ∧ B) ∨ (B ∧ A) → A ∧ B
∨-∧ (inj₁ (a , b)) = a , b
∨-∧ (inj₂ (b , a)) = a , b

-- Bi-implication.

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) ∧ (B → A)

⇔-p : (A B C : Set) →  A ⇔ (B ∧ C) → (C → B) → A ⇔ C
⇔-p A B C (h₁ , h₂) h₃ = prf₁ , prf₂
  where
  prf₁ : A → C
  prf₁ A = ∧-proj₂ (h₁ A)

  prf₂ : C → A
  prf₂ C = h₂ ((h₃ C) , C)

-- Empty data type.

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data ⊤ : Set where
  <> : ⊤

-- Negation

¬_ : Set → Set
¬ A = A → ⊥

cont : (A : Set) → A ∧ ¬ A → ⊥
cont _ (x , ¬x) = ¬x x
