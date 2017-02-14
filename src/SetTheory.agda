------------------------------------------
-- Set theory formalization
------------------------------------------

module SetTheory where

infix 5 _⊆_
infix 5 _∈_ _∉_
infix 4 _≡_
infix 4 _,_
infix 3 ¬_
infix 2 _∧_
infix 2 ∃
infix 1 _∨_
infix 0 _⇔_

-- 0ur Sets will be called denoted by 𝓢. This is
-- our universe of discourse. Membership of set
-- is also a primitive notion. That letter is
-- written by "\MCS"

postulate
  𝓢 : Set
  _∈_ : 𝓢 → 𝓢 → Set

------------------------------------------
-- Some First order logic I need.

-- ∧ data type (conjunction).

data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : ∀ {A B} → A ∧ B → A
∧-proj₁ (a , _) = a

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , b) = b

-- ∨ data type (disjunction).

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

-- Bi-implication.

_⇔_ : Set → Set → Set
A ⇔ B = (A → B) ∧ (B → A)

-- Empty data type.

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Negation

¬_ : Set → Set
¬ A = A → ⊥

-- Existential quantifier

data ∃ (A : 𝓢 → Set) : Set where
  _,_ : (t : 𝓢) → A t → ∃ A

-- Sugar syntax for the existential quantifier.

syntax ∃ (λ x → e) = ∃[ x ] e

-------------------------------------------

-- Equivalence and non equivalence

data _≡_ (x : 𝓢) : 𝓢 → Set where
  refl : x ≡ x

_≢_ : 𝓢 → 𝓢 → Set
x ≢ y = ¬ x ≡ y


-- Definitions of subset and not-membership.

_⊆_ : 𝓢 → 𝓢 → Set
x ⊆ y = ∀ {t} → t ∈ x → t ∈ y

_∉_ : 𝓢 → 𝓢 → Set
x ∉ y = ¬ (x ∈ y)

-------------------------------------------

-- The Axioms
-- ext (Extensionality) : If two sets have exactly the same members, they are equal.
-- empt (Empty Set Axiom) : There is a set having no members.
-- pair (Pairing Axiom) : For any sets y and z, there is a set having as members
-- just y and z.
-- pow (Power Set Axiom): For any x there is a set whose members are exactly the subsets
-- of x.
-- sub (Subset Axiom, or Specification Axiom): This axiom asserts the existence of a set
-- B whose members are exactly those sets x in y such that they satisfy certain property.
-- uni (Union Axiom) : For any set x, there exists a set A whose elements are exactly
-- the members of x.
-- The other three axioms are yet to implement.

postulate
  x y z : 𝓢
  ext  : ∀ {x y} → ∀ {z} → z ∈ x ⇔ z ∈ y → x ≡ y
  empt : ∀ {x} →  (∃ B : 𝓢) → x ∉ B
  pair : ∀ {y z} → (∃ B : 𝓢) → ∀ {x} → x ∈ B ⇔ (x ≡ y ∨ x ≡ z)
  pow  : ∀ {x} → (∃ B : 𝓢) → ∀ {y} → y ∈ B ⇔ y ⊆ x
  sub  : (A : 𝓢 → Set) → ∀ {y} → (∃ B : 𝓢) → ∀ {x} → x ∈ B ⇔ (x ∈ y ∧ A y)
  uni  : ∀ {z} → (∃ A : 𝓢) → ∀ {y x} → x ∈ y ∧ y ∈ z → x ∈ A
------------------------------------------

-- ∅ : 𝓢
-- ∅ =

