-------------------------------------------------
-- Formalisation of the Z axioms of set theory.
-------------------------------------------------
infix 1 ∃
infix 6 _∩_
infix 5 _⊆_
infix 5 _∈_ _∉_
infix 4 _≡_

module ZAxioms where

open import Logic

-- The universe of discourse (pure sets) and the membership
-- relationship. (The letter 𝓢 is type by "\MCS")
postulate
  𝓢   : Set
  _∈_ : 𝓢 → 𝓢 → Set

-- Existential quantifier

data ∃ (A : 𝓢 → Set) : Set where
  _,_ : (t : 𝓢) → A t → ∃ A

-- Sugar syntax for the existential quantifier.

syntax ∃ (λ x → e) = ∃[ x ] e

-- Existential projections.

proj₁ : {A : 𝓢 → Set} → ∃ A → 𝓢
proj₁ (t , _) = t

proj₂ : (A : 𝓢 → Set) → (foo : ∃ A)  → A (proj₁ foo)
proj₂ A (_ , Ax) = Ax

-- Equivalence and non equivalence with some useful properties

data _≡_ (x : 𝓢) : 𝓢 → Set where
  refl : x ≡ x

_≢_ : 𝓢 → 𝓢 → Set
x ≢ y = ¬ x ≡ y

sym : (x y : 𝓢) → x ≡ y → y ≡ x
sym x .x refl = refl

cong : (f :  𝓢 → 𝓢) {x y : 𝓢} → x ≡ y → f x ≡ f y
cong f refl = refl

subs : (P : 𝓢 → Set) {x y : 𝓢} (p : x ≡ y) (h : P x) → P y
subs P {x} {.x} refl h = h

trans : {x y z : 𝓢} → x ≡ y →  y ≡ z → x ≡ z
trans refl refl = refl

-- Property concerning bi-implication, needed in a proof.
⇔-p₂ : (z : 𝓢) → {A B C : Set} →  A ⇔ (B ∧ C) → (C → B) → A ⇔ C
⇔-p₂ z (a→b∧c , b∧c→a) c→b = (λ a → ∧-proj₂ (a→b∧c a)) , (λ c → b∧c→a ((c→b c) , c))

-- Definitions of subset and not-membership.

_⊆_ : 𝓢 → 𝓢 → Set
x ⊆ y = (t : 𝓢) → t ∈ x → t ∈ y

_∉_ : 𝓢 → 𝓢 → Set
x ∉ y = ¬ (x ∈ y)
{-# ATP definition _∉_ #-}

_⊂_ : 𝓢 → 𝓢 → Set
x ⊂ y = x ⊆ y ∧ x ≢ y

_⊂'_ : 𝓢 → 𝓢 → Set
x ⊂' y = x ⊆ y ∧ ∃ (λ z → z ∈ y ∧ z ∉ x)

-------------------------------------------

-- ZFC's axioms
-- From (Suppes 1960, p. 56)

-- ext (Extensionality) : If two sets have exactly the same members,
-- they are equal.

-- empt (Empty Set Axiom) : There is a set having no
-- members. Allows us to define the empty set.

-- pair (Pairing Axiom) : For any sets y and z, there is a set having
-- as members just y and z. Allows to define a set which is just
-- the pair of any two sets.

-- pow (Power Set Axiom): For any x there is a set whose members are
-- exactly the subsets of x. Allows us to define the power set
-- operation.

-- sub (Subset Axiom, or Specification Axiom): This axiom asserts the
-- existence of a set B whose members are exactly those sets x in y
-- such that they satisfy certain property. Allows us to define
-- many operations like cartesian products and difference of sets.

-- uni (Union Axiom) : For any set x, there exists a set A whose
-- elements are exactly the members of x. Allows us to define the
-- union of two sets.

-- pem (Principle of the excluded middle) : To prove some things
-- not valid in intuitionistic logic and valid in classical logic. Taken
-- from the Standford Encyclopedia entry on Intuitionistic Logic.
-- (https://plato.stanford.edu/entries/logic-intuitionistic/).

-- The sum axioms allow us to define the union operation
-- over a family of sets.

postulate
  empt : ∃ (λ B → ∀ x → x ∉ B)
  ext  : (x y : 𝓢) → ∀ {z} → z ∈ x ⇔ z ∈ y → x ≡ y
  union : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ z ∈ x ∨ z ∈ y)
  pair : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ (z ≡ x ∨ z ≡ y))
  pow : (x : 𝓢) → ∃ (λ B → ∀ {y} → y ∈ B ⇔ y ⊆ x)
  sub  : (A : 𝓢 → Set) → (y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ (z ∈ y ∧ A z)))
  pem : (A : Set) → A ∨ ¬ A
  sum : (A : 𝓢) → ∃ (λ C → (x : 𝓢) → x ∈ C ⇔ ∃ (λ B → x ∈ B ∧ B ∈ A))
{-# ATP axioms empt ext union pair pow #-}

-- sub not given to apia since it is an axiom schema and ATPs don't deal
-- with that.

-- pem isn't given either since ATP's use classical logic so it uses
-- this principle by default.

∅ : 𝓢
∅ = proj₁ empt
{-# ATP definition ∅ #-}

-- Intersection. Need to be included here to formalize
-- the axiom of regularity.

_∩_ : 𝓢 → 𝓢 → 𝓢
x ∩ y = proj₁ (sub (λ z → z ∈ y) x)

-- Axiom of regularity: Axiom that have two very intuitive consequences:
-- ∀ A (A ∉ A) and ¬ ∀ A,B (A∈B ∧ B∈A)
postulate
  reg : (A : 𝓢) → A ≢ ∅ → ∃ (λ x → x ∈ A ∧ ∀ y → y ∈ x → y ∉ A)
