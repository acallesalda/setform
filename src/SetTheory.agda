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
  𝓢   : Set
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

-- Existential projection.

proj₁ : {A : 𝓢 → Set} → ∃ A → 𝓢
proj₁ (t , _) = t

proj₂ : (A : 𝓢 → Set) → (foo : ∃ A)  → A (proj₁ foo)
proj₂ A (_ , Ax) = Ax

-------------------------------------------

-- Equivalence and non equivalence

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

-- Definitions of subset and not-membership.

_⊆_ : 𝓢 → 𝓢 → Set
x ⊆ y = (t : 𝓢) → t ∈ x → t ∈ y

_∉_ : 𝓢 → 𝓢 → Set
x ∉ y = ¬ (x ∈ y)
{-# ATP definition _∉_ #-}

_⊂_ : 𝓢 → 𝓢 → Set
x ⊂ y = x ⊆ y ∧ x ≢ y

-------------------------------------------

-- The Axioms

-- ext (Extensionality) : If two sets have exactly the same members,
-- they are equal.  empt (Empty Set Axiom) : There is a set having no
-- members.


-- pair (Pairing Axiom) : For any sets y and z, there is a set having
-- as members just y and z.

-- pow (Power Set Axiom): For any x there is a set whose members are
-- exactly the subsets of x.

-- sub (Subset Axiom, or Specification Axiom): This axiom asserts the
-- existence of a set B whose members are exactly those sets x in y
-- such that they satisfy certain property.

-- uni (Union Axiom) : For any set x, there exists a set A whose
-- elements are exactly the members of x.

-- The other three axioms are yet to implement.

postulate
  ext  : (x y z : 𝓢) → z ∈ x ⇔ z ∈ y → x ≡ y
  pair : ∀ {y z} → ∃[ B ] (∀ {x} → x ∈ B ⇔ (x ≡ y ∨ x ≡ z))
  pow : ∀ {x} → ∃ (λ B → ∀ {y} → y ∈ B ⇔ y ⊆ x)
  sub  : (A : 𝓢 → Set) → (y : 𝓢) → ∃ (λ B → (x : 𝓢) → (x ∈ B ⇔ (x ∈ y ∧ A x)))
{-# ATP axioms ext #-}
  -- uni  : ∀ {z} → (∃ A : 𝓢) → ∀ {y x} → x ∈ y ∧ y ∈ z → x ∈ A
------------------------------------------

postulate
  empt : ∃ (λ B → ∀ x → x ∉ B)
{-# ATP axioms empt #-}

∅ : 𝓢
∅ = proj₁ empt
{-# ATP definition ∅ #-}

notInEmpty : ∀ x → x ∉ ∅
notInEmpty x h  = (proj₂ _ empt) x h

-- I am having troubles proving this theorem (unique-∅).
-- The left hand side of the implication is easily provable,
-- but the right side is not. I tried seeing if apia could prove it,
-- but it couldn't either.

-- postulate unique-∅ : (x y : 𝓢) → ((x ∉ y) ⇔ y ≡ ∅)
-- {-# ATP prove unique-∅ #-}

subsetOfItself : (x : 𝓢) → x ⊆ x
subsetOfItself _ _ p = p

equalitySubset :  (x y : 𝓢) → x ⊆ y ∧ y ⊆ x → x ≡ y
equalitySubset x y (x⊆y , y⊆x) = ext x y _ ((x⊆y x) , (y⊆x x))

-- This theorem depends on the proof of unique-∅ so I didn't prove it.
postulate subsetOf-∅ : (x :  𝓢) (p : x ⊆ ∅) → x ≡ ∅
{-# ATP prove subsetOf-∅ #-}

trans-⊆ : (x y z : 𝓢) → x ⊆ y ∧ y ⊆ z → x ⊆ z
trans-⊆ x y z (x⊆y , y⊆z) t t∈x = y⊆z t (x⊆y t t∈x)

notContainedInItself : (x : 𝓢) → ¬ (x ⊂ x)
notContainedInItself _ (_ , x≢x) = x≢x refl

nonSymmetry-⊂ : (x y : 𝓢) (p : x ⊂ y) → ¬ (y ⊂ x)
nonSymmetry-⊂ x y (x⊆y , x≢y) (y⊆x , _) = x≢y (equalitySubset x y (x⊆y , y⊆x))

-- Don't know how to finish this proof.
trans-⊂ : (x y z : 𝓢) → x ⊂ y ∧ y ⊂ z → x ⊂ z
trans-⊂ x y z ((x⊆y , x≢y) , (y⊆z , y≢z)) = (trans-⊆ x y z (x⊆y , y⊆z), {!!})

⊂→⊆ : (x y : 𝓢) → x ⊂ y → x ⊆ y
⊂→⊆ _ _ (x⊆y , _) z z∈x = x⊆y z z∈x






