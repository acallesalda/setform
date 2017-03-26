------------------------------------------
-- Set theory formalization
------------------------------------------

module SetTheory where

infix 6 _-_
infix 6 _∩_
infix 6 _ₚ_
infix 6 _∪_
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

∨-e : (A B C : Set) → A ∨ B → (A → C) → (B → C) → C
∨-e A B C (inj₁ a) i₁ i₂ = i₁ a
∨-e A B C (inj₂ b) i₁ i₂ = i₂ b

trivial : (A : Set) → A → A
trivial _ A = A

∨-idem : (A : Set) → A ∨ A → A
∨-idem A (inj₁ a) = a
∨-idem A (inj₂ a) = a

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

_⊂'_ : 𝓢 → 𝓢 → Set
x ⊂' y = x ⊆ y ∧ ∃ (λ z → z ∈ y ∧ z ∉ x)


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
  ext  : (x y : 𝓢) → ∀ {z} → z ∈ x ⇔ z ∈ y → x ≡ y
  union : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ z ∈ x ∨ z ∈ y)
  pair : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ (z ≡ x ∨ z ≡ y))
  pow : ∀ {x} → ∃ (λ B → ∀ {y} → y ∈ B ⇔ y ⊆ x)
  sub  : (A : 𝓢 → Set) → (y : 𝓢) → ∃ (λ B → (x : 𝓢) → (x ∈ B ⇔ (x ∈ y ∧ A x)))
{-# ATP axioms ext union #-}
  -- uni  : ∀ {z} → (∃ A : 𝓢) → ∀ {y x} → x ∈ y ∧ y ∈ z → x ∈ A
------------------------------------------

-- Pairs, singletons.

_ₚ_ : 𝓢 → 𝓢 → 𝓢
x ₚ y = proj₁ (pair x y)

singleton : 𝓢 → 𝓢
singleton x = x ₚ x


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

subsetOfItself : ∀ {x} → x ⊆ x
subsetOfItself _ t∈x = t∈x

equalitySubset :  (x y : 𝓢) → x ⊆ y ∧ y ⊆ x → x ≡ y
equalitySubset x y (x⊆y , y⊆x) = ext x y ((x⊆y x) , (y⊆x x))

-- This theorem depends on the proof of unique-∅ so I didn't prove it.
-- postulate subsetOf-∅ : (x :  𝓢) (p : x ⊆ ∅) → x ≡ ∅
-- {-# ATP prove subsetOf-∅ #-}

trans-⊆ : (x y z : 𝓢) → x ⊆ y ∧ y ⊆ z → x ⊆ z
trans-⊆ x y z (x⊆y , y⊆z) t t∈x = y⊆z t (x⊆y t t∈x)

notContainedInItself : ∀ {x} → ¬ (x ⊂ x)
notContainedInItself (_ , x≢x) = x≢x refl

nonSymmetry-⊂ : (x y : 𝓢) (p : x ⊂ y) → ¬ (y ⊂ x)
nonSymmetry-⊂ x y (x⊆y , x≢y) (y⊆x , _) = x≢y (equalitySubset x y (x⊆y , y⊆x))

⊂→⊆ : ∀ {x y} → x ⊂ y → x ⊆ y
⊂→⊆ (x⊆y , _) z z∈x = x⊆y z z∈x

_∩_ : 𝓢 → 𝓢 → 𝓢
x ∩ y = proj₁ (sub (λ z → z ∈ x) y)

_∪_ : 𝓢 → 𝓢 → 𝓢
x ∪ y = proj₁ (union x y)
{-# ATP definition _∪_ #-}

-- proj₂ : (A : 𝓢 → Set) → (foo : ∃ A)  → A (proj₁ foo)
-- proj₂ A (_ , Ax) = Ax
-- union : (x y : 𝓢) → ∃ (λ B → ∀ {z} → z ∈ B ⇔ z ∈ x ∨ z ∈ y)

theorem : (x y : 𝓢) → ∀ {z} → z ∈ x ∪ y ⇔ z ∈ x ∨ z ∈ y
theorem x y = proj₂ _ (union x y)


postulate
 ∪-d : (x A B : 𝓢) → x ∈ (A ∪ B) ⇔ x ∈ A ∨ x ∈ B
 ∩-def : (x A B : 𝓢) → x ∈ (A ∩ B) ⇔ x ∈ A ∧ x ∈ B
{-# ATP prove ∪-d #-}

∩-d₁ : (x A B : 𝓢)  → x ∈ (A ∩ B) → x ∈ A ∧ x ∈ B
∩-d₁ x A B = ∧-proj₁ (∩-def x A B)

∩-d₂ : (x A B : 𝓢) → x ∈ A ∧ x ∈ B → x ∈ (A ∩ B)
∩-d₂ x A B = ∧-proj₂ (∩-def x A B)

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

∩-itself : (A : 𝓢) → A ∩ A ≡ A
∩-itself A = equalitySubset (A ∩ A) A (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ A ∩ A → x ∈ A
  p₁ x x₁ = ∧-proj₁ (∩-d₁ _ A _ x₁)
  p₂ : (x :  𝓢) → x ∈ A → x ∈ A ∩ A
  p₂ x x₁ = ∩-d₂ _ A A (x₁ , x₁)

A∩B⊆A : (A B : 𝓢) → A ∩ B ⊆ A
A∩B⊆A A B _ p = ∧-proj₁ (∩-d₁ _ A _ p)

∪-d₁ : (x A B : 𝓢) → x ∈ (A ∪ B) → x ∈ A ∨ x ∈ B
∪-d₁ x A B = ∧-proj₁ (∪-d x A B)

∪-d₂ : (x A B : 𝓢) → x ∈ A ∨ x ∈ B → x ∈ (A ∪ B)
∪-d₂ x A B = ∧-proj₂ (∪-d x A B)

postulate
 pair-d : (x y z : 𝓢) → z ∈ (x ₚ y) ⇔ z ≡ x ∨ z ≡ y

-- th : ∀ {z} → (x y : 𝓢) → z ∈ x ₚ y ⇔ z ≡ x ∨ x ≡ y
-- th x y = proj₂ (λ z → z ∈ x ₚ y ⇔ z ≡ x ∨ z ≡ y) {!!}

_-_ : 𝓢 → 𝓢 → 𝓢
x - y = proj₁ (sub (λ z → z ∉ x) y)

postulate
 dif-d : (A B z : 𝓢) → z ∈ A - B ⇔ z ∈ A ∧ z ∉ B

dif-d₁ : (A B z : 𝓢) → z ∈ A - B → z ∈ A ∧ z ∉ B
dif-d₁ A B z = ∧-proj₁ (dif-d A B z)

dif-d₂ : (A B z : 𝓢) → z ∈ A ∧ z ∉ B → z ∈ A - B
dif-d₂ A B z = ∧-proj₂ (dif-d A B z)

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
