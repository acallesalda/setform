------------------------------------------
-- Set theory formalization
------------------------------------------

module SetTheory where

infix 6 𝓟_
infix 6 _-_
infix 6 _∩_
infix 6 _ₚ_
infix 6 _∪_
infix 5 _⊆_
infix 5 _∈_ _∉_
infix 4 _≡_
infix 4 _,_
infix 3 ¬_
infix 1 _∧_
infix 1 ∃
infix 1 _∨_
infix 0 _⇔_

-- 0ur Sets will be denoted by 𝓢. This is
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

-- Existential projections.

proj₁ : {A : 𝓢 → Set} → ∃ A → 𝓢
proj₁ (t , _) = t

proj₂ : (A : 𝓢 → Set) → (foo : ∃ A)  → A (proj₁ foo)
proj₂ A (_ , Ax) = Ax

-------------------------------------------

-- Equivalence and non equivalence with some useful properties

data _≡_ (x : 𝓢) : 𝓢 → Set where
  refl : x ≡ x

_≢_ : 𝓢 → 𝓢 → Set
x ≢ y = ¬ x ≡ y

sym : (x y : 𝓢) → x ≡ y → y ≡ x
sym x .x refl = refl

trans : {x y z : 𝓢} → x ≡ y →  y ≡ z → x ≡ z
trans refl refl = refl

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

-- ZFC's axioms
-- From (Suppes 1960, p. 56)

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

-- pem (Principle of the excluded middle) : To prove some things
-- not valid in intuitionistic logic and valid in classical logic.

-- The other three axioms are yet to implement.

postulate
  empt : ∃ (λ B → ∀ x → x ∉ B)
  ext  : (x y : 𝓢) → ∀ {z} → z ∈ x ⇔ z ∈ y → x ≡ y
  union : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ z ∈ x ∨ z ∈ y)
  pair : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → z ∈ B ⇔ (z ≡ x ∨ z ≡ y))
  pow : (x : 𝓢) → ∃ (λ B → ∀ {y} → y ∈ B ⇔ y ⊆ x)
  sub  : (A : 𝓢 → Set) → (y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ (z ∈ y ∧ A z)))
  pem : (A : Set) → A ∨ ¬ A
{-# ATP axioms empt ext union pair pow #-}

-- sub not given to apia since it is an axiom schema and ATPs don't deal
-- with that.

-- pem isn't given either since ATP's use classical logic so it uses
-- this principle by default.

-- Basic Properties involving membership, and subsets.

∅ : 𝓢
∅ = proj₁ empt
{-# ATP definition ∅ #-}

cont : (A : Set) → A ∧ ¬ A → ⊥
cont _ (x , ¬x) = ¬x x

memberEq : (x y z : 𝓢) → x ∈ y ∧ y ≡ z → x ∈ z
memberEq x y z (x₁ , x₂) = subs _ x₂ x₁

notInEmpty : ∀ x → x ∉ ∅
notInEmpty x h  = (proj₂ _ empt) x h

subsetOfItself : ∀ {x} → x ⊆ x
subsetOfItself _ t∈x = t∈x

equalitySubset :  (x y : 𝓢) → x ⊆ y ∧ y ⊆ x → x ≡ y
equalitySubset x y (x⊆y , y⊆x) = ext x y ((x⊆y x) , (y⊆x x))

trans-⊆ : (x y z : 𝓢) → x ⊆ y ∧ y ⊆ z → x ⊆ z
trans-⊆ x y z (x⊆y , y⊆z) t t∈x = y⊆z t (x⊆y t t∈x)

notContainedInItself : ∀ {x} → ¬ (x ⊂ x)
notContainedInItself (_ , x≢x) = x≢x refl

nonSymmetry-⊂ : (x y : 𝓢) (p : x ⊂ y) → ¬ (y ⊂ x)
nonSymmetry-⊂ x y (x⊆y , x≢y) (y⊆x , _) = x≢y (equalitySubset x y (x⊆y , y⊆x))

⊂→⊆ : ∀ {x y} → x ⊂ y → x ⊆ y
⊂→⊆ (x⊆y , _) z z∈x = x⊆y z z∈x

-- Properties involving operations between sets, algebra of sets.

-- First, some properties of the union between sets, justified by the
-- union axiom.

_∪_ : 𝓢 → 𝓢 → 𝓢
x ∪ y = proj₁ (union x y)
{-# ATP definition _∪_ #-}

∪-d : (x y : 𝓢) → ∀ {z} → z ∈ x ∪ y ⇔ z ∈ x ∨ z ∈ y
∪-d x y = proj₂ _ (union x y)

∪-d₁ : (A B : 𝓢) → ∀ {x} → x ∈ (A ∪ B) → x ∈ A ∨ x ∈ B
∪-d₁ A B = ∧-proj₁ (∪-d A B)

∪-d₂ : (A B : 𝓢) → ∀ {x} → x ∈ A ∨ x ∈ B → x ∈ (A ∪ B)
∪-d₂ A B = ∧-proj₂ (∪-d A B)

A∪B≡B∪A : (A B : 𝓢) → A ∪ B ≡ B ∪ A
A∪B≡B∪A A B = equalitySubset (A ∪ B) (B ∪ A) (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ (A ∪ B) → x ∈ (B ∪ A)
  p₁ x x₁ = ∪-d₂ B A (∨-sym _ _ (∪-d₁ A B x₁))
  p₂ : (x : 𝓢) → x ∈ (B ∪ A) → x ∈ (A ∪ B)
  p₂ x x₁ = ∪-d₂ A B (∨-sym _ _ (∪-d₁ B A x₁))

A∪A≡A : (A : 𝓢) → A ∪ A ≡ A
A∪A≡A A = equalitySubset (A ∪ A) A (p₁ , p₂)
  where
  p₁ : (x :  𝓢) → x ∈ (A ∪ A) → x ∈ A
  p₁ x x₁ = ∨-idem _ (∪-d₁ A A x₁)
  p₂ : (x : 𝓢) → x ∈ A → x ∈ (A ∪ A)
  p₂ x x₁ = ∪-d₂ A A (inj₁ x₁)

∪-prop : (A B : 𝓢) → A ⊆ A ∪ B
∪-prop A B t x = ∪-d₂ _ _ (inj₁ x)

⊆∪ : (x A B : 𝓢) → x ⊆ A ∧ x ⊆ B → x ⊆ A ∪ B
⊆∪ x A B (x₁ , x₂) t x₃ = trans-⊆ _ _ _ (x₁ , (∪-prop _ _)) _ x₃

∪-prop₂ : (x A B : 𝓢) → x ⊆ A ∨ x ⊆ B → x ⊆ A ∪ B
∪-prop₂ x A B (inj₁ x₁) t x₂ = ∪-d₂ _ _ (inj₁ (x₁ _ x₂))
∪-prop₂ x A B (inj₂ x₁) t x₂ = ∪-d₂ _ _ (inj₂ (x₁ _ x₂))

-- Properties about the intersection opertaion. Its existence is justified
-- as an axiom derived from the sub axiom schema.

_∩_ : 𝓢 → 𝓢 → 𝓢
x ∩ y = proj₁ (sub (λ z → z ∈ y) x)

sub₂ : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ z ∈ x ∧ z ∈ y))
sub₂ x y = sub (λ z → z ∈ y) x

∩-def : (x y : 𝓢) → ∀ {z} → z ∈ x ∩ y ⇔ z ∈ x ∧ z ∈ y
∩-def x y = proj₂ _ (sub₂ x y)

∩-d₁ : (x A B : 𝓢)  → x ∈ (A ∩ B) → x ∈ A ∧ x ∈ B
∩-d₁ x A B = ∧-proj₁ (∩-def A B)

∩-d₂ : (x A B : 𝓢) → x ∈ A ∧ x ∈ B → x ∈ (A ∩ B)
∩-d₂ x A B = ∧-proj₂ (∩-def A B)

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

-- Properties involving the difference between sets. The existence of this
-- sets is also justified as an instance of the subset axiom schema.

sub₃ : (x y : 𝓢) → ∃ (λ B → {z : 𝓢} → (z ∈ B ⇔ z ∈ x ∧ z ∉ y))
sub₃ x y = sub (λ z → z ∉ y) x

_-_ : 𝓢 → 𝓢 → 𝓢
x - y = proj₁ (sub₃ x y)

dif-def : (x y : 𝓢) → ∀ {z} → z ∈ (x - y) ⇔ z ∈ x ∧ z ∉ y
dif-def x y = proj₂ _ (sub₃ x y)

dif-d₁ : (A B z : 𝓢) → z ∈ A - B → z ∈ A ∧ z ∉ B
dif-d₁ A B z = ∧-proj₁ (dif-def A B)

dif-d₂ : (A B z : 𝓢) → z ∈ A ∧ z ∉ B → z ∈ A - B
dif-d₂ A B z = ∧-proj₂ (dif-def A B)

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

-- Pairs, justified by the pair axiom

_ₚ_ : 𝓢 → 𝓢 → 𝓢
x ₚ y = proj₁ (pair x y)

pair-d : (x y : 𝓢) → ∀ {z} → z ∈ x ₚ y ⇔ (z ≡ x ∨ z ≡ y)
pair-d x y = proj₂ _ (pair x y)

pair-d₁ : (x y : 𝓢) → ∀ {z} → z ∈ x ₚ y → (z ≡ x ∨ z ≡ y)
pair-d₁ x y = ∧-proj₁ (pair-d x y)

pair-d₂ : (x y : 𝓢) → ∀ {z} → (z ≡ x ∨ z ≡ y) → z ∈ x ₚ y
pair-d₂ x y = ∧-proj₂ (pair-d x y)

pair-p₁ : (x y : 𝓢) → x ₚ y ≡ y ₚ x
pair-p₁ x y = equalitySubset (x ₚ y) (y ₚ x) (p₁ , p₂)
  where
  p₁ : (z : 𝓢) → z ∈ x ₚ y → z ∈ y ₚ x
  p₁ z z∈x,y = pair-d₂ y x (∨-sym _ _ (pair-d₁ x y z∈x,y))
  p₂ : (z : 𝓢) → z ∈ y ₚ x → z ∈ x ₚ y
  p₂ z z∈y,x = pair-d₂ x y (∨-sym _ _ (pair-d₁ y x z∈y,x))

singleton : 𝓢 → 𝓢
singleton x = x ₚ x

singletonp : (x : 𝓢) → ∀ {z} → z ∈ singleton x → z ≡ x
singletonp x x₁ = ∨-idem _ (pair-d₁ x x x₁)

singletonp₂ : (x : 𝓢) → x ∈ singleton x
singletonp₂ x = pair-d₂ x x (inj₁ refl)

pair-prop-helper₁ : {a b c : 𝓢} → a ≡ b ∨ a ≡ c → a ≢ b → a ≡ c
pair-prop-helper₁ (inj₁ a≡b)  h = ⊥-elim (h a≡b)
pair-prop-helper₁ (inj₂ refl) _ = refl

pair-prop-helper₂ : {a b : 𝓢} → a ≢ b → b ≢ a
pair-prop-helper₂ h b≡a = h (sym _ _ b≡a)

-- Theorem 44, p. 31 (Suppes, 1972).
pair-prop : (x y u v : 𝓢) → x ₚ y ≡ u ₚ v → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
pair-prop x y u v eq = ∨-e _ _ _ (pem (x ≡ y)) h-x≡y h-x≢y
  where
  u∈u,v : u ∈ (u ₚ v)
  u∈u,v = ∨-prop₁ (pair-d₂ u v) refl

  u∈x,y : u ∈ (x ₚ y)
  u∈x,y = memberEq u (u ₚ v) (x ₚ y) (u∈u,v , (sym _ _ eq))

  disj₁ : u ≡ x ∨ u ≡ y
  disj₁ = pair-d₁ _ _ u∈x,y

  v∈u,v : v ∈ (u ₚ v)
  v∈u,v = ∨-prop₂ (pair-d₂ u v) refl

  v∈x,y : v ∈ (x ₚ y)
  v∈x,y = memberEq v (u ₚ v) (x ₚ y) (v∈u,v , (sym _ _ eq))

  disj₂ : v ≡ x ∨ v ≡ y
  disj₂ = pair-d₁ _ _ v∈x,y

  x∈x,y : x ∈ (x ₚ y)
  x∈x,y = ∨-prop₁ (pair-d₂ x y) refl

  x∈u,v : x ∈ (u ₚ v)
  x∈u,v = memberEq x (x ₚ y) (u ₚ v) (x∈x,y , eq)

  disj₃ : x ≡ u ∨ x ≡ v
  disj₃ = pair-d₁ _ _ x∈u,v

  y∈x,y : y ∈ (x ₚ y)
  y∈x,y = ∨-prop₂ (pair-d₂ x y) refl

  y∈u,v : y ∈ (u ₚ v)
  y∈u,v = memberEq y (x ₚ y) (u ₚ v) (y∈x,y , eq)

  disj₄ : y ≡ u ∨ y ≡ v
  disj₄ = pair-d₁ _ _ y∈u,v

  h-x≡y : x ≡ y → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
  h-x≡y eq₂ = inj₁ (x≡u , v≡y)
    where
    x≡u : u ≡ x
    x≡u = ∨-idem _ disj-aux
      where
      disj-aux : u ≡ x ∨ u ≡ x
      disj-aux = subs _ (sym _ _ eq₂) disj₁

    v≡y : v ≡ y
    v≡y = ∨-idem _ disj-aux
      where
      disj-aux : v ≡ y ∨ v ≡ y
      disj-aux = subs _ eq₂ disj₂

  h-x≢y : x ≢ y → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
  -- Suppes negates u ≡ x and obtains v ≡ x ∧ u ≡ y. Then
  -- he negates u ≡ y and obtains u ≡ x ∧ v ≡ y. He uses then
  -- a weird rule of logic like this:
  -- (¬ A → C ∧ D) → (¬ D → A ∧ B) → ((A ∧ B) ∨ (C ∧ D))
  -- Is that a rule of logic? I don't understand his reasoning
  h-x≢y ¬eq = ∨-e _ _ _ (pem (x ≡ u)) h₁ h₂
    where
    h₁ : x ≡ u → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
    h₁ x≡u = ∨-e _ _ _ (pem (y ≡ u)) h₁₁ h₁₂
      where
      h₁₁ : y ≡ u → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
      h₁₁ y≡u = ⊥-elim (¬eq (trans x≡u (sym _ _ y≡u)))

      h₁₂ : y ≢ u → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
      h₁₂ h = inj₁ (sym _ _ x≡u , sym _ _ (pair-prop-helper₁ disj₄ h))

    h₂ : x ≢ u → (u ≡ x ∧ v ≡ y) ∨ (v ≡ x ∧ u ≡ y)
    h₂ h = inj₂ (sym _ _ (pair-prop-helper₁ disj₃ h)
                ,
                (pair-prop-helper₁ disj₁ (pair-prop-helper₂ h)))

-- Ordered pairs

-- To prove things about ordered pairs I have to prove first
-- pair-prop.

_ₒ_ : 𝓢 → 𝓢 → 𝓢
x ₒ y = x ₚ (x ₚ y)

-- Power sets

𝓟_ : 𝓢 → 𝓢
𝓟 x = proj₁ (pow x)

𝓟-d : (x : 𝓢) → ∀ {z} → z ∈ (𝓟 x) ⇔ z ⊆ x
𝓟-d x = proj₂ _ (pow x)

𝓟-d₁ : (x : 𝓢) → ∀ {z} → z ∈ (𝓟 x) → z ⊆ x
𝓟-d₁ _ = ∧-proj₁ (𝓟-d _)

𝓟-d₂ : (x : 𝓢) → ∀ {z} → z ⊆ x → z ∈ (𝓟 x)
𝓟-d₂ _ = ∧-proj₂ (𝓟-d _)

A∈𝓟A : (A : 𝓢) → A ∈ 𝓟 A
A∈𝓟A A = 𝓟-d₂ A subsetOfItself

⊆𝓟 : (A B : 𝓢) → A ⊆ B ⇔ 𝓟 A ⊆ 𝓟 B
⊆𝓟 A B = iₗ , iᵣ
  where
  iₗ : A ⊆ B → 𝓟 A ⊆ 𝓟 B
  iₗ A⊆B t t∈𝓟A = 𝓟-d₂ _ t⊆B
    where
     t⊆A : t ⊆ A
     t⊆A = 𝓟-d₁ A t∈𝓟A
     t⊆B : t ⊆ B
     t⊆B = trans-⊆ _ _ _ (t⊆A , A⊆B)
  iᵣ : 𝓟 A ⊆ 𝓟 B → A ⊆ B
  iᵣ 𝓟A⊆𝓟B t t∈A = 𝓟-d₁ _ A∈𝓟B _ t∈A
    where
    A∈𝓟B : A ∈ 𝓟 B
    A∈𝓟B = 𝓟A⊆𝓟B _ (A∈𝓟A _)

𝓟∪ : (A B : 𝓢) → (𝓟 A) ∪ (𝓟 B) ⊆ 𝓟 (A ∪ B)
𝓟∪ A B t t∈𝓟A∪𝓟B = 𝓟-d₂ _ t⊆A∪B
  where
  ∪₁ : t ∈ 𝓟 A ∨ t ∈ 𝓟 B
  ∪₁ = ∪-d₁ _ _ t∈𝓟A∪𝓟B
  p : t ⊆ A ∨ t ⊆ B
  p = ∨-prop₄ aux₁ (𝓟-d₁ _)
    where
    aux₁ : t ⊆ A ∨ t ∈ 𝓟 B
    aux₁ = ∨-prop₃ ∪₁ (𝓟-d₁ _)
  t⊆A∪B : t ⊆ A ∪ B
  t⊆A∪B = ∪-prop₂ _ _ _ p

-- Cartesian Product. Suppes define it by using some weird
-- instantiation of the subset axiom. I don't really understand
-- his reasoning so translating it is a bit difficult.

_X_ : 𝓢 → 𝓢 → 𝓢
A X B = {!!}

-- References
--
-- Enderton, Herbert B. (1977). Elements of Set Theory.  Academic
-- Press Inc.
--
-- Suppes, Patrick (1960). Axiomatic Set Theory.  The University
-- Series in Undergraduate Mathematics.  D. Van Nostrand Company, Inc.
--
-- Suppes, Patrick (1972). Axiomatic Set Theory.  Dover Publications,
-- Inc.
