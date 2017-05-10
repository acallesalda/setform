---------------------------------------
-- Pairs of sets
---------------------------------------

{-# OPTIONS --allow-unsolved-meta #-}

module Pairs where

-- Everything involving pairs, be them unordered
-- or ordered pairs. Also the definition of power set
-- and cartesian product between sets.

open import Logic
open import Algebra
open import Subset
open import ZAxioms

-- Pairs, justified by the pair axiom

_ₚ_ : 𝓢 → 𝓢 → 𝓢
x ₚ y = proj₁ (pair x y)

pair-d : (x y : 𝓢) → ∀ {z} → z ∈ x ₚ y ⇔ (z ≡ x ∨ z ≡ y)
pair-d x y = proj₂ _ (pair x y)

-- Both ∧-projections
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

singletonp₃ : (x : 𝓢) → ∀ {y} → x ≡ y → x ∈ singleton y
singletonp₃ x x≡y = pair-d₂ _ _ (inj₁ x≡y)

singletonp₄ : (x y : 𝓢) → x ∈ singleton y → x ∩ singleton y ≡ ∅
singletonp₄ x y h = {!!}
  where
  p₁ : x ≡ y
  p₁ = singletonp _ h

  p₂ : x ∩ singleton x ≡ ∅
  p₂ = {!!}

pair-prop-helper₁ : {a b c : 𝓢} → a ≡ b ∨ a ≡ c → a ≢ b → a ≡ c
pair-prop-helper₁ (inj₁ a≡b) h = ⊥-elim (h a≡b)
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

-- Theorem 45, p. 32 (Suppes 1960).
singleton-eq : (x y : 𝓢) → singleton x ≡ singleton y → x ≡ y
singleton-eq x y eq = sym _ _ (∧-proj₁ (∨-idem _ aux))
  where
  aux : ((y ≡ x) ∧ (y ≡ x)) ∨ ((y ≡ x) ∧ (y ≡ x))
  aux = pair-prop x x y y eq

singleton-⊆ : (x A : 𝓢) → x ∈ A → singleton x ⊆ A
singleton-⊆ x A x∈A t t∈xₛ = subs _ (sym _ _ (singletonp _ t∈xₛ)) x∈A

prop-p₂ : (y z : 𝓢) → y ₚ z ≡ singleton y ∪ singleton z
prop-p₂ y z = equalitySubset _ _ (p₁ , p₂)
  where
  p₁ : (x : 𝓢) → x ∈ y ₚ z → x ∈ singleton y ∪ singleton z
  p₁ _ h = ∪-d₂ _ _ (∨-prop₅ (pair-d₁ _ _ h) (singletonp₃ _) (singletonp₃ _))

  p₂ : (x : 𝓢) → x ∈ singleton y ∪ singleton z → x ∈ y ₚ z
  p₂ x h = pair-d₂ _ _ (∨-prop₅ (∪-d₁ _ _ h) (singletonp _) (singletonp _))

-- Ordered pairs

_ₒ_ : 𝓢 → 𝓢 → 𝓢
x ₒ y = singleton x ₚ (x ₚ y)

-- Just an abvreviation for next theorem
abv₁ : 𝓢 → 𝓢 → 𝓢 → 𝓢 → Set
abv₁ u x v y = (u ₚ u ≡ x ₚ x ∧ u ₚ v ≡ x ₚ y) ∨ (u ₚ v ≡ x ₚ x ∧ u ₚ u ≡ x ₚ y)

-- Theorem 46, p. 32 (Suppes).
ord-p : (x y u v : 𝓢) → x ₒ y ≡ u ₒ v → x ≡ u ∧ y ≡ v
ord-p x y u v eq = ∨-e _ _ _ aux a→c b→c
  where
  aux : abv₁ u x v y
  aux = pair-prop _ _ _ _ eq

  a→c : singleton u ≡ singleton x ∧ u ₚ v ≡ x ₚ y → x ≡ u ∧ y ≡ v
  a→c (eqₚ , eqₛ) = x≡u , y≡v
    where
    x≡u : x ≡ u
    x≡u = singleton-eq _ _ (sym _ _ eqₚ)

    y≡v : y ≡ v
    y≡v = {!!}
  b→c : u ₚ v ≡ singleton x ∧ singleton u ≡ x ₚ y → x ≡ u ∧ y ≡ v
  b→c x₁ = {!!}

-- Power sets

𝓟_ : 𝓢 → 𝓢
𝓟 x = proj₁ (pow x)

-- Theorem 86, p. 47 (Suppes 1960)
𝓟-d : (x : 𝓢) → ∀ {z} → z ∈ (𝓟 x) ⇔ z ⊆ x
𝓟-d x = proj₂ _ (pow x)

-- Both projections.
𝓟-d₁ : (x : 𝓢) → ∀ {z} → z ∈ (𝓟 x) → z ⊆ x
𝓟-d₁ _ = ∧-proj₁ (𝓟-d _)

𝓟-d₂ : (x : 𝓢) → ∀ {z} → z ⊆ x → z ∈ (𝓟 x)
𝓟-d₂ _ = ∧-proj₂ (𝓟-d _)

-- Theorem 87, p. 47 (Suppes 1960).
A∈𝓟A : (A : 𝓢) → A ∈ 𝓟 A
A∈𝓟A A = 𝓟-d₂ A subsetOfItself

-- Theorem 91, p. 48 (Suppes 1960).
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

-- Theorem 92, p. 48 (Suppes 1960).
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

-- Cartesian Product. First we have to prove some things using
-- the subset axiom in order to be able to define cartesian products.

-- Two abvreviations to make sub₄ shorter.

abv₂ : 𝓢 → 𝓢 → 𝓢 → Set
abv₂ z A B = z ∈ 𝓟 (𝓟 (A ∪ B))

abv₃ : 𝓢 → 𝓢 → 𝓢 → Set
abv₃ z A B = ∃ (λ y → ∃ (λ w → (y ∈ A ∧ w ∈ B) ∧ z ≡ y ₒ w))

--Instance of the subset axiom.
sub₄ : (A B : 𝓢) → ∃ (λ C → {z : 𝓢} → z ∈ C ⇔ abv₂ z A B ∧ abv₃ z A B)
sub₄ A B = sub (λ x → abv₃ x A B) (𝓟 (𝓟 (A ∪ B)))

-- Proved inside theorem 95, p. 49 (Suppes 1960)
prop₁ : (A B x : 𝓢) → abv₃ x A B → abv₂ x A B
prop₁ A B x (y , (z , ((y∈A , z∈B) , eqo))) = subs _ (sym _ _ eqo)  yₒz∈𝓟𝓟A∪B
  where
  yₛ⊆A : singleton y ⊆ A
  yₛ⊆A = singleton-⊆ _ _ y∈A

  yₛ⊆A∪B : singleton y ⊆ A ∪ B
  yₛ⊆A∪B t t∈yₛ = trans-⊆ _ _ _ (yₛ⊆A , (∪-prop _ _)) _ t∈yₛ

  zₛ⊆B : singleton z ⊆ B
  zₛ⊆B = singleton-⊆ _ _ z∈B

  zₛ⊆A∪B : singleton z ⊆ A ∪ B
  zₛ⊆A∪B t t∈zₛ = trans-⊆ _ _ _ (zₛ⊆B , ∪-prop₃ _ _) _ t∈zₛ

  y,z⊆A∪B : y ₚ z ⊆ A ∪ B
  y,z⊆A∪B t t∈y,z = ∪-prop₄ _ _ _ yₛ⊆A∪B zₛ⊆A∪B _ p
    where
    p : t ∈ singleton y ∪ singleton z
    p = subs (λ w → t ∈ w) (prop-p₂ y z) t∈y,z
  yₛ∈𝓟A∪B : singleton y ∈ 𝓟 (A ∪ B)
  yₛ∈𝓟A∪B = 𝓟-d₂ _ yₛ⊆A∪B

  y,z∈𝓟A∪B : y ₚ z ∈ 𝓟 (A ∪ B)
  y,z∈𝓟A∪B = 𝓟-d₂ _ y,z⊆A∪B

  yₒz⊆𝓟A∪B : y ₒ z ⊆ 𝓟 (A ∪ B)
  yₒz⊆𝓟A∪B t t∈o = ∨-e _ _ _ (pair-d₁ _ _ t∈o) i₁ i₂
    where
    i₁ : t ≡ singleton y → t ∈ 𝓟 (A ∪ B)
    i₁ eq = subs _ (sym t (singleton y) eq) yₛ∈𝓟A∪B

    i₂ : t ≡ y ₚ z → t ∈ 𝓟 (A ∪ B)
    i₂ eq = subs _ (sym t (y ₚ z) eq) y,z∈𝓟A∪B
  yₒz∈𝓟𝓟A∪B : y ₒ z ∈ 𝓟 (𝓟 (A ∪ B))
  yₒz∈𝓟𝓟A∪B = 𝓟-d₂ _ yₒz⊆𝓟A∪B

Aᵤ : 𝓢 → 𝓢 → 𝓢
Aᵤ A B = proj₁ (sub₄ A B)

-- Theorem 95, p 49 (Suppes 1960).
pAᵤ : (A B : 𝓢) → {z : 𝓢} → z ∈ (Aᵤ A B) ⇔ abv₂ z A B ∧ abv₃ z A B
pAᵤ A B = proj₂ _ (sub₄ A B)

crts : (A B : 𝓢) → ∃ (λ C → (z : 𝓢) → z ∈ C ⇔ abv₃ z A B)
crts A B  = (Aᵤ A B) , (λ w → ⇔-p₂ w (pAᵤ A B) (prop₁ A B w))

_X_ : 𝓢 → 𝓢 → 𝓢
A X B = proj₁ (crts A B)

-- Theorem 97, p. 50 (Suppes 1960).
crts-p : (A B x : 𝓢) → x ∈ A X B ⇔ abv₃ x A B
crts-p A B x = proj₂ _ (crts A B) x

-- Both projections
crts-p₁ : (A B x : 𝓢) →  x ∈ A X B → abv₃ x A B
crts-p₁ A B x = ∧-proj₁ (crts-p A B x)

crts-p₂ : (A B x : 𝓢) → abv₃ x A B → x ∈ A X B
crts-p₂ A B x = ∧-proj₂ (crts-p A B x)

crts-d₁ : (x y A B : 𝓢) → x ₒ y ∈ A X B → x ∈ A ∧ y ∈ B
crts-d₁ x y A B h = (subs (λ w → w ∈ A) (sym _ _ eq₁) aux∈A)
                         ,
                         subs (λ w → w ∈ B) (sym _ _ eq₂) aux₂∈B
  where
  foo : ∃ (λ z → ∃ (λ w → (z ∈ A ∧ w ∈ B) ∧ (x ₒ y) ≡ (z ₒ w)))
  foo = crts-p₁ A B (x ₒ y) h

  aux : 𝓢
  aux = proj₁ foo

  aux-p : ∃ (λ w → (aux ∈ A ∧ w ∈ B) ∧ (x ₒ y) ≡ (aux ₒ w))
  aux-p = proj₂ _ foo

  aux₂ : 𝓢
  aux₂ = proj₁ aux-p

  aux₂-p : (aux ∈ A ∧ aux₂ ∈ B) ∧ (x ₒ y) ≡ (aux ₒ aux₂)
  aux₂-p = proj₂ _ aux-p

  aux∈A : aux ∈ A
  aux∈A = ∧-proj₁ (∧-proj₁ aux₂-p)

  aux₂∈B : aux₂ ∈ B
  aux₂∈B = ∧-proj₂ (∧-proj₁ aux₂-p)

  eq : x ₒ y ≡ aux ₒ aux₂
  eq = ∧-proj₂ aux₂-p

  eqs : x ≡ aux ∧ y ≡ aux₂
  eqs = ord-p _ _ _ _ eq

  eq₁ : x ≡ aux
  eq₁ = ∧-proj₁ eqs

  eq₂ : y ≡ aux₂
  eq₂ = ∧-proj₂ eqs

-- References
--
-- Suppes, Patrick (1960). Axiomatic Set Theory.
-- The University Series in Undergraduate Mathematics.
-- D. Van Nostrand Company, inc.
--
-- Enderton, Herbert B. (1977). Elements of Set Theory.
-- Academic Press Inc.
