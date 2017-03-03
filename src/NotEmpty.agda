module NotEmpty where

infix 5 _∈_ _∉_
infix 4 _,_
infix 3 ¬_
infix 2 ∃

postulate
  𝓢   : Set
  _∈_ : 𝓢 → 𝓢 → Set

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data ∃ (A : 𝓢 → Set) : Set where
  _,_ : (t : 𝓢) → A t → ∃ A

proj₁ : {A : 𝓢 → Set} → ∃ A → 𝓢
proj₁ (t , _) = t

proj₂ : (A : 𝓢 → Set) → (foo : ∃ A)  → A (proj₁ foo)
proj₂ A (_ , Ax) = Ax

_∉_ : 𝓢 → 𝓢 → Set
x ∉ y = ¬ (x ∈ y)

postulate
  empt : ∃ (λ B → ∀ x → x ∉ B)

∅ : 𝓢
∅ = proj₁ empt

notInEmpty : ∀ x → x ∉ ∅
notInEmpty x h  = (proj₂ _ empt) x h
