module InequalityReasoningExercise where

open import EqualityAux

infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
      --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

module ≤-Reasoning where

  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≤-≡⟨_⟩_
  infix  3 _≤-∎

  ≤-begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  ≤-begin x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤-≡⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≡ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤-≡⟨ refl ⟩ y≤z = ≤-trans ≤-refl y≤z

  _≤-∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ≤-∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  ≤-begin
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ≤-∎

+-monoʳ-≤ (suc n) p q p≤q =
  ≤-begin
    (suc n) + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    (suc n) + q
  ≤-∎

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  ≤-begin
    m + p
  ≤-≡⟨ +-comm m p ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
    p + n
  ≤-≡⟨ +-comm p n ⟩
    n + p
  ≤-∎

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  ≤-begin
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ≤-∎


