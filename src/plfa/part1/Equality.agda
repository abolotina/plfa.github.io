
module Equality where


-- Equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_


-- Equality is an equivalence relation

sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym {A} {x} {.x} refl = refl


trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans {A} {x} {.x} {.x} refl refl = refl


-- Congruence and substitution

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
    ---------
  → f x ≡ f y
cong f refl = refl


cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl


cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl


subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px



open import AuxDefs

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

postulate
  +-comm : ∀ (m n : ℕ) → m + n ≡ n + m


even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n  =  subst even (+-comm m n)


-- Chains of equations

module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning


trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =        -- begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))
  begin                                 -- ==>
    x                                   -- trans x≡y (trans y≡z refl)
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎


-- Chains of equations, another example

postulate
  +-identity : ∀ (m   : ℕ) → m + zero  ≡ m
  +-suc      : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)


+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm′ m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm′ m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

{-

Exercise ≤-Reasoning

The proof of monotonicity from Chapter Relations can be written in a more readable
form by using an analogue of our notation for ≡-Reasoning. Define ≤-Reasoning
analogously, and use it to write out an alternative proof that addition is monotonic
with regard to inequality. Rewrite all of +-monoˡ-≤, +-monoʳ-≤, and +-mono-≤.

-}

-- Rewriting

{-

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

-}


{-# BUILTIN EQUALITY _≡_ #-}


even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm′ m n ev = {!!}


-- Multiple rewrites

+-comm″ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm″ zero    n = {!!}
+-comm″ (suc m) n = {!!}


-- With-abstraction (examples from the Agda docs)

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) → (xs : List A) → List A
infixr 5 _∷_


filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
...                  | true  = x ∷ filter p xs
...                  | false = filter p xs


compare : ℕ → ℕ → Comparison
compare x y with x < y
...            | false with y < x
...                       | false = equal
...                       | true  = greater
compare x y    | true = less


compare′ : ℕ → ℕ → Comparison
compare′ x y with x < y | y < x
...             | true  | _     = less
...             | _     | true  = greater
...             | false | false = equal


-- Rewriting expanded

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm″ m n ev with m + n | +-comm m n
...                  | mn    | eq       = {!!}


-- Leibniz equality

_≐_ : ∀ {A : Set} (x y : A) → Set₁             -- Set : Set₁, Set₁ : Set₂, and so on
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y


refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px  =  {!!}

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  {!!}


sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx


-- subst : ∀ {A : Set} {x y : A} (P : A → Set)
--   → x ≡ y
--     ---------
--   → P x → P y


≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y


≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y  =  Qy
  where
    Q : A → Set
    Q z = x ≡ z
    Qx : Q x
    Qx = refl
    Qy : Q y
    Qy = x≐y Q Qx


-- Universe polymorphism

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

--    lzero : Level
--    lsuc  : Level → Level

--    Set₀    ==>    Set lzero
--    Set₁    ==>    Set (lsuc lzero)
--    Set₂    ==>    Set (lsuc (lsuc lzero))


-- Given two levels, returns the larger of the two
-- _⊔_ : Level → Level → Level


data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x


sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
    ------
  → y ≡′ x
sym′ refl′ = refl′


_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y


_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

