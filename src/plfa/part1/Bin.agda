module plfa.part1.Bin where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Nat.Properties using (+-suc)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩    = 0
from (b O) = 2 * from b
from (b I) = suc (2 * from b)

inc-suc-law : ∀ b → from (inc b) ≡ suc (from b)
inc-suc-law ⟨⟩ = refl
inc-suc-law (b O) = refl
inc-suc-law (b I) rewrite
    inc-suc-law b
  | +-suc (suc (from b)) ((from b) + 0) = refl

