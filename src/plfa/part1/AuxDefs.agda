module AuxDefs where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

data Bool : Set where
  true  : Bool
  false : Bool

data Comparison : Set where
  less    : Comparison
  equal   : Comparison
  greater : Comparison

_<_ : ℕ → ℕ → Bool
zero < y      = true
suc x < zero  = false
suc x < suc y = x < y

