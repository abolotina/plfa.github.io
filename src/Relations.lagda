---
title     : "Relations: Inductive Definition of Relations"
layout    : page
permalink : /Relations
---

After having defined operations such as addition and multiplication,
the next step is to define relations, such as *less than or equal*.

## Imports

\begin{code}
open import Naturals using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Properties using (com+; com+zero; com+suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}

## Defining relations

The relation *less than or equal* has an infinite number of
instances.  Here are just a few of them:

   0 ≤ 0     0 ≤ 1     0 ≤ 2     0 ≤ 3     ...
             1 ≤ 1     1 ≤ 2     1 ≤ 3     ...
                       2 ≤ 2     2 ≤ 3     ...
                                 3 ≤ 3     ...
                                           ...

And yet, we can write a finite definition that encompasses
all of these instances in just a few lines.  Here is the
definition as a pair of inference rules:

    z≤n --------
        zero ≤ n

        m ≤ n
    s≤s -------------
        suc m ≤ suc n

And here is the definition in Agda:
\begin{code}
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {m : ℕ} → zero ≤ m
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
\end{code}
Here `z≤n` and `s≤s` (with no spaces) are constructor names,
while `m ≤ m`, and `m ≤ n` and `suc m ≤ suc n` (with spaces)
are propositions.

Both definitions above tell us the same two things:

+ *Base case*: for all naturals `n`, the proposition `zero ≤ n` holds
+ *Inductive case*: for all naturals `m` and `n`, if the proposition
  `m ≤ n` holds, then the proposition `suc m ≤ suc n` holds.

In fact, they each give us a bit more detail:

+ *Base case*: for all naturals `n`, the constructor `z≤n` 
  produces evidence that `zero ≤ n` holds.
+ *Inductive case*: for all naturals `m` and `n`, the constructor
  `s≤s` takes evidence that `m ≤ n` holds into evidence that
  `suc m ≤ suc n` holds.

Here we have used the word *evidence* as interchangeable with the
word *proof*.  We will tend to say *evidence* when we want to stress
that proofs are just terms in Agda.

For example, here in inference rule notation is the proof that
`2 ≤ 4`.

      z≤n -----
          0 ≤ 2
     s≤s -------
          1 ≤ 3
    s≤s ---------
          2 ≤ 4

And here is the corresponding Agda proof.
\begin{code}
ex₁ : 2 ≤ 4
ex₁ = s≤s (s≤s z≤n)
\end{code}

## Implicit arguments

In the Agda definition, the two lines defining the constructors
use `∀`, very similar to our use of `∀` in propositions such as:

    com+ : ∀ (m n : ℕ) → m + n ≡ n + m

However, here the declarations are surrounded by curly braces `{ }`
rather than parentheses `( )`.  This means that the arguments are
*implicit* and need not be written explicitly.  Thus, we would write,
for instance, `com+ m n` for the proof that `m + n ≡ n + m`, but
here will write `z≤n` for the proof that `m ≤ m`, leaving the `m` implicit,
or if `m≤n` is evidence that `m ≤ n`, we write write `s≤s m≤n` for the
evidence that `suc m ≤ suc n`, leaving both `m` and `n` implicit.

It is possible to provide implicit arguments explicitly if we wish, by
writing the arguments inside curly braces.  For instance, here is the
Agda proof that `2 ≤ 4` repeated, with the implicit arguments made
explicit.
\begin{code}
ex₂ : 2 ≤ 4
ex₂ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))
\end{code}

## Precedence

We write `infix` to indicate that it is a parse error to write two
adjacent comparisons, as it makes no sense to give `2 ≤ 4 ≤ 6` either
the meaning `(2 ≤ 4) ≤ 6` or `(2 ≤ 4) ≤ 6`.The Agda standard library
sets the precedence of `_≤_` at level 4, which means it binds less
tightly that `_+_` at level 6, or `_*_` at level 7.
\begin{code}
infix 4 _≤_
\end{code}

## Properties of ordering relations

Relations occur all the time, and mathematicians have agreed
on names for some of the most common properties.

+ *Reflexive* For all `n`, the relation `n ≤ n` holds.
+ *Transitive* For all `m`, `n`, and `p`, if `m ≤ n` and
`n ≤ p` hold, then `m ≤ p` holds.
+ *Anti-symmetric* For all `m` and `n`, if both `m ≤ n` and
`n ≤ m` hold, then `m ≡ n` holds.
+ *Total* For all `m` and `n`, either `m ≤ n` or `n ≤ m`
holds.

The relation `_≤_` satisfies all four of these properties.

There are also names for some combinations of these properties.

+ *Preorder* Any relation that is reflexive and transitive.
+ *Partial order* Any preorder that is also anti-symmetric.
+ *Total order* Any partial order that is also total.

If you ever bump into a relation at a party, you now know how
to make small talk, by asking it whether it is reflexive, transitive,
anti-symmetric, and total. Or instead you might ask whether it is a
preorder, partial order, or total order.

Less frivolously, if you ever bump into a relation while reading
a technical paper, this gives you an easy way to orient yourself,
by checking whether or not it is a preorder, partial order, or total order.
A careful author will often make it explicit, for instance by saying
that a given relation is a preoder but not a partial order, or a
partial order but not a total order. (Can you think of examples of
such relations?)


## Reflexivity

The first property to prove about comparison is that it is reflexive:
for any natural `n`, the relation `n ≤ n` holds.
\begin{code}
refl≤ : ∀ (n : ℕ) → n ≤ n
refl≤ zero = z≤n
refl≤ (suc n) = s≤s (refl≤ n)
\end{code}
The proof is a straightforward induction on `n`.  In the base case,
`zero ≤ zero` holds by `z≤n`.  In the inductive case, the inductive
hypothesis `refl≤ n` gives us a proof of `n ≤ n`, and applying `s≤s`
to that yields a proof of `suc n ≤ suc n`.

It is a good exercise to prove reflexivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.


## Transitivity

The second property to prove about comparison is that it is
transitive: for any naturals `m`, `n`, andl `p`, if `m ≤ n` and `n ≤
p` hold, then `m ≤ p` holds.
\begin{code}
trans≤ : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
trans≤ z≤n _ = z≤n
trans≤ (s≤s m≤n) (s≤s n≤p) = s≤s (trans≤ m≤n n≤p)
\end{code}
Here the proof is most easily thought of as by induction on the
*evidence* that `m ≤ n`, so we have left `m`, `n`, and `p` implicit.

In the base case, `m ≤ n` holds by `z≤n`, so it must be that
`m` is `zero`, in which case `m ≤ p` also holds by `z≤n`. In this
case, the fact that `n ≤ p` is irrelevant, and we write `_` as the
pattern to indicate that the corresponding evidence is unused. We
could instead have written `n≤p` but not used that variable on the
right-hand side of the equation.

In the inductive case, `m ≤ n` holds by `s≤s m≤n`, so it must be that `m`
is of the form `suc m′` and `n` is of the form `suc n′` and `m≤n` is
evidence that `m′ ≤ n′`.  In this case, the only way that `p ≤ n` can
hold is by `s≤s n≤p`, where `p` is of the form `suc p′` and `n≤p` is
evidence that `n′ ≤ p′`.  The inductive hypothesis `trans≤ m≤n n≤p`
provides evidence that `m′ ≤ p′`, and applying `s≤s` to that gives
evidence of the desired conclusion, `suc m′ ≤ suc p′`.

The case `trans≤ (s≤s m≤n) z≤n` cannot arise, since the first piece of
evidence implies `n` must be `suc n′` for some `n′` while the second
implies `n` must be `zero`.  Agda can determine that such a case cannot
arise, and does not require it to be listed.

Alternatively, we could make the implicit parameters explicit.
\begin{code}
trans≤′ : ∀ (m n p : ℕ) → m ≤ n → n ≤ p → m ≤ p
trans≤′ zero n p z≤n _ = z≤n
trans≤′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (trans≤′ m n p m≤n n≤p)
\end{code}
One might argue that this is clearer, since it shows us the forms of `m`, `n`,
and `p`, or one might argue that the extra length obscures the essence of the
proof.  We will usually opt for shorter proofs.

The technique of inducting on evidence that a property holds (e.g.,
inducting on evidence that `m ≤ n`)---rather than induction on the
value of which the property holds (e.g., inducting on `m`)---will turn
out to be immensely valuable, and one that we use often.

Again, it is a good exercise to prove transitivity interactively in Emacs,
using holes and the `^C ^C`, `^C ^,`, and `^C ^R` commands.

## Antisymmetry

The third thing to prove about comparison is that it is antisymmetric:
for all naturals `m` and `n`, if both `m ≤ n` and `n ≤ m` hold, then
`m ≡ n` holds.
\begin{code}
antisym≤ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
antisym≤ z≤n z≤n = refl
antisym≤ (s≤s m≤n) (s≤s n≤m) rewrite antisym≤ m≤n n≤m = refl
\end{code}
Again, the proof is by induction over the evidence that `m ≤ n`
and `n ≤ m` hold, and so we have left `m` and `n` implicit.

In the base case, both relations hold by `z≤n`,
so it must be the case that both `m` and `n` are `zero`,
in which case `m ≡ n` holds by reflexivity. (The reflexivity
of equivlance, that is, not the reflexivity of comparison.)

In the inductive case, `m ≤ n` holds by `s≤s m≤n` and `n ≤ m`
holds by `s≤s n≤m`, 


Any ordering relation that is both reflexive and transitive is called
a *preorder*, and any preorder that is also antisymmetric is a *partial order*.
Hence, we have shown that "less than or equal" is a partial order.  We will
later show that it satisfies the strong property of being a *total order*.

## Monotonicity







\begin{code}
mono+≤ : ∀ (m p q : ℕ) → p ≤ q → m + p ≤ m + q
mono+≤ zero p q p≤q =  p≤q
mono+≤ (suc m) p q p≤q =  s≤s (mono+≤ m p q p≤q)

mono+≤′ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
mono+≤′ m n p m≤n rewrite com+ m p | com+ n p = mono+≤ p m n m≤n

mono+≤″ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
mono+≤″ m n p q m≤n p≤q = trans≤′ (mono+≤′ m n p m≤n) (mono+≤ n p q p≤q)

inverse+∸≤ : ∀ (m n : ℕ) → m ≤ n → (n ∸ m) + m ≡ n
inverse+∸≤ zero n z≤n rewrite com+zero n  = refl
inverse+∸≤ (suc m) (suc n) (s≤s m≤n)
  rewrite com+suc m (n ∸ m) | inverse+∸≤ m n m≤n = refl

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ} → zero < suc n
  s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

infix 4 _<_

<implies≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<implies≤ z<s = s≤s z≤n
<implies≤ (s<s m<n) = s≤s (<implies≤ m<n)

≤implies< : ∀ {m n : ℕ} → suc m ≤ n → m < n
≤implies< (s≤s z≤n) = z<s
≤implies< (s≤s (s≤s m≤n)) = s<s (≤implies< (s≤s m≤n))
\end{code}

## Trichotomy

\begin{code}
_>_ : ℕ → ℕ → Set
n > m = m < n

infix 4 _>_

data Trichotomy : ℕ → ℕ → Set where
  less : ∀ {m n : ℕ} → m < n → Trichotomy m n
  same : ∀ {m n : ℕ} → m ≡ n → Trichotomy m n
  more : ∀ {m n : ℕ} → m > n → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero zero = same refl
trichotomy zero (suc n) = less z<s
trichotomy (suc m) zero = more z<s
trichotomy (suc m) (suc n) with trichotomy m n
... | less m<n = less (s<s m<n)
... | same refl = same refl
... | more n<m = more (s<s n<m)

\end{code}

## Unicode

In this chapter we use the following unicode.

    ≡  U+2261  IDENTICAL TO (\==)
    ∀  U+2200  FOR ALL (\forall)
    λ  U+03BB  GREEK SMALL LETTER LAMBDA (\Gl, \lambda)
