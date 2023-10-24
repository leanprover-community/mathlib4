/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Sub.Defs

/-! # Antidiagonal with values in general types

Let `μ` be an AddCommMonoid.

* We define a type class `HasAntidiagonal` which contains a function
`antidiagonal : μ → Finset (μ × μ)` such that `antidiagonal n`
is the Finset of all pairs adding to `n`, as witnessed by `mem_antidiagonal`.

Assume that `μ` is a canonically ordered add monoid with locally finite order.
For example, one may take `μ` to be `ℕ`, more generally `σ →₀ ℕ`.

* `Finset.antidiagonalOfLocallyFinite` is a member of this type class.

These functions apply to (ι →₀ ℕ), more generally to (ι →₀ μ)
  under the additional assumption `OrderedSub μ` that make it a canonically ordered add monoid.
  In fact, we just need an AddMonoid with a compatible order,
  finite Iic, such that if a + b = n, then a, b ≤ n,
  and any finiteness condition would be OK.

However, it is not made as an instance because in specific cases,
there are more efficient definitions of the antidiagonal.
For instance, `Mathlib.Data.Finset.NatAntidiagonal`
and `Mathlib.Data.Finsupp.Antidiagonal` declare such instances.

This definition does not exactly match with that of `Multiset.antidiagonal` which is
defined in `Mathlib.Data.Multiset.Antidiagonal`, because of the multiplicities.
Indeed, by counting multiplicities, `Multiset α` is equivalent to `α →₀ ℕ`,
but `Finset.antidiagonal` and `Multiset.antidiagonal` will return different objects.
For example, for `s : Multiset ℕ := {0,0,0}`, `Multiset.antidiagonal s` has 8 elements
but `Finset.antidiagonal s` has only 4.

```lean
def s : Multiset ℕ := {0, 0, 0}
#eval (Finset.antidiagonal s).card -- 4
#eval Multiset.card (Multiset.antidiagonal s) -- 8
```

## TODO

* Define `HasMulAntidiagonal` (for monoids).
For `PNat`, we will recover the set of divisors of a strictly positive integer.

-/

namespace Finset

open scoped BigOperators

open Function

/-- The class of additive monoids with an antidiagonal -/
class HasAntidiagonal (μ : Type*) [AddMonoid μ] where
  /-- The antidiagonal of an element `n` is the finset of pairs `(i, j)` such that `i + j = n`. -/
  antidiagonal : μ → Finset (μ × μ)
  /-- A pair belongs to `antidiagonal n` iff the sum of its components is equal to `n` -/
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n

export HasAntidiagonal (antidiagonal mem_antidiagonal)

attribute [simp] mem_antidiagonal

/-- All HasAntidiagonal are equal -/
instance (μ : Type*) [AddMonoid μ] :
    Subsingleton (HasAntidiagonal μ) := by
  apply Subsingleton.intro
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  suffices : a = b
  simp_rw [this]
  ext n xy
  rw [ha, hb]

-- The goal of these two functions is to allow to rewrite antidiagonal/mem_antidiagonal
-- when the decidability instances obsucate Lean
-- Are they useful at all?
lemma HasAntidiagonal.antidiagonal_rfl (μ : Type*) [AddMonoid μ]
    [H1 : HasAntidiagonal μ] [H2 : HasAntidiagonal μ] :
    H1.antidiagonal = H2.antidiagonal := by
  have : H1 = H2 := by
    apply Subsingleton.elim
  rw [this]

lemma HasAntidiagonal.mem_antidiagonal' (μ : Type*) [AddMonoid μ]
    [HasAntidiagonal μ] (n : μ) (p : μ × μ):
    p ∈ antidiagonal n ↔ p.fst + p.snd = n := mem_antidiagonal

variable {μ : Type*}
  [CanonicallyOrderedAddCommMonoid μ]
  [LocallyFiniteOrder μ] [DecidableEq μ]

/-- In a canonically ordered add monoid, the antidiagonal can be construct by filtering.

Note that this is not an instance, as for some times a more efficient algorithm is available. -/
abbrev antidiagonalOfLocallyFinite : HasAntidiagonal μ where
  antidiagonal n := Finset.filter (fun uv => uv.fst + uv.snd = n) (Finset.product (Iic n) (Iic n))
  mem_antidiagonal {n} {a} := by
    simp only [Prod.forall, mem_filter, and_iff_right_iff_imp]
    intro h; rw [← h]
    erw [mem_product, mem_Iic, mem_Iic]
    exact ⟨le_self_add, le_add_self⟩

end Finset
