/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# The extension adjoining all p-th roots to a field of characteristic p.

In this file, we introduce the field extension adjoining all `p`-th roots to a
field of characteristic `p`.

# Main definitions and results

* `adjoinPthRoots`: the field extension adjoining all `p`-th roots, defined as the field itself,
  with the algebra map being the frobenius map.
* `adjoinPthRootsPthRoot`: the `p`-th root map `k → adjoinPthRoots k p`, mapping an element
  to its unique `p`-th root in `adjoinPthRoots`. It is implemented as a `RingEquiv` with underlying
  identity map.

-/

public section

variable (k : Type*) [Field k]

/-- Adjoining all `p`-th root to a field of characteristic `p`. -/
@[nolint unusedArguments, expose]
def adjoinPthRoots (p : ℕ) [ExpChar k p] := k

variable (p : ℕ) [ExpChar k p]

instance : Field (adjoinPthRoots k p) := inferInstanceAs (Field k)

instance : Algebra k (adjoinPthRoots k p) := (frobenius k p).toAlgebra

/-- The `p`-th root map `k → adjoinPthRoots k p`, as a `RingEquiv`. -/
def adjoinPthRootsPthRoot : k ≃+* adjoinPthRoots k p := RingEquiv.refl k

lemma adjoinPthRootsPthRoot_apply_pow (x : k) :
    (adjoinPthRootsPthRoot k p x) ^ p = algebraMap k (adjoinPthRoots k p) x := by
  rfl

lemma adjoinPthRootsPthRoot_symm_apply_eq_pow (x : adjoinPthRoots k p) :
    algebraMap k (adjoinPthRoots k p) ((adjoinPthRootsPthRoot k p).symm x) = x ^ p := by
  rfl

instance adjoinPthRoots_purelyInseparable : IsPurelyInseparable k (adjoinPthRoots k p) := by
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (adjoinPthRootsPthRoot k p).symm x
  simp [adjoinPthRootsPthRoot_symm_apply_eq_pow]
