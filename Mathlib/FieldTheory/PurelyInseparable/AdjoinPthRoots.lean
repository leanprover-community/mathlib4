/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# The extension of adjoining all pth root to a field of characteriatic p.

In this file, we introduced the field extension of adjoining all `p`th roots to
a field of characteristic `p`.

# Main definitions and results

* `adjoinPthRoots` : the field extension of adjoining all `p`th roots, defined as the field itself,
  with algebra map being the frobenius.

* `adjoinPthRootsSelf` : the underlying identity map, equal to the `p`th power of the
  original element after mapped by algebra map.

* `adjoinPthRootsPthRoot` : the underlying identity map, mapping an element to its unique
  `p`-th root in `adjoinPthRoots`, inverse to `adjoinPthRootsSelf`.

-/

public section

variable (k : Type*) [Field k]

/-- Adjoining all `p`-th root to a field of characteristic `p`.
It is defined as the field itself with algebra map being the frobenius map. -/
@[nolint unusedArguments, expose]
def adjoinPthRoots (p : ℕ) [ExpChar k p] := k

variable (p : ℕ) [ExpChar k p]

instance : Field (adjoinPthRoots k p) := inferInstanceAs (Field k)

instance : Algebra k (adjoinPthRoots k p) := (frobenius k p).toAlgebra

/-- The equivalence `k ≃ adjoinPthRoots k p` with underlying map id. -/
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
