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
field of (exponential) characteristic `p`.

# Main definitions and results

* `AdjoinPthRoots`: the field extension adjoining all `p`-th roots to a field of
  (exponential) characteristic `p`.
* `AdjoinPthRoots.root`: for `k` a field of (exponential) characteristic `p`, the `p`-th root map
  `k → AdjoinPthRoots k`, mapping an element to its unique `p`-th root in `AdjoinPthRoots`,
  as a `RingEquiv`.

-/

public section

variable (k : Type*) [Field k]

/-- Adjoining all `p`-th root to a field of (exponential) characteristic `p`. -/
-- Note: It is defined as a typeclass synonym of the field `k` itself
-- with a `k`-algebra structure given by the frobenius map.
def AdjoinPthRoots := k

@[no_expose]
noncomputable instance : Field (AdjoinPthRoots k) := inferInstanceAs (Field k)

@[no_expose]
noncomputable instance : Algebra k (AdjoinPthRoots k) := (frobenius k (ringExpChar k)).toAlgebra

instance (p : ℕ) [ExpChar k p] : ExpChar (AdjoinPthRoots k) p := inferInstanceAs (ExpChar k p)

/-- For `k` a field of (exponential) characteristic `p`,
the `p`-th root map `k → AdjoinPthRoots k`, as a `RingEquiv`. -/
noncomputable def AdjoinPthRoots.root : k ≃+* AdjoinPthRoots k := RingEquiv.refl k

variable {k} (p : ℕ) [ExpChar k p]

@[simp]
lemma AdjoinPthRoots.root_pow (x : k) :
    (AdjoinPthRoots.root k x) ^ p = algebraMap k (AdjoinPthRoots k) x := by
  rw [← ringExpChar.eq k p]
  rfl

lemma AdjoinPthRoots.algebraMap_root_symm (x : AdjoinPthRoots k) :
    algebraMap k (AdjoinPthRoots k) ((AdjoinPthRoots.root k).symm x) = x ^ p := by
  rw [← ringExpChar.eq k p]
  rfl

instance : IsPurelyInseparable k (AdjoinPthRoots k) := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  rw [isPurelyInseparable_iff_pow_mem k p]
  intro x
  use 1, (AdjoinPthRoots.root k).symm x
  simp [AdjoinPthRoots.algebraMap_root_symm p]
