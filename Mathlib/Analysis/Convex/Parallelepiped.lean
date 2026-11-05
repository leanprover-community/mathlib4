/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Geometry.Convex.Parallelepiped

/-!
# Topological and metric properties of parallelepipeds

See `Mathlib.Geometry.Convex.Parallelepiped` for the purely algebraic theory of parallelepipeds.

## Main statements

* `norm_le_of_mem_parallelepiped`: a point of the parallelepiped spanned by `v` has norm at most
  `∑ i, ‖v i‖`.
* `isCompact_parallelepiped`: parallelepipeds in real normed spaces are compact.
-/

@[expose] public section

open Set

variable {ι E : Type*} [Fintype ι]

section Normed

variable {K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [SeminormedAddCommGroup E] [NormedSpace K E]

theorem norm_le_of_mem_parallelepiped {v : ι → E} {x : E} (hx : x ∈ parallelepiped K v) :
    ‖x‖ ≤ ∑ i, ‖v i‖ := by
  obtain ⟨t, ht, rfl⟩ := hx
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_smul]
  refine mul_le_of_le_one_left (norm_nonneg _) ((norm_le_norm_of_abs_le_abs ?_).trans_eq norm_one)
  rw [abs_of_nonneg (ht.1 i), abs_one]
  exact ht.2 i

theorem isBounded_parallelepiped (v : ι → E) : Bornology.IsBounded (parallelepiped K v) :=
  isBounded_iff_forall_norm_le.2 ⟨_, fun _ ↦ norm_le_of_mem_parallelepiped⟩

theorem isBounded_halfOpenParallelepiped (v : ι → E) :
    Bornology.IsBounded (halfOpenParallelepiped K v) :=
  (isBounded_parallelepiped v).subset (halfOpenParallelepiped_subset_parallelepiped v)

end Normed

theorem isCompact_parallelepiped [NormedAddCommGroup E] [NormedSpace ℝ E] (v : ι → E) :
    IsCompact (parallelepiped ℝ v) :=
  isCompact_Icc.image (by fun_prop)
