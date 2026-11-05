/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anouk Brose, Sébastien Gouëzel, Justus Springer
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Basis.Defs

import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Analysis.Convex.Combination
import Mathlib.Order.Interval.Set.Pi

/-!
# Parallelepipeds

Closed and half-open parallelepipeds spanned by a finite family of vectors in a module over a
linearly ordered field.

## Main definitions

* `parallelepiped K v`: the parallelepiped spanned by `v`, i.e. all combinations
  `∑ i, t i • v i` with `t i ∈ [0, 1]`.
* `halfOpenParallelepiped K v`: the half-open parallelepiped spanned by `v`, i.e. all combinations
  `∑ i, t i • v i` with `t i ∈ [0, 1)`.
-/

@[expose] public section

open Set Module
open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K]
variable {ι ι' E F : Type*} [Fintype ι] [Fintype ι']
variable [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

section parallelepiped

variable (K) in
/-- The parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → K => ∑ i, t i • v i) '' Icc 0 1

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped K v ↔ ∃ t ∈ Icc (0 : ι → K) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

@[simp]
theorem parallelepiped_of_isEmpty [IsEmpty ι] (v : ι → E) : parallelepiped K v = {0} := by
  simp [parallelepiped]

theorem parallelepiped_basis_eq (b : Basis ι K E) :
    parallelepiped K b = {x | ∀ i, b.repr x i ∈ Set.Icc 0 1} := by
  rw [parallelepiped, ← funext b.equivFun_symm_apply, LinearEquiv.image_symm_eq_preimage]
  ext
  simp [Pi.le_def, forall_and]

theorem image_parallelepiped (f : E →ₗ[K] F) (v : ι → E) :
    f '' parallelepiped K v = parallelepiped K (f ∘ v) := by
  rw [parallelepiped, ← image_comp]
  congr 1 with t
  simp

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped K (v ∘ e) = parallelepiped K v := by
  ext x
  refine (e.arrowCongr (.refl K)).exists_congr fun t ↦ ?_
  simp [Pi.le_def, ← e.sum_comp, e.forall_congr_left]

theorem parallelepiped_prod (v : ι → E) (w : ι' → F) :
    parallelepiped K (Sum.elim (LinearMap.inl K E F ∘ v) (LinearMap.inr K E F ∘ w)) =
      parallelepiped K v ×ˢ parallelepiped K w := by
  ext ⟨x, y⟩
  rw [mem_parallelepiped_iff, (Equiv.sumArrowEquivProdArrow ι ι' K).exists_congr_left]
  simp [mem_parallelepiped_iff, Pi.le_def, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum,
    and_and_and_comm]

variable [IsStrictOrderedRing K]

@[simp]
theorem zero_mem_parallelepiped (v : ι → E) : (0 : E) ∈ parallelepiped K v :=
  (mem_parallelepiped_iff v _).mpr ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩

theorem parallelepiped_eq_sum_segment (v : ι → E) :
    parallelepiped K v = ∑ i, segment K 0 (v i) := by
  simp_rw [parallelepiped, segment_eq_image, smul_zero, zero_add, ← image_fintype_sum_pi,
    ← piMap_image_univ_pi, ← image_comp, pi_univ_Icc, Function.comp_def, Pi.map_apply,
    ← Pi.zero_def, ← Pi.one_def]

/-- A parallelepiped spanned by a single vector is a segment. -/
theorem parallelepiped_unique [Unique ι] (v : ι → E) :
    parallelepiped K v = segment K 0 (v default) := by
  rw [parallelepiped_eq_sum_segment, Finset.univ_unique, Finset.sum_singleton]

theorem convex_parallelepiped (v : ι → E) : Convex K (parallelepiped K v) := by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _ _ => convex_segment _ _

/-- A `parallelepiped` is the convex hull of its vertices -/
theorem parallelepiped_eq_convexHull (v : ι → E) :
    parallelepiped K v = convexHull K (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

/-- The axis aligned parallelepiped over `ι → K` is a cuboid. -/
theorem parallelepiped_single [DecidableEq ι] (a : ι → K) :
    (parallelepiped K fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  have h : (fun t : ι → K ↦ ∑ i, t i • Pi.single i (a i)) = Pi.map fun i ↦ (· * a i) := by
    ext t j
    simp [Pi.single_apply]
  simp_rw [parallelepiped, h, ← pi_univ_Icc, piMap_image_univ_pi, ← pi_univ_uIcc, Pi.zero_apply,
    Pi.one_apply, ← uIcc_of_le zero_le_one, image_mul_const_uIcc, zero_mul, one_mul]

end parallelepiped

section halfOpenParallelepiped

variable (K) in
/-- The half-open parallelepiped spanned by a finite family of vectors. -/
def halfOpenParallelepiped (v : ι → E) : Set E :=
  (fun t : ι → K => ∑ i, t i • v i) '' univ.pi fun _ ↦ Ico 0 1

theorem mem_halfOpenParallelepiped_iff (v : ι → E) (x : E) :
    x ∈ halfOpenParallelepiped K v ↔
      ∃ t : ι → K, (∀ i, t i ∈ Ico (0 : K) 1) ∧ x = ∑ i, t i • v i := by
  simp [halfOpenParallelepiped, eq_comm]

@[simp]
theorem halfOpenParallelepiped_of_isEmpty [IsEmpty ι] (v : ι → E) :
    halfOpenParallelepiped K v = {0} := by
  simp [halfOpenParallelepiped, univ_eq_empty_iff.mpr]

theorem sum_smul_mem_halfOpenParallelepiped (v : ι → E) {t : ι → K}
    (ht : ∀ i, t i ∈ Ico (0 : K) 1) : ∑ i, t i • v i ∈ halfOpenParallelepiped K v :=
  (mem_halfOpenParallelepiped_iff v _).mpr ⟨t, ht, rfl⟩

/-- For linearly independent `v`, a linear combination of `v` lies in the half-open parallelepiped
spanned by `v` if and only if all its coefficients lie in `[0, 1)`. -/
theorem LinearIndependent.sum_smul_mem_halfOpenParallelepiped_iff {v : ι → E}
    (hv : LinearIndependent K v) {t : ι → K} :
    ∑ i, t i • v i ∈ halfOpenParallelepiped K v ↔ ∀ i, t i ∈ Ico (0 : K) 1 := by
  refine ⟨fun h ↦ ?_, sum_smul_mem_halfOpenParallelepiped v⟩
  obtain ⟨t', ht', hsum⟩ := (mem_halfOpenParallelepiped_iff v _).mp h
  exact fun i ↦ Fintype.linearIndependent_iffₛ.mp hv _ _ hsum i ▸ ht' i

theorem halfOpenParallelepiped_basis_eq (b : Basis ι K E) :
    halfOpenParallelepiped K b = {x | ∀ i, b.repr x i ∈ Ico 0 1} := by
  ext x
  conv_lhs => rw [← b.sum_repr x]
  exact b.linearIndependent.sum_smul_mem_halfOpenParallelepiped_iff

theorem image_halfOpenParallelepiped (f : E →ₗ[K] F) (v : ι → E) :
    f '' halfOpenParallelepiped K v = halfOpenParallelepiped K (f ∘ v) := by
  rw [halfOpenParallelepiped, ← image_comp]
  congr 1 with t
  simp

/-- Reindexing a family of vectors does not change their half-open parallelepiped. -/
@[simp]
theorem halfOpenParallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    halfOpenParallelepiped K (v ∘ e) = halfOpenParallelepiped K v := by
  ext x
  refine (e.arrowCongr (.refl K)).exists_congr fun t ↦ ?_
  simp [← e.sum_comp, e.forall_congr_left]

theorem halfOpenParallelepiped_prod (v : ι → E) (w : ι' → F) :
    halfOpenParallelepiped K (Sum.elim (LinearMap.inl K E F ∘ v) (LinearMap.inr K E F ∘ w)) =
      halfOpenParallelepiped K v ×ˢ halfOpenParallelepiped K w := by
  ext ⟨x, y⟩
  rw [mem_halfOpenParallelepiped_iff, (Equiv.sumArrowEquivProdArrow ι ι' K).exists_congr_left]
  simp [mem_halfOpenParallelepiped_iff, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum,
    and_and_and_comm]

theorem halfOpenParallelepiped_subset_parallelepiped (v : ι → E) :
    halfOpenParallelepiped K v ⊆ parallelepiped K v :=
  image_mono fun _ ht ↦ ⟨fun i ↦ (ht i trivial).1, fun i ↦ (ht i trivial).2.le⟩

variable [IsStrictOrderedRing K]

@[simp]
theorem zero_mem_halfOpenParallelepiped (v : ι → E) : (0 : E) ∈ halfOpenParallelepiped K v :=
  (mem_halfOpenParallelepiped_iff v _).mpr ⟨0, by simp⟩

theorem convex_halfOpenParallelepiped (v : ι → E) : Convex K (halfOpenParallelepiped K v) :=
  (convex_pi fun _ _ ↦ convex_Ico 0 1).linear_image (Fintype.linearCombination K v)

end halfOpenParallelepiped
