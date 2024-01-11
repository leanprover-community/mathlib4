/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Projection

#align_import analysis.convex.cone.dual from "leanprover-community/mathlib"@"915591b2bb3ea303648db07284a161a7f2a9e3d4"

/-!
# Convex cones in inner product spaces

We define `Set.innerDualCone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove the following theorems:
* `ConvexCone.innerDualCone_of_innerDualCone_eq_self`:
  The `innerDualCone` of the `innerDualCone` of a nonempty, closed, convex cone is itself.

-/


open Set LinearMap

open Classical Pointwise

variable {𝕜 E F G : Type*}

/-! ### The dual cone -/


section Dual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (s t : Set H)

open RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
def Set.innerDualCone (s : Set H) : ConvexCone ℝ H where
  carrier := { y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫ }
  smul_mem' c hc y hy x hx := by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' u hu v hv x hx := by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)
#align set.inner_dual_cone Set.innerDualCone

@[simp]
theorem mem_innerDualCone (y : H) (s : Set H) : y ∈ s.innerDualCone ↔ ∀ x ∈ s, 0 ≤ ⟪x, y⟫ :=
  Iff.rfl
#align mem_inner_dual_cone mem_innerDualCone

@[simp]
theorem innerDualCone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => False.elim
#align inner_dual_cone_empty innerDualCone_empty

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp]
theorem innerDualCone_zero : (0 : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ y (hy : y = 0) => hy.symm ▸ (inner_zero_left _).ge
#align inner_dual_cone_zero innerDualCone_zero

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp]
theorem innerDualCone_univ : (univ : Set H).innerDualCone = 0 := by
  suffices ∀ x : H, x ∈ (univ : Set H).innerDualCone → x = 0 by
    apply SetLike.coe_injective
    exact eq_singleton_iff_unique_mem.mpr ⟨fun x _ => (inner_zero_right _).ge, this⟩
  exact fun x hx => by simpa [← real_inner_self_nonpos] using hx (-x) (mem_univ _)
#align inner_dual_cone_univ innerDualCone_univ

theorem innerDualCone_le_innerDualCone (h : t ⊆ s) : s.innerDualCone ≤ t.innerDualCone :=
  fun _ hy x hx => hy x (h hx)
#align inner_dual_cone_le_inner_dual_cone innerDualCone_le_innerDualCone

theorem pointed_innerDualCone : s.innerDualCone.Pointed := fun x _ => by rw [inner_zero_right]
#align pointed_inner_dual_cone pointed_innerDualCone

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
theorem innerDualCone_singleton (x : H) :
    ({x} : Set H).innerDualCone = (ConvexCone.positive ℝ ℝ).comap (innerₛₗ ℝ x) :=
  ConvexCone.ext fun _ => forall_eq
#align inner_dual_cone_singleton innerDualCone_singleton

theorem innerDualCone_union (s t : Set H) :
    (s ∪ t).innerDualCone = s.innerDualCone ⊓ t.innerDualCone :=
  le_antisymm (le_inf (fun _ hx _ hy => hx _ <| Or.inl hy) fun _ hx _ hy => hx _ <| Or.inr hy)
    fun _ hx _ => Or.rec (hx.1 _) (hx.2 _)
#align inner_dual_cone_union innerDualCone_union

theorem innerDualCone_insert (x : H) (s : Set H) :
    (insert x s).innerDualCone = Set.innerDualCone {x} ⊓ s.innerDualCone := by
  rw [insert_eq, innerDualCone_union]
#align inner_dual_cone_insert innerDualCone_insert

theorem innerDualCone_iUnion {ι : Sort*} (f : ι → Set H) :
    (⋃ i, f i).innerDualCone = ⨅ i, (f i).innerDualCone := by
  refine' le_antisymm (le_iInf fun i x hx y hy => hx _ <| mem_iUnion_of_mem _ hy) _
  intro x hx y hy
  rw [ConvexCone.mem_iInf] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact hx _ _ hj
#align inner_dual_cone_Union innerDualCone_iUnion

theorem innerDualCone_sUnion (S : Set (Set H)) :
    (⋃₀ S).innerDualCone = sInf (Set.innerDualCone '' S) := by
  simp_rw [sInf_image, sUnion_eq_biUnion, innerDualCone_iUnion]
#align inner_dual_cone_sUnion innerDualCone_sUnion

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
theorem innerDualCone_eq_iInter_innerDualCone_singleton :
    (s.innerDualCone : Set H) = ⋂ i : s, (({↑i} : Set H).innerDualCone : Set H) := by
  rw [← ConvexCone.coe_iInf, ← innerDualCone_iUnion, iUnion_of_singleton_coe]
#align inner_dual_cone_eq_Inter_inner_dual_cone_singleton innerDualCone_eq_iInter_innerDualCone_singleton

theorem isClosed_innerDualCone : IsClosed (s.innerDualCone : Set H) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [innerDualCone_eq_iInter_innerDualCone_singleton]
  apply isClosed_iInter
  intro x
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ({↑x} : Set H).innerDualCone = (inner x : H → ℝ) ⁻¹' Set.Ici 0 := by
    rw [innerDualCone_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')

#align is_closed_inner_dual_cone isClosed_innerDualCone

theorem ConvexCone.pointed_of_nonempty_of_isClosed (K : ConvexCone ℝ H) (ne : (K : Set H).Nonempty)
    (hc : IsClosed (K : Set H)) : K.Pointed := by
  obtain ⟨x, hx⟩ := ne
  let f : ℝ → H := (· • x)
  -- f (0, ∞) is a subset of K
  have fI : f '' Set.Ioi 0 ⊆ (K : Set H) := by
    rintro _ ⟨_, h, rfl⟩
    exact K.smul_mem (Set.mem_Ioi.1 h) hx
  -- closure of f (0, ∞) is a subset of K
  have clf : closure (f '' Set.Ioi 0) ⊆ (K : Set H) := hc.closure_subset_iff.2 fI
  -- f is continuous at 0 from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : ℝ)) 0 :=
    (continuous_id.smul continuous_const).continuousWithinAt
  -- 0 belongs to the closure of the f (0, ∞)
  have mem₀ := fc.mem_closure_image (by rw [closure_Ioi (0 : ℝ), mem_Ici])
  -- as 0 ∈ closure f (0, ∞) and closure f (0, ∞) ⊆ K, 0 ∈ K.
  have f₀ : f 0 = 0 := zero_smul ℝ x
  simpa only [f₀, ConvexCone.Pointed, ← SetLike.mem_coe] using mem_of_subset_of_mem clf mem₀
#align convex_cone.pointed_of_nonempty_of_is_closed ConvexCone.pointed_of_nonempty_of_isClosed

section CompleteSpace

variable [CompleteSpace H]

/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) {b : H} (disj : b ∉ K) :
    ∃ y : H, (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 := by
  -- let `z` be the point in `K` closest to `b`
  obtain ⟨z, hzK, infi⟩ := exists_norm_eq_iInf_of_complete_convex ne hc.isComplete K.convex b
  -- for any `w` in `K`, we have `⟪b - z, w - z⟫_ℝ ≤ 0`
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero K.convex hzK).1 infi
  -- set `y := z - b`
  use z - b
  constructor
  · -- the rest of the proof is a straightforward calculation
    rintro x hxK
    specialize hinner _ (K.add_mem hxK hzK)
    rwa [add_sub_cancel, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul, ← real_inner_smul_right,
      neg_smul, one_smul, neg_sub] at hinner
  · -- as `K` is closed and non-empty, it is pointed
    have hinner₀ := hinner 0 (K.pointed_of_nonempty_of_isClosed ne hc)
    -- the rest of the proof is a straightforward calculation
    rw [zero_sub, inner_neg_right, Right.neg_nonpos_iff] at hinner₀
    have hbz : b - z ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! hzK
      rwa [← hzK]
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul]
    calc
      0 < ⟪b - z, b - z⟫_ℝ := lt_of_not_le ((Iff.not real_inner_self_nonpos).2 hbz)
      _ = ⟪b - z, b - z⟫_ℝ + 0 := (add_zero _).symm
      _ ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ := (add_le_add rfl.ge hinner₀)
      _ = ⟪b - z, b - z + z⟫_ℝ := (inner_add_right _ _ _).symm
      _ = ⟪b - z, b⟫_ℝ := by rw [sub_add_cancel]

#align convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem

/-- The inner dual of inner dual of a non-empty, closed convex cone is itself.  -/
theorem ConvexCone.innerDualCone_of_innerDualCone_eq_self (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDualCone : Set H).innerDualCone = K := by
  ext x
  constructor
  · rw [mem_innerDualCone, ← SetLike.mem_coe]
    contrapose!
    exact K.hyperplane_separation_of_nonempty_of_isClosed_of_nmem ne hc
  · rintro hxK y h
    specialize h x hxK
    rwa [real_inner_comm]
#align convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self ConvexCone.innerDualCone_of_innerDualCone_eq_self

end CompleteSpace

end Dual
