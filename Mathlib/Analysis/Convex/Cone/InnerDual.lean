/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Convex cones in inner product spaces

We define `PointedCone.innerDual` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove the following theorems:
* `ConvexCone.innerDual_of_innerDual_eq_self`:
  The `innerDual` of the `innerDual` of a nonempty, closed, convex cone is itself.
* `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `K` in a complete, real inner product space `H`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).
-/

open Set LinearMap Pointwise

/-! ### The dual cone -/


section Dual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {s t : Set H} {y : H}

open RealInnerProductSpace

namespace PointedCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
def innerDual (s : Set H) : PointedCone ℝ H where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [inner_add_right]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by
    rw [← Nonneg.coe_smul, real_inner_smul_right]; exact mul_nonneg c.2 (hy hx)

@[simp] lemma mem_innerDual : y ∈ innerDual s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫ := .rfl

@[simp] lemma innerDual_empty : innerDual (∅ : Set H) = ⊤ := by ext; simp

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp] lemma innerDual_zero : innerDual (0 : Set H) = ⊤ := by ext; simp

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp]
theorem innerDual_univ : innerDual (univ : Set H) = 0 :=
  le_antisymm (fun x hx ↦ by simpa [← real_inner_self_nonpos] using hx (mem_univ (-x))) (by simp)

@[gcongr] lemma innerDual_le_innerDual (h : t ⊆ s) : innerDual s ≤ innerDual t :=
  fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
lemma innerDual_singleton (x : H) :
    innerDual ({x} : Set H) = (positive ℝ ℝ).comap (innerₛₗ ℝ x) := by ext; simp

theorem innerDual_union (s t : Set H) : innerDual (s ∪ t) = innerDual s ⊓ innerDual t :=
  le_antisymm (le_inf (fun _ hx _ hy ↦ hx <| .inl hy) fun _ hx _ hy ↦ hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h ↦ hx.1 h) (fun h ↦ hx.2 h)

theorem innerDual_insert (x : H) (s : Set H) :
    innerDual (insert x s) = innerDual {x} ⊓ innerDual s := by
  rw [insert_eq, innerDual_union]

theorem innerDual_iUnion {ι : Sort*} (f : ι → Set H) :
    innerDual (⋃ i, f i) = ⨅ i, innerDual (f i) := by
  ext; simp [forall_swap (α := H)]

theorem innerDual_sUnion (S : Set (Set H)) : innerDual (⋃₀ S) = sInf (innerDual '' S) := by
  ext; simp [forall_swap (α := H)]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
theorem innerDual_eq_iInter_innerDual_singleton :
    innerDual s = ⋂ i : s, (innerDual {i.val} : Set H) := by
  ext; simp [forall_swap (α := H)]

theorem isClosed_innerDual : IsClosed (innerDual s : Set H) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [innerDual_eq_iInter_innerDual_singleton]
  apply isClosed_iInter
  intro x
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : innerDual ({↑x} : Set H) = (inner x : H → ℝ) ⁻¹' Set.Ici 0 := by
    rw [innerDual_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')

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

section CompleteSpace

variable [CompleteSpace H]

open scoped InnerProductSpace in
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
    rwa [add_sub_cancel_right, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul,
      ← real_inner_smul_right, neg_smul, one_smul, neg_sub] at hinner
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
      _ ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ := add_le_add rfl.ge hinner₀
      _ = ⟪b - z, b - z + z⟫_ℝ := (inner_add_right _ _ _).symm
      _ = ⟪b - z, b⟫_ℝ := by rw [sub_add_cancel]

/-- The inner dual of inner dual of a non-empty, closed convex cone is itself. -/
theorem ConvexCone.innerDual_of_innerDual_eq_self (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDual : Set H).innerDual = K := by
  ext x
  constructor
  · rw [mem_innerDual, ← SetLike.mem_coe]
    contrapose!
    exact K.hyperplane_separation_of_nonempty_of_isClosed_of_nmem ne hc
  · rintro hxK y h
    specialize h x hxK
    rwa [real_inner_comm]

end CompleteSpace

end Dual


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner dual cone of a pointed cone is a pointed cone. -/
def dual (S : PointedCone ℝ E) : PointedCone ℝ E :=
  ((S : Set E).innerDual).toPointedCone <| pointed_innerDual (S : Set E)

@[simp, norm_cast]
theorem toConvexCone_dual (S : PointedCone ℝ E) : ↑(dual S) = (S : Set E).innerDual :=
  rfl

open scoped InnerProductSpace in
@[simp]
theorem mem_dual {S : PointedCone ℝ E} {y : E} : y ∈ dual S ↔ ∀ ⦃x⦄, x ∈ S → 0 ≤ ⟪x, y⟫_ℝ := by
  rfl

end Dual
