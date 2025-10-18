/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner dual cone of a set

We define the inner dual cone of a set `s` in an inner product space to be the proper cone
consisting of all points `y` such that `0 ≤ ⟪x, y⟫` for all `x ∈ s`.

## Main statements

We prove the following theorems:
* `ProperCone.innerDual_innerDual`: The double inner dual of a proper convex cone is itself.
* `ProperCone.hyperplane_separation'`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `C` in a complete, real inner product space `E`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).

## Implementation notes

We do not provide `ConvexCone`- nor `PointedCone`-valued versions of `ProperCone.innerDual` since
the inner dual cone of any set is always closed and contains `0`, i.e. is a proper cone.
Furthermore, the strict version `{y | ∀ x ∈ s, 0 < ⟪x, y⟫}` is a candidate to the name
`ConvexCone.innerDual`.
-/

open Set LinearMap Pointwise
open scoped RealInnerProductSpace

variable {R E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {s t : Set E} {x x₀ y : E}

open Function

namespace ProperCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
@[simps! toSubmodule]
def innerDual (s : Set E) : ProperCone ℝ E := .dual (innerₗ E) s

@[simp] lemma mem_innerDual : y ∈ innerDual s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫ := .rfl

@[simp] lemma innerDual_empty : innerDual (∅ : Set E) = ⊤ := by ext; simp

/-- Dual cone of the convex cone `{0}` is the total space. -/
@[simp] lemma innerDual_zero : innerDual (0 : Set E) = ⊤ := by ext; simp

/-- Dual cone of the total space is the convex cone `{0}`. -/
@[simp]
lemma innerDual_univ : innerDual (univ : Set E) = ⊥ :=
  le_antisymm (fun x hx ↦ by simpa [← real_inner_self_nonpos] using hx (mem_univ (-x))) (by simp)

@[gcongr] lemma innerDual_le_innerDual (h : t ⊆ s) : innerDual s ≤ innerDual t :=
  fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
lemma innerDual_singleton (x : E) :
    innerDual ({x} : Set E) = (positive ℝ ℝ).comap (innerSL ℝ x) := by ext; simp

lemma innerDual_union (s t : Set E) : innerDual (s ∪ t) = innerDual s ⊓ innerDual t :=
  le_antisymm (le_inf (fun _ hx _ hy ↦ hx <| .inl hy) fun _ hx _ hy ↦ hx <| .inr hy)
    fun _ hx _ => Or.rec (fun h ↦ hx.1 h) (fun h ↦ hx.2 h)

lemma innerDual_insert (x : E) (s : Set E) :
    innerDual (insert x s) = innerDual {x} ⊓ innerDual s := by
  rw [insert_eq, innerDual_union]

lemma innerDual_iUnion {ι : Sort*} (f : ι → Set E) :
    innerDual (⋃ i, f i) = ⨅ i, innerDual (f i) := by
  ext; simp [forall_swap (α := E)]

lemma innerDual_sUnion (S : Set (Set E)) : innerDual (⋃₀ S) = sInf (innerDual '' S) := by
  ext; simp [forall_swap (α := E)]

/-! ### Farkas' lemma and double dual of a cone in a Hilbert space -/

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem hyperplane_separation' (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ y, (∀ x ∈ C, 0 ≤ ⟪x, y⟫) ∧ ⟪x₀, y⟫ < 0 := by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, ?_⟩
  simpa [← real_inner_comm _ ((InnerProductSpace.toDual ℝ E).symm f), *]

/-- The inner dual of inner dual of a proper cone is itself. -/
@[simp] theorem innerDual_innerDual (C : ProperCone ℝ E) :
    innerDual (innerDual (C : Set E)) = C := by
  simpa using C.dual_flip_dual (innerₗ E)

open scoped InnerProductSpace

/-- Relative geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem relative_hyperplane_separation {C : ProperCone ℝ E} {f : E →L[ℝ] F} {b : F} :
    b ∈ C.map f ↔ ∀ y : F, f.adjoint y ∈ innerDual C → 0 ≤ ⟪b, y⟫_ℝ where
  mp := by
    -- suppose `b ∈ C.map f`
    simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
      AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
      ContinuousLinearMap.coe_restrictScalars', ClosedSubmodule.coe_toSubmodule,
      ClosedSubmodule.mem_mk, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, Classical.skolem, forall_and,
      mem_innerDual, ContinuousLinearMap.adjoint_inner_right, forall_exists_index, and_imp]
          -- there is a sequence `seq : ℕ → F` in the image of `f` that converges to `b`
    rintro x seq hmem hx htends y hinner
    obtain rfl : f ∘ seq = x := funext hx
    have h n : 0 ≤ ⟪f (seq n), y⟫_ℝ := by simpa [real_inner_comm] using hinner (hmem n)
    exact ge_of_tendsto' ((continuous_id.inner continuous_const).seqContinuous htends) h
  mpr h := by
    -- By contradiction, suppose `b ∉ C.map f`.
    contrapose! h
    -- as `b ∉ C.map f`, there is a hyperplane `y` separating `b` from `C.map f`
    obtain ⟨y, hxy, hyb⟩ := (C.map f).hyperplane_separation' h
    -- the rest of the proof is a straightforward algebraic manipulation
    refine ⟨y, fun x hx ↦ ?_, hyb⟩
    simpa [ContinuousLinearMap.adjoint_inner_right]
      using hxy (f x) (subset_closure <| mem_image_of_mem _ hx)

theorem hyperplane_separation_of_notMem (K : ProperCone ℝ E) {f : E →L[ℝ] F} {b : F}
    (disj : b ∉ K.map f) :
    ∃ y : F, ContinuousLinearMap.adjoint f y ∈ innerDual K ∧ ⟪b, y⟫_ℝ < 0 := by
  contrapose! disj; rwa [K.relative_hyperplane_separation]

@[deprecated (since := "2025-05-24")]
alias hyperplane_separation_of_nmem := ProperCone.hyperplane_separation_of_notMem

end ProperCone

section Dual

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (s t : Set H)

open RealInnerProductSpace

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
@[deprecated ProperCone.innerDual (since := "2025-07-06")]
def Set.innerDualCone (s : Set H) : ConvexCone ℝ H where
  carrier := { y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫ }
  smul_mem' c hc y hy x hx := by
    rw [real_inner_smul_right]
    exact mul_nonneg hc.le (hy x hx)
  add_mem' u hu v hv x hx := by
    rw [inner_add_right]
    exact add_nonneg (hu x hx) (hv x hx)

set_option linter.deprecated false in
@[deprecated ProperCone.mem_innerDual (since := "2025-07-06")]
theorem mem_innerDualCone (y : H) (s : Set H) : y ∈ s.innerDualCone ↔ ∀ x ∈ s, 0 ≤ ⟪x, y⟫ :=
  Iff.rfl

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_empty (since := "2025-07-06")]
theorem innerDualCone_empty : (∅ : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => False.elim

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_zero (since := "2025-07-06")]
theorem innerDualCone_zero : (0 : Set H).innerDualCone = ⊤ :=
  eq_top_iff.mpr fun _ _ y (hy : y = 0) => hy.symm ▸ (inner_zero_left _).ge

set_option linter.deprecated false in
/-- Dual cone of the total space is the convex cone {0}. -/
@[deprecated ProperCone.innerDual_univ (since := "2025-07-06")]
theorem innerDualCone_univ : (univ : Set H).innerDualCone = 0 := by
  suffices ∀ x : H, x ∈ (univ : Set H).innerDualCone → x = 0 by
    apply SetLike.coe_injective
    exact eq_singleton_iff_unique_mem.mpr ⟨fun x _ => (inner_zero_right _).ge, this⟩
  exact fun x hx => by simpa [← real_inner_self_nonpos] using hx (-x) (mem_univ _)

variable {s t} in
set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_le_innerDual (since := "2025-07-06")]
theorem innerDualCone_le_innerDualCone (h : t ⊆ s) : s.innerDualCone ≤ t.innerDualCone :=
  fun _ hy x hx => hy x (h hx)

set_option linter.deprecated false in
@[deprecated ProperCone.pointed_toConvexCone (since := "2025-07-06")]
theorem pointed_innerDualCone : s.innerDualCone.Pointed := fun x _ => by rw [inner_zero_right]

set_option linter.deprecated false in
/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
@[deprecated ProperCone.innerDual_singleton (since := "2025-07-06")]
theorem innerDualCone_singleton (x : H) :
    ({x} : Set H).innerDualCone = (ConvexCone.positive ℝ ℝ).comap (innerₛₗ ℝ x) :=
  ConvexCone.ext fun _ => forall_eq

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_union (since := "2025-07-06")]
theorem innerDualCone_union (s t : Set H) :
    (s ∪ t).innerDualCone = s.innerDualCone ⊓ t.innerDualCone :=
  le_antisymm (le_inf (fun _ hx _ hy => hx _ <| Or.inl hy) fun _ hx _ hy => hx _ <| Or.inr hy)
    fun _ hx _ => Or.rec (hx.1 _) (hx.2 _)

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_insert (since := "2025-07-06")]
theorem innerDualCone_insert (x : H) (s : Set H) :
    (insert x s).innerDualCone = Set.innerDualCone {x} ⊓ s.innerDualCone := by
  rw [insert_eq, innerDualCone_union]

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_iUnion (since := "2025-07-06")]
theorem innerDualCone_iUnion {ι : Sort*} (f : ι → Set H) :
    (⋃ i, f i).innerDualCone = ⨅ i, (f i).innerDualCone := by
  refine le_antisymm (le_iInf fun i x hx y hy => hx _ <| mem_iUnion_of_mem _ hy) ?_
  intro x hx y hy
  rw [ConvexCone.mem_iInf] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact hx _ _ hj

set_option linter.deprecated false in
@[deprecated ProperCone.innerDual_sUnion (since := "2025-07-06")]
theorem innerDualCone_sUnion (S : Set (Set H)) :
    (⋃₀ S).innerDualCone = sInf (Set.innerDualCone '' S) := by
  simp_rw [sInf_image, sUnion_eq_biUnion, innerDualCone_iUnion]

set_option linter.deprecated false in
/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
@[deprecated "No replacement" (since := "2025-07-06")]
theorem innerDualCone_eq_iInter_innerDualCone_singleton :
    (s.innerDualCone : Set H) = ⋂ i : s, (({↑i} : Set H).innerDualCone : Set H) := by
  rw [← ConvexCone.coe_iInf, ← innerDualCone_iUnion, iUnion_of_singleton_coe]

set_option linter.deprecated false in
@[deprecated ProperCone.isClosed (since := "2025-07-06")]
theorem isClosed_innerDualCone : IsClosed (s.innerDualCone : Set H) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [innerDualCone_eq_iInter_innerDualCone_singleton]
  apply isClosed_iInter
  intro x
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ({↑x} : Set H).innerDualCone = (inner ℝ (x : H)) ⁻¹' Set.Ici 0 := by
    rw [innerDualCone_singleton, ConvexCone.coe_comap, ConvexCone.coe_positive, innerₛₗ_apply_coe]
  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')

namespace PointedCone

set_option linter.deprecated false in
@[deprecated "Now irrelevant" (since := "2025-07-06")]
lemma toConvexCone_dual (C : PointedCone ℝ H) :
    (dual (innerₗ H) (C : Set H)).toConvexCone = (C : Set H).innerDualCone := rfl

end PointedCone

namespace ProperCone

set_option linter.deprecated false in
@[deprecated "Now irrelevant" (since := "2025-07-06")]
lemma coe_dual [CompleteSpace H] (C : ProperCone ℝ H) :
    dual (innerₗ H) C = (C : Set H).innerDualCone := rfl

end ProperCone

section CompleteSpace

variable [CompleteSpace H]

open scoped InnerProductSpace in
/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem (K : ConvexCone ℝ H)
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
    have hinner₀ := hinner 0 (ConvexCone.Pointed.of_nonempty_of_isClosed (C := K) ne hc)
    -- the rest of the proof is a straightforward calculation
    rw [zero_sub, inner_neg_right, Right.neg_nonpos_iff] at hinner₀
    have hbz : b - z ≠ 0 := by
      rw [sub_ne_zero]
      contrapose! hzK
      rwa [← hzK]
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul]
    calc
      0 < ⟪b - z, b - z⟫_ℝ := lt_of_not_ge ((Iff.not real_inner_self_nonpos).2 hbz)
      _ = ⟪b - z, b - z⟫_ℝ + 0 := (add_zero _).symm
      _ ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ := add_le_add rfl.ge hinner₀
      _ = ⟪b - z, b - z + z⟫_ℝ := (inner_add_right _ _ _).symm
      _ = ⟪b - z, b⟫_ℝ := by rw [sub_add_cancel]

@[deprecated (since := "2025-05-24")]
alias ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem :=
  ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem

set_option linter.deprecated false in
/-- The inner dual of inner dual of a non-empty, closed convex cone is itself. -/
@[deprecated ProperCone.innerDual_innerDual (since := "2025-07-06")]
theorem ConvexCone.innerDualCone_of_innerDualCone_eq_self (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) :
    ((K : Set H).innerDualCone : Set H).innerDualCone = K := by
  ext x
  constructor
  · rw [mem_innerDualCone, ← SetLike.mem_coe]
    contrapose!
    exact K.hyperplane_separation_of_nonempty_of_isClosed_of_notMem ne hc
  · rintro hxK y h
    specialize h x hxK
    rwa [real_inner_comm]

namespace ProperCone
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

set_option linter.deprecated false in
/-- The dual of the dual of a proper cone is itself. -/
@[deprecated ProperCone.innerDual_innerDual (since := "2025-07-06")]
theorem dual_dual (K : ProperCone ℝ H) : innerDual (innerDual (K : Set H)) = K :=
  ProperCone.toPointedCone_injective <| PointedCone.toConvexCone_injective <|
    (K : ConvexCone ℝ H).innerDualCone_of_innerDualCone_eq_self K.nonempty K.isClosed

end ProperCone

end CompleteSpace

end Dual
