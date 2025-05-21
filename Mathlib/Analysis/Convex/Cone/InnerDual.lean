/-
Copyright (c) 2021 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yaël Dillies
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Inner dual cone of a set

We define the inner dual cone of a set `s` in an inner product space to be the proper cone
consisting of all points `y` such that for all `x ∈ s` we have `0 ≤ ⟪x, y⟫`.

## Main statements

We prove the following theorems:
* `ConvexCone.innerDual_of_innerDual_eq_self`:
  The `innerDual` of the `innerDual` of a proper convex cone is itself.
* `ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `K` in a complete, real inner product space `E`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).
-/

open Set LinearMap Pointwise
open scoped RealInnerProductSpace

variable {R E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {s t : Set E} {x x₀ y : E}

/-! ### Dual of a cone in an inner product space -/

namespace PointedCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
def innerDual (s : Set E) : PointedCone ℝ E where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by rw [inner_add_right]; exact add_nonneg (hu hx) (hv hx)
  smul_mem' c y hy x hx := by
    rw [← Nonneg.coe_smul, real_inner_smul_right]; exact mul_nonneg c.2 (hy hx)

@[simp] lemma mem_innerDual : y ∈ innerDual s ↔ ∀ ⦃x⦄, x ∈ s → 0 ≤ ⟪x, y⟫ := .rfl

@[simp] lemma innerDual_empty : innerDual (∅ : Set E) = ⊤ := by ext; simp

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp] lemma innerDual_zero : innerDual (0 : Set E) = ⊤ := by ext; simp

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp]
lemma innerDual_univ : innerDual (univ : Set E) = 0 :=
  le_antisymm (fun x hx ↦ by simpa [← real_inner_self_nonpos] using hx (mem_univ (-x))) (by simp)

@[gcongr] lemma innerDual_le_innerDual (h : t ⊆ s) : innerDual s ≤ innerDual t :=
  fun _y hy _x hx ↦ hy (h hx)

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `fun y ↦ ⟪x, y⟫`. -/
lemma innerDual_singleton (x : E) :
    innerDual ({x} : Set E) = (positive ℝ ℝ).comap (innerₛₗ ℝ x) := by ext; simp

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

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma innerDual_eq_iInter_innerDual_singleton :
    innerDual s = ⋂ i : s, (innerDual {i.val} : Set E) := by
  ext; simp [forall_swap (α := E)]

lemma isClosed_innerDual : IsClosed (innerDual s : Set E) := by
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw [innerDual_eq_iInter_innerDual_singleton]
  refine isClosed_iInter fun x ↦ ?_
  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : innerDual ({↑x} : Set E) = (inner ℝ x : E → ℝ) ⁻¹' Set.Ici 0 := by
    rw [innerDual_singleton]; rfl
  -- the preimage is closed as `inner ℝ x` is continuous and `[0, ∞)` is closed
  rw [h]
  exact isClosed_Ici.preimage (continuous_const.inner continuous_id')

end PointedCone

namespace ProperCone

/-- The dual cone of a set `s` is the cone consisting of all points `y` such that for all points
`x ∈ s` we have `0 ≤ ⟪x, y⟫`. -/
@[simps toSubmodule]
def innerDual (s : Set E) : ProperCone ℝ E where
  toSubmodule := PointedCone.innerDual s
  isClosed' := PointedCone.isClosed_innerDual

@[simp, norm_cast]
lemma toPointedCone_innerDual (s : Set E) : (innerDual s).toPointedCone = .innerDual s := rfl

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

end ProperCone

/-! ### Farkas' lemma and double dual of a cone in a Hilbert space -/

variable [CompleteSpace E] [CompleteSpace F]

/-- Geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem ProperCone.hyperplane_separation' (C : ProperCone ℝ E) (hx₀ : x₀ ∉ C) :
    ∃ y, (∀ x ∈ C, 0 ≤ ⟪x, y⟫) ∧ ⟪x₀, y⟫ < 0 := by
  obtain ⟨f, hf, hf₀⟩ := C.hyperplane_separation_point hx₀
  exact ⟨(InnerProductSpace.toDual ℝ E).symm f,
    by simpa [← real_inner_comm _ ((InnerProductSpace.toDual ℝ E).symm f), *]⟩


/-- The inner dual of inner dual of a proper cone is itself. -/
@[simp] theorem ProperCone.innerDual_innerDual (C : ProperCone ℝ E) :
    innerDual (innerDual (C : Set E)) = C := by
  ext x
  constructor
  · simp only [SetLike.mem_coe, mem_innerDual, mem_setOf_eq]
    contrapose!
    simpa [real_inner_comm x] using C.hyperplane_separation'
  · rintro hx y h
    specialize h hx
    rwa [real_inner_comm]

section CompleteSpace

open scoped InnerProductSpace

/-- Relative geometric interpretation of **Farkas' lemma**. Also stronger version of the
**Hahn-Banach separation theorem** for proper cones. -/
theorem ProperCone.relative_hyperplane_separation {C : ProperCone ℝ E} {f : E →L[ℝ] F} {b : F} :
    b ∈ C.map f ↔ ∀ y : F, f.adjoint y ∈ innerDual C → 0 ≤ ⟪b, y⟫_ℝ where
  mp := by
      -- suppose `b ∈ C.map f`
      simp only [map, ClosedSubmodule.map, Submodule.closure, Submodule.topologicalClosure,
        AddSubmonoid.topologicalClosure, Submodule.coe_toAddSubmonoid, Submodule.map_coe,
        ContinuousLinearMap.coe_restrictScalars, ClosedSubmodule.coe_toSubmodule,
        ClosedSubmodule.mem_mk, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        mem_closure_iff_seq_limit, mem_image, SetLike.mem_coe, mem_innerDual, forall_exists_index,
        and_imp, Classical.skolem, forall_and, ContinuousLinearMap.adjoint_inner_right]
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

end CompleteSpace
