/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ ha)

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ ha)

/-- Compact hausdorff topological fields are finite. -/
instance (priority := 100) {K} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

variable (K)

/-- A topological division ring is a division ring with a topology where all operations are
continuous, including inversion. -/
class IsTopologicalDivisionRing : Prop extends IsTopologicalRing K, HasContinuousInv₀ K

@[deprecated (since := "2025-03-25")] alias TopologicalDivisionRing := IsTopologicalDivisionRing

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [IsTopologicalDivisionRing α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure

theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

end Subfield

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/--
The map `fun x => a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself,
when `a ≠ 0`.
-/
@[simps]
def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]

theorem affineHomeomorph_image_Icc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ico {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioo {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b) := by
  simp [h]

end affineHomeomorph

section LocalExtr

variable {α β : Type*} [TopologicalSpace α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β] {a : α}

open Topology

theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2] with z h3 h4 using(inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open Set

variable {α 𝕜 : Type*} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S := by
  have : DiscreteTopology ({1, -1} : Set 𝕜) := Finite.instDiscreteTopology
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using hsq
  simpa using hS.eqOn_const_of_mapsTo hf hmaps

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) :
    EqOn f g S ∨ EqOn f (-g) S := by
  have hsq : EqOn ((f / g) ^ 2) 1 S := fun x hx => by
    simpa [div_eq_one_iff_eq (pow_ne_zero _ (hg_ne hx)), div_pow] using hsq hx
  simpa +contextual [EqOn, div_eq_iff (hg_ne _)]
    using hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z => hg_ne) hsq

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) {y : α} (hy : y ∈ S)
    (hy' : f y = g y) : EqOn f g S := fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

end Preconnected

section ContinuousSMul

variable {F : Type*} [DivisionRing F] [TopologicalSpace F] [IsTopologicalRing F]
    (X : Type*) [TopologicalSpace X] [MulAction F X] [ContinuousSMul F X]

instance Subfield.continuousSMul (M : Subfield F) : ContinuousSMul M X :=
  Subring.continuousSMul M.toSubring X

end ContinuousSMul
