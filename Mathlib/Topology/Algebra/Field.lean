/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison

! This file was ported from Lean 3 source module topology.algebra.field
! leanprover-community/mathlib commit c10e724be91096453ee3db13862b9fb9a992fef2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.Algebra.GroupWithZero
import Mathbin.Topology.LocalExtr
import Mathbin.FieldTheory.Subfield

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


variable {K : Type _} [DivisionRing K] [TopologicalSpace K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel ha)
#align filter.tendsto_cocompact_mul_left₀ Filter.tendsto_cocompact_mul_left₀

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right₀ [ContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)
#align filter.tendsto_cocompact_mul_right₀ Filter.tendsto_cocompact_mul_right₀

variable (K)

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class TopologicalDivisionRing extends TopologicalRing K, HasContinuousInv₀ K : Prop
#align topological_division_ring TopologicalDivisionRing

section Subfield

variable {α : Type _} [Field α] [TopologicalSpace α] [TopologicalDivisionRing α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  {
    K.toSubring.topologicalClosure with
    carrier := closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv]
        exact mem_closure_image (continuous_at_inv₀ h) hx }
#align subfield.topological_closure Subfield.topologicalClosure

theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  subset_closure
#align subfield.le_topological_closure Subfield.le_topologicalClosure

theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure
#align subfield.is_closed_topological_closure Subfield.isClosed_topologicalClosure

theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align subfield.topological_closure_minimal Subfield.topologicalClosure_minimal

end Subfield

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type _} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜
    where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel]
    exact mul_div_cancel_left x h
  right_inv y := by simp [mul_div_cancel' _ h]
#align affine_homeomorph affineHomeomorph

end affineHomeomorph

section LocalExtr

variable {α β : Type _} [TopologicalSpace α] [LinearOrderedSemifield β] {a : α}

open Topology

theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2]with z h3 h4 using(inv_le_inv h4 h2.self_of_nhds).mpr h3
#align is_local_min.inv IsLocalMin.inv

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/


open Set

variable {α 𝕜 : Type _} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S :=
  by
  simp_rw [eq_on, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] at hsq
  -- First deal with crazy case where `S` is empty.
  by_cases hSe : ∀ x : α, x ∉ S
  · left
    intro x hx
    exfalso
    exact hSe x hx
  push_neg  at hSe
  choose y hy using hSe
  suffices ∀ x : α, x ∈ S → f x = f y by
    rcases hsq hy with ⟨⟩
    · left
      intro z hz
      rw [Pi.one_apply z, ← h]
      exact this z hz
    · right
      intro z hz
      rw [Pi.neg_apply, Pi.one_apply, ← h]
      exact this z hz
  refine' fun x hx => hS.constant_of_maps_to hf (fun z hz => _) hx hy
  show f z ∈ ({-1, 1} : Set 𝕜)
  · exact mem_insert_iff.mpr (hsq hz).symm
  exact discrete_of_t1_of_finite
#align is_preconnected.eq_one_or_eq_neg_one_of_sq_eq IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) :
    EqOn f g S ∨ EqOn f (-g) S :=
  by
  rcases hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z hz => hg_ne hz) fun x hx => _ with
    (h | h)
  · refine' Or.inl fun x hx => _
    rw [← div_eq_one_iff_eq (hg_ne hx)]
    exact h hx
  · refine' Or.inr fun x hx => _
    specialize h hx
    rwa [Pi.div_apply, Pi.neg_apply, Pi.one_apply, div_eq_iff (hg_ne hx), neg_one_mul] at h
  · rw [Pi.one_apply, div_pow, Pi.div_apply, hsq hx, div_self]
    exact pow_ne_zero _ (hg_ne hx)
#align is_preconnected.eq_or_eq_neg_of_sq_eq IsPreconnected.eq_or_eq_neg_of_sq_eq

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [HasContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) {y : α} (hy : y ∈ S)
    (hy' : f y = g y) : EqOn f g S := fun x hx =>
  by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h hy, eq_comm, ← sub_eq_zero, sub_eq_add_neg, Pi.neg_apply, neg_neg, ← mul_two,
      mul_eq_zero] at hy'
    cases hy'
    -- need to handle case of `char 𝕜 = 2` separately
    · exfalso
      exact hg_ne hy hy'
    ·
      rw [h hx, Pi.neg_apply, eq_comm, ← sub_eq_zero, sub_eq_add_neg, neg_neg, ← mul_two, hy',
        mul_zero]
#align is_preconnected.eq_of_sq_eq IsPreconnected.eq_of_sq_eq

end Preconnected

