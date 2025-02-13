/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree

/-!
# Lemmas about extensions by Abelian groups

This file gives lemmas about group extensions `1 → N → E → G → 1` that hold when `N` is Abelian.

For the main definitions, see `Mathlib/GroupTheory/GroupExtension/Defs.lean`. For basic lemmas about
group extensions in general, see `Mathlib/GroupTheory/GroupExtension/Basic.lean`.

## Main definition

- `SemidirectProduct.conjClassesEquivH1 (φ : G →* MulAut N)`: the bijection between the
  `N`-conjugacy classes of splittings associated to the semidirect product `G ⋊[φ] N` and
  $H^1 (G, N)$

## References

* [Kenneth S. Brown, *Cohomology of groups*][brown1982]

-/

namespace SemidirectProduct

variable {N G : Type} [CommGroup N] [Group G] (φ : G →* MulAut N)

/-- The `ℤ`-linear `G`-representation associated to a multiplicative action -/
noncomputable def toRep : Rep ℤ G :=
  @Rep.ofMulDistribMulAction G N _ _ (MulDistribMulAction.compHom N φ)

theorem toRep_ρ_apply_apply (g : G) (n : Additive N) :
    ((toRep φ).ρ g) n = Additive.ofMul (φ g (Additive.toMul n)) := rfl

/-- Returns the 1-cocycle corresponding to a splitting. -/
def splittingToOneCocycle (s : (toGroupExtension φ).Splitting) :
    groupCohomology.oneCocycles (toRep φ) where
  val g := Additive.ofMul (α := N) (s g).left
  property := by
    rw [groupCohomology.mem_oneCocycles_iff]
    intro g₁ g₂
    rw [toRep_ρ_apply_apply, toMul_ofMul, map_mul, mul_left, mul_comm, ← ofMul_mul, right_splitting]

/-- Returns the splitting corresponding to a 1-cocycle. -/
def splittingOfOneCocycle (f : groupCohomology.oneCocycles (toRep φ)) :
    (toGroupExtension φ).Splitting where
  toFun g := ⟨Additive.toMul (f g), g⟩
  map_one' := by
    ext
    · simp only [one_left, groupCohomology.oneCocycles_map_one, toMul_zero]
    · simp only [one_right]
  map_mul' g₁ g₂ := by
    ext
    · simp only [mul_left]
      rw [(groupCohomology.mem_oneCocycles_iff f).mp f.property g₁ g₂, toMul_add, mul_comm,
        toRep_ρ_apply_apply, toMul_ofMul]
    · simp only [mul_right]
  rightInverse_rightHom g := by simp only [toGroupExtension_rightHom, rightHom_eq_right]

/-- The bijection between the splittings of the group extension associated to a semidirect product
  and the 1-cocycles -/
def splittingEquivOneCocycles :
    (toGroupExtension φ).Splitting ≃ groupCohomology.oneCocycles (toRep φ) where
  toFun := splittingToOneCocycle φ
  invFun := splittingOfOneCocycle φ
  left_inv s := by
    unfold splittingToOneCocycle splittingOfOneCocycle
    congr
    ext g
    <;> congr
    <;> exact (s.rightHom_splitting g).symm
  right_inv f := by
    unfold splittingToOneCocycle splittingOfOneCocycle
    ext g
    simp only [mk_eq_inl_mul_inr, GroupExtension.Splitting.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      mul_left, left_inl, right_inl, map_one, left_inr, MulAut.one_apply, mul_one, ofMul_toMul,
      groupCohomology.oneCocycles.coe_mk]

/-- Two splittings are `N`-conjugates iff the difference of the corresponding 1-cocycles is a
  1-coboundary. -/
theorem isConj_iff_sub_mem_oneCoboundaries (s₁ s₂ : (toGroupExtension φ).Splitting) :
    (toGroupExtension φ).IsConj s₁ s₂ ↔
    splittingToOneCocycle φ s₁ - splittingToOneCocycle φ s₂ ∈
    groupCohomology.oneCoboundaries (toRep φ) := by
  rw [sub_mem_comm_iff, groupCohomology.mem_oneCoboundaries_iff]
  apply Additive.ofMul.exists_congr
  intro n
  rw [funext_iff]
  apply forall_congr'
  intro g
  simp only [toGroupExtension_inl, SemidirectProduct.ext_iff, mul_left, mul_right, inv_left,
    inv_right, right_splitting, left_inl, right_inl, inv_one, map_one, map_inv, MulAut.one_apply,
    one_mul, mul_one, and_true]
  rw [eq_mul_inv_iff_mul_eq, mul_comm, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_comm,
    ← mul_inv_eq_iff_eq_mul, ← groupCohomology.oneCocycles.val_eq_coe, AddSubgroupClass.coe_sub,
    Pi.sub_apply]
  simp only [splittingToOneCocycle, toRep_ρ_apply_apply, toMul_ofMul, ← div_eq_mul_inv]
  rfl

/-- The bijection between the `N`-conjugacy classes of splittings and the first cohomology group -/
def conjClassesEquivH1 : (toGroupExtension φ).ConjClasses ≃ groupCohomology.H1 (toRep φ) :=
  Quotient.congr (splittingEquivOneCocycles φ) (by
    intro s₁ s₂
    rw [Submodule.quotientRel_def]
    exact isConj_iff_sub_mem_oneCoboundaries φ s₁ s₂
  )

end SemidirectProduct
