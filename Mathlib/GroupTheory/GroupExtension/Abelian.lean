/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/

import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option linter.style.header false in
set_option linter.directoryDependency false in

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

end SemidirectProduct

namespace GroupExtension

section SemidirectProduct

variable {N G : Type} [CommGroup N] [Group G] {φ : G →* MulAut N}

namespace Splitting

/-- The 1-cocycle corresponding to a splitting. -/
@[simps!]
def toOneCocycle (s : (SemidirectProduct.toGroupExtension φ).Splitting) :
    groupCohomology.cocycles₁ (SemidirectProduct.toRep φ) :=
  @groupCohomology.cocyclesOfIsMulCocycle₁ G N _ _ (MulDistribMulAction.compHom N φ)
    (fun g ↦ (s g).left)
    fun g₁ g₂ ↦ by
      simp only [map_mul, SemidirectProduct.mul_left, SemidirectProduct.right_splitting]
      rw [mul_comm, MulAction.compHom_smul_def, MulAut.smul_def]

theorem toOneCocycle_apply (s : (SemidirectProduct.toGroupExtension φ).Splitting) (g : G) :
    s.toOneCocycle g = Additive.ofMul (s g).left := toOneCocycle_coe s g

/-- The splitting corresponding to a 1-cocycle. -/
@[simps!]
noncomputable def ofOneCocycle (f : groupCohomology.cocycles₁ (SemidirectProduct.toRep φ)) :
    (SemidirectProduct.toGroupExtension φ).Splitting where
  toFun g := ⟨Additive.toMul (f g), g⟩
  map_one' := by
    ext
    · simp only [SemidirectProduct.one_left, groupCohomology.cocycles₁_map_one, toMul_zero]
    · simp only [SemidirectProduct.one_right]
  map_mul' g₁ g₂ := by
    ext
    · simp only [SemidirectProduct.mul_left]
      rw [(groupCohomology.mem_cocycles₁_iff f).mp f.property g₁ g₂, toMul_add, mul_comm,
        SemidirectProduct.toRep_ρ_apply_apply, toMul_ofMul]
    · simp only [SemidirectProduct.mul_right]
  rightInverse_rightHom g :=  by
    simp only [SemidirectProduct.toGroupExtension_rightHom, SemidirectProduct.rightHom_eq_right]

/-- The bijection between the splittings of the group extension associated to a semidirect product
  and the 1-cocycles -/
@[simps!]
noncomputable def equivOneCocycles : (SemidirectProduct.toGroupExtension φ).Splitting ≃
    groupCohomology.cocycles₁ (SemidirectProduct.toRep φ) where
  toFun := toOneCocycle
  invFun := ofOneCocycle
  left_inv s := by
    ext g
    · rw [ofOneCocycle_apply_left, toOneCocycle_apply, toMul_ofMul]
    · rw [ofOneCocycle_apply_right, ← SemidirectProduct.rightHom_eq_right,
      ← SemidirectProduct.toGroupExtension_rightHom, rightHom_splitting]
  right_inv f := by
    ext g
    simp only [toOneCocycle_apply, ofOneCocycle_apply_left, ofMul_toMul]

end Splitting

/-- The bijection between the `N`-conjugacy classes of splittings and the first cohomology group -/
noncomputable def conjClassesEquivH1 : (SemidirectProduct.toGroupExtension φ).ConjClasses ≃
    (groupCohomology.shortComplexH1 (SemidirectProduct.toRep φ)).moduleCatLeftHomologyData.H :=
  Quotient.congr Splitting.equivOneCocycles (by
    intro s₁ s₂
    rw [Submodule.quotientRel_def, sub_mem_comm_iff]
    simp only [groupCohomology.shortComplexH1, groupCohomology.d₀₁, groupCohomology.d₁₂,
      ModuleCat.hom_ofHom, CategoryTheory.ShortComplex.moduleCatToCycles,
      LinearMap.range_codRestrict, Submodule.mem_comap, Submodule.subtype_apply,
      groupCohomology.cocycles₁.val_eq_coe, LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk,
      SemidirectProduct.toRep_ρ_apply_apply]
    change (SemidirectProduct.toGroupExtension φ).IsConj s₁ s₂ ↔
      ∃ y, (fun g ↦ Additive.ofMul ((φ g) (Additive.toMul y)) - y) =
        Splitting.equivOneCocycles s₂ - Splitting.equivOneCocycles s₁
    apply Additive.ofMul.exists_congr
    intro n
    simp only [funext_iff]
    apply forall_congr'
    intro g
    simp only [SemidirectProduct.toGroupExtension_inl, SemidirectProduct.ext_iff,
      SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
      MulAut.one_apply, SemidirectProduct.mul_right, one_mul, SemidirectProduct.inv_left, inv_one,
      map_inv, SemidirectProduct.inv_right, mul_one, toMul_ofMul,
      ← groupCohomology.cocycles₁.val_eq_coe, AddSubgroupClass.coe_sub, Pi.sub_apply,
      Splitting.equivOneCocycles_apply_coe, SemidirectProduct.right_splitting, and_true]
    rw [eq_mul_inv_iff_mul_eq, eq_sub_iff_add_eq', ← add_sub_assoc, sub_eq_iff_eq_add',
      ← Additive.ofMul.apply_eq_iff_eq]
    simp only [ofMul_mul]
    rfl
  )

end SemidirectProduct

end GroupExtension
