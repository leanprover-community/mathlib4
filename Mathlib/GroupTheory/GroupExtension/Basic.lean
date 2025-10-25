/-
Copyright (c) 2024 Yudai Yamazaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yudai Yamazaki
-/

import Mathlib.GroupTheory.GroupExtension.Defs
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Basic lemmas about group extensions

This file gives basic lemmas about group extensions.

For the main definitions, see `Mathlib/GroupTheory/GroupExtension/Defs.lean`.
-/

variable {N G : Type*} [Group N] [Group G]

namespace GroupExtension

variable {E : Type*} [Group E] (S : GroupExtension N E G)

/-- The isomorphism `E ⧸ S.rightHom.ker ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.rightHom.ker ≃+ G` induced by `S.rightHom` -/]
noncomputable def quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

/-- The isomorphism `E ⧸ S.inl.range ≃* G` induced by `S.rightHom` -/
@[to_additive /-- The isomorphism `E ⧸ S.inl.range ≃+ G` induced by `S.rightHom` -/]
noncomputable def quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq S.range_inl_eq_ker_rightHom).trans
    S.quotientKerRightHomEquivRight

/-- An arbitrarily chosen section -/
@[to_additive surjInvRightHom /-- An arbitrarily chosen section -/]
noncomputable def surjInvRightHom : S.Section where
  toFun := Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

namespace Section

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (σ σ' : S.Section) (g g₁ g₂ : G)
  (equiv : S.Equiv S')

@[to_additive]
theorem mul_inv_mem_range_inl : σ g * (σ' g)⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
theorem inv_mul_mem_range_inl : (σ g)⁻¹ * σ' g ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]
theorem exists_eq_inl_mul : ∃ n : N, σ g = S.inl n * σ' g := by
  obtain ⟨n, hn⟩ := mul_inv_mem_range_inl σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]
theorem exists_eq_mul_inl : ∃ n : N, σ g = σ' g * S.inl n := by
  obtain ⟨n, hn⟩ := inv_mul_mem_range_inl σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]
theorem mul_mul_mul_inv_mem_range_inl : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
theorem mul_inv_mul_mul_mem_range_inl : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]
theorem exists_mul_eq_inl_mul_mul : ∃ n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂ := by
  obtain ⟨n, hn⟩ := mul_mul_mul_inv_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [mul_assoc, map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq, hn]

@[to_additive]
theorem exists_mul_eq_mul_mul_inl : ∃ n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n := by
  obtain ⟨n, hn⟩ := mul_inv_mul_mul_mem_range_inl σ g₁ g₂
  use n⁻¹
  rw [map_inv, eq_mul_inv_iff_mul_eq, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, hn]

initialize_simps_projections AddGroupExtension.Section (toFun → apply)
initialize_simps_projections Section (toFun → apply)

/-- The composition of an isomorphism between equivalent group extensions and a section -/
@[to_additive (attr := simps!)
/-- The composition of an isomorphism between equivalent additive group extensions and a section -/]
def equivComp : S'.Section where
  toFun := equiv ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply, equiv.rightHom_map, rightHom_section]

end Section

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G}

/-- An equivalence of group extensions from a homomorphism making a commuting diagram. Such a
homomorphism is necessarily an isomorphism. -/
@[to_additive
/-- An equivalence of additive group extensions from a homomorphism making a commuting diagram.
Such a homomorphism is necessarily an isomorphism. -/]
noncomputable def ofMonoidHom (f : E →* E') (comp_inl : f.comp S.inl = S'.inl)
    (rightHom_comp : S'.rightHom.comp f = S.rightHom) : S.Equiv S' where
  __ := f
  invFun e' :=
    let e := Function.surjInv S.rightHom_surjective (S'.rightHom e')
    e * S.inl (Function.invFun S'.inl ((f e)⁻¹ * e'))
  left_inv e := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, ← map_inv, ← map_mul]
    obtain ⟨n, hn⟩ :
        (Function.surjInv S.rightHom_surjective (S'.rightHom (f e)))⁻¹ * e ∈ S.inl.range := by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply,
        rightHom_comp]
      simpa only [Function.surjInv_eq] using inv_mul_cancel (S.rightHom e)
    rw [← eq_inv_mul_iff_mul_eq, ← hn, ← MonoidHom.comp_apply, comp_inl,
      Function.leftInverse_invFun S'.inl_injective]
  right_inv e' := by
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, map_mul]
    rw [← eq_inv_mul_iff_mul_eq, ← MonoidHom.comp_apply, comp_inl]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, S'.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      ← MonoidHom.comp_apply, rightHom_comp]
    simpa only [Function.surjInv_eq] using inv_mul_cancel (S'.rightHom e')
  inl_comm := congrArg DFunLike.coe comp_inl
  rightHom_comm := congrArg DFunLike.coe rightHom_comp

end Equiv

namespace Splitting

variable {S}
variable (s : S.Splitting)

/-- `G` acts on `N` by conjugation. -/
noncomputable def conjAct : G →* MulAut N := S.conjAct.comp s

/-- A split group extension is equivalent to the extension associated to a semidirect product. -/
noncomputable def semidirectProductToGroupExtensionEquiv :
    (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toFun := fun ⟨n, g⟩ ↦ S.inl n * s g
  invFun := fun e ↦ ⟨Function.invFun S.inl (e * (s (S.rightHom e))⁻¹), S.rightHom e⟩
  left_inv := fun ⟨n, g⟩ ↦ by
    simp only [map_mul, rightHom_inl, rightHom_splitting, one_mul, mul_inv_cancel_right,
      Function.leftInverse_invFun S.inl_injective n]
  right_inv := fun e ↦ by
    simp only [← eq_mul_inv_iff_mul_eq]
    apply Function.invFun_eq
    rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv,
      rightHom_splitting, mul_inv_cancel]
  map_mul' := fun ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ↦ by
    simp only [conjAct, MonoidHom.comp_apply, map_mul, inl_conjAct_comm, MonoidHom.coe_coe]
    group
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, Function.comp_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, map_mul, rightHom_inl, one_mul, rightHom_splitting,
      SemidirectProduct.rightHom_eq_right]

/-- The group associated to a split extension is isomorphic to a semidirect product. -/
noncomputable def semidirectProductMulEquiv : N ⋊[s.conjAct] G ≃* E :=
  s.semidirectProductToGroupExtensionEquiv.toMulEquiv

end Splitting

namespace IsConj

/-- `N`-conjugacy is reflexive. -/
@[to_additive /-- `N`-conjugacy is reflexive. -/]
theorem refl (s : S.Splitting) : S.IsConj s s :=
  ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

/-- `N`-conjugacy is symmetric. -/
@[to_additive /-- `N`-conjugacy is symmetric. -/]
theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

/-- `N`-conjugacy is transitive. -/
@[to_additive /-- `N`-conjugacy is transitive. -/]
theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
    S.IsConj s₁ s₃ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

/-- The setoid of splittings with `N`-conjugacy -/
@[to_additive /-- The setoid of splittings with `N`-conjugacy -/]
def setoid : Setoid S.Splitting where
  r := S.IsConj
  iseqv :=
  { refl := refl S
    symm := symm S
    trans := trans S }

end IsConj

/-- The `N`-conjugacy classes of splittings -/
@[to_additive /-- The `N`-conjugacy classes of splittings -/]
def ConjClasses := Quotient <| IsConj.setoid S

end GroupExtension

namespace SemidirectProduct

variable {φ : G →* MulAut N} (s : (toGroupExtension φ).Splitting)

theorem right_splitting (g : G) : (s g).right = g := by
  rw [← rightHom_eq_right, ← toGroupExtension_rightHom, s.rightHom_splitting]

end SemidirectProduct
