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
@[to_additive "The isomorphism `E ⧸ S.rightHom.ker ≃+ G` induced by `S.rightHom`" ]
noncomputable def quotientKerRightHomEquivRight : E ⧸ S.rightHom.ker ≃* G :=
  QuotientGroup.quotientKerEquivOfSurjective S.rightHom S.rightHom_surjective

/-- The isomorphism `E ⧸ S.inl.range ≃* G` induced by `S.rightHom` -/
@[to_additive "The isomorphism `E ⧸ S.inl.range ≃+ G` induced by `S.rightHom`" ]
noncomputable def quotientRangeInlEquivRight : E ⧸ S.inl.range ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq S.range_inl_eq_ker_rightHom).trans
    S.quotientKerRightHomEquivRight

/-- The inverse of the surjective `S.rightHom` -/
@[to_additive surjInvRightHom "The inverse of the surjective `S.rightHom`." ]
noncomputable def surjInvRightHom : S.Section where
  toFun := Function.surjInv S.rightHom_surjective
  rightInverse_rightHom := Function.surjInv_eq S.rightHom_surjective

namespace Section

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (σ σ' : S.Section) (g g₁ g₂ : G)
  (equiv : S.Equiv S')

@[to_additive]
theorem section_mul_inv_mem_range : σ g * (σ' g)⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
theorem section_inv_mul_mem_range : (σ g)⁻¹ * σ' g ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    inv_mul_cancel]

@[to_additive]
theorem exists_inl_mul_section : ∃ n : N, σ g = S.inl n * σ' g := by
  obtain ⟨n, hn⟩ := section_mul_inv_mem_range σ σ' g
  exact ⟨n, by rw [hn, inv_mul_cancel_right]⟩

@[to_additive]
theorem exists_section_mul_inl : ∃ n : N, σ g = σ' g * S.inl n := by
  obtain ⟨n, hn⟩ := section_inv_mul_mem_range σ' σ g
  exact ⟨n, by rw [hn, mul_inv_cancel_left]⟩

@[to_additive]
theorem section_mul_mul_mul_inv_mem_range : σ g₁ * σ g₂ * (σ (g₁ * g₂))⁻¹ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_inv_cancel]

@[to_additive]
theorem section_mul_inv_mul_mul_mem_range : (σ (g₁ * g₂))⁻¹ * σ g₁ * σ g₂ ∈ S.inl.range := by
  simp only [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, rightHom_section,
    mul_assoc, inv_mul_cancel]

@[to_additive]
theorem exists_section_mul_eq_inl_mul : ∃ n : N, σ (g₁ * g₂) = S.inl n * σ g₁ * σ g₂ := by
  obtain ⟨n, hn⟩ := section_mul_mul_mul_inv_mem_range σ g₁ g₂
  use n⁻¹
  rw [mul_assoc, map_inv, eq_inv_mul_iff_mul_eq, ← eq_mul_inv_iff_mul_eq, hn]

@[to_additive]
theorem exists_section_mul_eq_mul_inl : ∃ n : N, σ (g₁ * g₂) = σ g₁ * σ g₂ * S.inl n := by
  obtain ⟨n, hn⟩ := section_mul_inv_mul_mul_mem_range σ g₁ g₂
  use n⁻¹
  rw [map_inv, eq_mul_inv_iff_mul_eq, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, hn]

/-- The composition of a homomorphism between equivalent group extensions and a section -/
@[to_additive
      "The composition of a homomorphism between equivalent additive group extensions and a
      section"]
def ofEquiv : S'.Section where
  toFun := equiv.toMonoidHom ∘ σ
  rightInverse_rightHom g := by
    rw [Function.comp_apply, ← MonoidHom.comp_apply, equiv.rightHom_comm, rightHom_section]

@[to_additive]
theorem ofEquiv_def (g : G) : σ.ofEquiv equiv g = equiv.toMonoidHom (σ g) := rfl

end Section

namespace Equiv

variable {S}
variable {E' : Type*} [Group E'] {S' : GroupExtension N E' G} (equiv : S.Equiv S')

/-- The four lemma (deriving injectivity) specialized for group extensions -/
@[to_additive "The four lemma (deriving injectivity) specialized for additive group extensions"]
theorem injective : Function.Injective equiv.toMonoidHom := by
  rw [injective_iff_map_eq_one]
  intro e he
  obtain ⟨n, rfl⟩ : e ∈ S.inl.range := by
    simpa only [map_one, ← MonoidHom.comp_apply, equiv.rightHom_comm, S.range_inl_eq_ker_rightHom]
      using congrArg S'.rightHom he
  rw [← MonoidHom.comp_apply, equiv.inl_comm,
    (injective_iff_map_eq_one' S'.inl).mp S'.inl_injective] at he
  rw [he, S.inl.map_one]

/-- The four lemma (deriving surjectivity) specialized for group extensions -/
@[to_additive "The four lemma (deriving surjectivity) specialized for additive group extensions"]
theorem surjective : Function.Surjective equiv.toMonoidHom := by
  intro e'
  obtain ⟨e, he⟩ := S.rightHom_surjective (S'.rightHom e')
  rw [eq_comm, ← equiv.rightHom_comm, MonoidHom.comp_apply, MonoidHom.eq_iff,
    ← S'.range_inl_eq_ker_rightHom] at he
  obtain ⟨n, hn⟩ := he
  use e * S.inl n
  rw [MonoidHom.map_mul, ← MonoidHom.comp_apply, equiv.inl_comm, hn, mul_inv_cancel_left]

/-- The five lemma specialized for group extensions -/
@[to_additive "The five lemma specialized for additive group extensions"]
theorem bijective : Function.Bijective equiv.toMonoidHom := ⟨equiv.injective, equiv.surjective⟩

/-- The homomorphism associated to an equivalence of group extensions is an isomorphism. -/
@[to_additive
      "The homomorphism associated to an equivalence of additive group extensions is an
      isomorphism."]
noncomputable def toMulEquiv : E ≃* E' := MulEquiv.ofBijective equiv.toMonoidHom equiv.bijective

@[to_additive]
theorem toMulEquiv_eq_toMonoidHom : equiv.toMulEquiv = equiv.toMonoidHom := rfl

/-- A group extension is equivalent to itself. -/
@[to_additive "An additive group extension is equivalent to itself."]
def refl (S : GroupExtension N E G) : S.Equiv S where
  toMonoidHom := MonoidHom.id E
  inl_comm := MonoidHom.id_comp _
  rightHom_comm := MonoidHom.comp_id _

/-- The inverse of an equivalence of group extensions is an equivalence. -/
@[to_additive "The inverse of an equivalence of additive group extensions is an equivalence."]
noncomputable def symm : S'.Equiv S where
  toMonoidHom := equiv.toMulEquiv.symm
  inl_comm := by
    rw [← equiv.inl_comm, ← MonoidHom.comp_assoc, ← toMulEquiv_eq_toMonoidHom,
      MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom, MonoidHom.id_comp]
  rightHom_comm := by
    rw [← equiv.rightHom_comm, MonoidHom.comp_assoc, ← toMulEquiv_eq_toMonoidHom,
      MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm, MonoidHom.comp_id]

/-- The composition of monoid homomorphisms associated to equivalences of group extensions gives
    another equivalence. -/
@[to_additive
      "The composition of monoid homomorphisms associated to equivalences of additive group
      extensions gives another equivalence."]
def trans {E'' : Type*} [Group E''] {S'' : GroupExtension N E'' G} (equiv' : S'.Equiv S'') :
    S.Equiv S'' where
  toMonoidHom := equiv'.toMonoidHom.comp equiv.toMonoidHom
  inl_comm := by rw [MonoidHom.comp_assoc, equiv.inl_comm, equiv'.inl_comm]
  rightHom_comm := by rw [← MonoidHom.comp_assoc, equiv'.rightHom_comm, equiv.rightHom_comm]

end Equiv

namespace Splitting

variable {S}
variable (s : S.Splitting)

/-- `G` acts on `N` by conjugation. -/
noncomputable def conjAct : G →* MulAut N := S.conjAct.comp s

/-- A group homomorphism from the corresponding semidirect product -/
def semidirectProductMonoidHom : N ⋊[s.conjAct] G →* E where
  toFun := fun ⟨n, g⟩ ↦ S.inl n * s g
  map_one' := by simp only [map_one, mul_one]
  map_mul' := fun ⟨n₁, g₁⟩ ⟨n₂, g₂⟩ ↦ by
    simp only [conjAct, MonoidHom.comp_apply, map_mul, inl_conjAct_comm, MonoidHom.coe_coe]
    group

/-- A split group extension is equivalent to the extension associated to a semidirect product. -/
def semidirectProductToGroupExtensionEquiv :
    (SemidirectProduct.toGroupExtension s.conjAct).Equiv S where
  toMonoidHom := semidirectProductMonoidHom s
  inl_comm := by
    ext n
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply,
      semidirectProductMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, mul_one]
  rightHom_comm := by
    ext ⟨n, g⟩
    simp only [SemidirectProduct.toGroupExtension, MonoidHom.comp_apply,
      SemidirectProduct.rightHom_eq_right, semidirectProductMonoidHom, MonoidHom.coe_mk,
      OneHom.coe_mk, map_mul, rightHom_inl, rightHom_splitting, one_mul]

/-- The group associated to a split extension is isomorphic to a semidirect product. -/
noncomputable def semidirectProductMulEquiv : N ⋊[s.conjAct] G ≃* E :=
  s.semidirectProductToGroupExtensionEquiv.toMulEquiv

end Splitting

namespace IsConj

/-- `N`-conjugacy is reflexive. -/
@[to_additive "`N`-conjugacy is reflexive."]
theorem refl (s : S.Splitting) : S.IsConj s s :=
  ⟨1, by simp only [map_one, inv_one, one_mul, mul_one]⟩

/-- `N`-conjugacy is symmetric. -/
@[to_additive "`N`-conjugacy is symmetric."]
theorem symm {s₁ s₂ : S.Splitting} (h : S.IsConj s₁ s₂) : S.IsConj s₂ s₁ := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n⁻¹, by simp only [hn, map_inv]; group⟩

/-- `N`-conjugacy is transitive. -/
@[to_additive "`N`-conjugacy is transitive."]
theorem trans {s₁ s₂ s₃ : S.Splitting} (h₁ : S.IsConj s₁ s₂) (h₂ : S.IsConj s₂ s₃) :
    S.IsConj s₁ s₃ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ * n₂, by simp only [hn₁, hn₂, map_mul]; group⟩

/-- The setoid of splittings with `N`-conjugacy -/
@[to_additive "The setoid of splittings with `N`-conjugacy"]
def setoid : Setoid S.Splitting where
  r := S.IsConj
  iseqv := {
    refl := refl S
    symm := symm S
    trans := trans S
  }

end IsConj

/-- The `N`-conjugacy classes of splittings -/
@[to_additive "The `N`-conjugacy classes of splittings"]
def ConjClasses := Quotient <| IsConj.setoid S

end GroupExtension

namespace SemidirectProduct

variable {φ : G →* MulAut N} (s : (toGroupExtension φ).Splitting)

theorem right_splitting (g : G) : (s g).right = g := by
  rw [← rightHom_eq_right, ← toGroupExtension_rightHom, s.rightHom_splitting]

end SemidirectProduct
