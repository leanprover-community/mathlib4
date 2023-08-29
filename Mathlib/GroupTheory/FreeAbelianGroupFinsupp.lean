/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Hom.Equiv.TypeTags
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.Finsupp.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.IsFreeGroup
import Mathlib.LinearAlgebra.Dimension

#align_import group_theory.free_abelian_group_finsupp from "leanprover-community/mathlib"@"47b51515e69f59bca5cf34ef456e6000fe205a69"

/-!
# Isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `Finsupp` to `FreeAbelianGroup`.

## Main declarations

- `FreeAbelianGroup.equivFinsupp`: group isomorphism between `FreeAbelianGroup X` and `X →₀ ℤ`
- `FreeAbelianGroup.coeff`: the multiplicity of `x : X` in `a : FreeAbelianGroup X`
- `FreeAbelianGroup.support`: the finset of `x : X` that occur in `a : FreeAbelianGroup X`

-/


noncomputable section

open BigOperators

variable {X : Type*}

/-- The group homomorphism `FreeAbelianGroup X →+ (X →₀ ℤ)`. -/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X →+ X →₀ ℤ :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : ℤ)
#align free_abelian_group.to_finsupp FreeAbelianGroup.toFinsupp

/-- The group homomorphism `(X →₀ ℤ) →+ FreeAbelianGroup X`. -/
def Finsupp.toFreeAbelianGroup : (X →₀ ℤ) →+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)
#align finsupp.to_free_abelian_group Finsupp.toFreeAbelianGroup

open Finsupp FreeAbelianGroup

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) := by
  ext
  -- ⊢ ↑(AddMonoidHom.comp toFreeAbelianGroup (singleAddHom x)) 1 = ↑(↑(AddMonoidHo …
  simp only [AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply, one_smul,
    toFreeAbelianGroup, Finsupp.liftAddHom_apply_single]
#align finsupp.to_free_abelian_group_comp_single_add_hom Finsupp.toFreeAbelianGroup_comp_singleAddHom

@[simp]
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup :
    toFinsupp.comp toFreeAbelianGroup = AddMonoidHom.id (X →₀ ℤ) := by
  ext x y; simp only [AddMonoidHom.id_comp]
  -- ⊢ ↑(↑(AddMonoidHom.comp (AddMonoidHom.comp toFinsupp toFreeAbelianGroup) (sing …
           -- ⊢ ↑(↑(AddMonoidHom.comp (AddMonoidHom.comp toFinsupp toFreeAbelianGroup) (sing …
  rw [AddMonoidHom.comp_assoc, Finsupp.toFreeAbelianGroup_comp_singleAddHom]
  -- ⊢ ↑(↑(AddMonoidHom.comp toFinsupp (↑(AddMonoidHom.flip (smulAddHom ℤ (FreeAbel …
  simp only [toFinsupp, AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply,
    one_smul, lift.of, AddMonoidHom.flip_apply, smulAddHom_apply, AddMonoidHom.id_apply]
#align free_abelian_group.to_finsupp_comp_to_free_abelian_group FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  -- ⊢ ↑(AddMonoidHom.comp toFreeAbelianGroup toFinsupp) (of x✝) = ↑(AddMonoidHom.i …
  rw [toFreeAbelianGroup, toFinsupp, AddMonoidHom.comp_apply, lift.of,
    liftAddHom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]
#align finsupp.to_free_abelian_group_comp_to_finsupp Finsupp.toFreeAbelianGroup_comp_toFinsupp

@[simp]
theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAbelianGroup_comp_toFinsupp, AddMonoidHom.id_apply]
  -- 🎉 no goals
#align finsupp.to_free_abelian_group_to_finsupp Finsupp.toFreeAbelianGroup_toFinsupp

namespace FreeAbelianGroup

open Finsupp

@[simp]
theorem toFinsupp_of (x : X) : toFinsupp (of x) = Finsupp.single x 1 := by
  simp only [toFinsupp, lift.of]
  -- 🎉 no goals
#align free_abelian_group.to_finsupp_of FreeAbelianGroup.toFinsupp_of

@[simp]
theorem toFinsupp_toFreeAbelianGroup (f : X →₀ ℤ) :
    FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) = f := by
  rw [← AddMonoidHom.comp_apply, toFinsupp_comp_toFreeAbelianGroup, AddMonoidHom.id_apply]
  -- 🎉 no goals
#align free_abelian_group.to_finsupp_to_free_abelian_group FreeAbelianGroup.toFinsupp_toFreeAbelianGroup

variable (X)

/-- The additive equivalence between `FreeAbelianGroup X` and `(X →₀ ℤ)`. -/
@[simps!]
def equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ) where
  toFun := toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add
#align free_abelian_group.equiv_finsupp FreeAbelianGroup.equivFinsupp

/-- `A` is a basis of the ℤ-module `FreeAbelianGroup A`. -/
noncomputable def basis (α : Type*) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩
#align free_abelian_group.basis FreeAbelianGroup.basis

/-- Isomorphic free abelian groups (as modules) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupLinearEquiv {α β : Type*}
    (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _
#align free_abelian_group.equiv.of_free_abelian_group_linear_equiv FreeAbelianGroup.Equiv.ofFreeAbelianGroupLinearEquiv

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupEquiv {α β : Type*} (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) :
    α ≃ β :=
  Equiv.ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv
#align free_abelian_group.equiv.of_free_abelian_group_equiv FreeAbelianGroup.Equiv.ofFreeAbelianGroupEquiv

/-- Isomorphic free groups have equivalent bases. -/
def Equiv.ofFreeGroupEquiv {α β : Type*} (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  Equiv.ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)
#align free_abelian_group.equiv.of_free_group_equiv FreeAbelianGroup.Equiv.ofFreeGroupEquiv

open IsFreeGroup

/-- Isomorphic free groups have equivalent bases (`IsFreeGroup` variant). -/
def Equiv.ofIsFreeGroupEquiv {G H : Type*} [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H]
    (e : G ≃* H) : Generators G ≃ Generators H :=
  Equiv.ofFreeGroupEquiv <| MulEquiv.trans (toFreeGroup G).symm <| MulEquiv.trans e <| toFreeGroup H
#align free_abelian_group.equiv.of_is_free_group_equiv FreeAbelianGroup.Equiv.ofIsFreeGroupEquiv

variable {X}

/-- `coeff x` is the additive group homomorphism `FreeAbelianGroup X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : FreeAbelianGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp toFinsupp
#align free_abelian_group.coeff FreeAbelianGroup.coeff

/-- `support a` for `a : FreeAbelianGroup X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.toFinsupp.support
#align free_abelian_group.support FreeAbelianGroup.support

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]
  -- ⊢ ↑(↑toFinsupp a) x ≠ 0 ↔ ↑(coeff x) a ≠ 0
  exact Iff.rfl
  -- 🎉 no goals
#align free_abelian_group.mem_support_iff FreeAbelianGroup.mem_support_iff

theorem not_mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support, Finsupp.not_mem_support_iff]
  -- ⊢ ↑(↑toFinsupp a) x = 0 ↔ ↑(coeff x) a = 0
  exact Iff.rfl
  -- 🎉 no goals
#align free_abelian_group.not_mem_support_iff FreeAbelianGroup.not_mem_support_iff

@[simp]
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, AddMonoidHom.map_zero]
  -- 🎉 no goals
#align free_abelian_group.support_zero FreeAbelianGroup.support_zero

@[simp]
theorem support_of (x : X) : support (of x) = {x} := by
  rw [support, toFinsupp_of, Finsupp.support_single_ne_zero _ one_ne_zero]
  -- 🎉 no goals
#align free_abelian_group.support_of FreeAbelianGroup.support_of

@[simp]
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, AddMonoidHom.map_neg, Finsupp.support_neg]
  -- 🎉 no goals
#align free_abelian_group.support_neg FreeAbelianGroup.support_neg

@[simp]
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  ext x
  -- ⊢ x ∈ support (k • a) ↔ x ∈ support a
  simp only [mem_support_iff, AddMonoidHom.map_zsmul]
  -- ⊢ k • ↑(coeff x) a ≠ 0 ↔ ↑(coeff x) a ≠ 0
  simp only [h, zsmul_int_int, false_or_iff, Ne.def, mul_eq_zero]
  -- 🎉 no goals
#align free_abelian_group.support_zsmul FreeAbelianGroup.support_zsmul

@[simp]
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  apply support_zsmul k _ a
  -- ⊢ ↑k ≠ 0
  exact_mod_cast h
  -- 🎉 no goals
#align free_abelian_group.support_nsmul FreeAbelianGroup.support_nsmul

open Classical

theorem support_add (a b : FreeAbelianGroup X) : support (a + b) ⊆ a.support ∪ b.support := by
  simp only [support, AddMonoidHom.map_add]
  -- ⊢ (↑toFinsupp a + ↑toFinsupp b).support ⊆ (↑toFinsupp a).support ∪ (↑toFinsupp …
  apply Finsupp.support_add
  -- 🎉 no goals
#align free_abelian_group.support_add FreeAbelianGroup.support_add

end FreeAbelianGroup
