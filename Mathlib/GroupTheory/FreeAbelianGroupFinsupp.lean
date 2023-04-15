/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module group_theory.free_abelian_group_finsupp
! leanprover-community/mathlib commit 47b51515e69f59bca5cf34ef456e6000fe205a69
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.TypeTags
import Mathbin.Algebra.Module.Equiv
import Mathbin.Data.Finsupp.Defs
import Mathbin.GroupTheory.FreeAbelianGroup
import Mathbin.GroupTheory.IsFreeGroup
import Mathbin.LinearAlgebra.Dimension

/-!
# Isomorphism between `free_abelian_group X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `free_abelian_group X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `finsupp` to `free_abelian_group`.

## Main declarations

- `free_abelian_group.equiv_finsupp`: group isomorphism between `free_abelian_group X` and `X →₀ ℤ`
- `free_abelian_group.coeff`: the multiplicity of `x : X` in `a : free_abelian_group X`
- `free_abelian_group.support`: the finset of `x : X` that occur in `a : free_abelian_group X`

-/


noncomputable section

open BigOperators

variable {X : Type _}

/-- The group homomorphism `free_abelian_group X →+ (X →₀ ℤ)`. -/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X →+ X →₀ ℤ :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : ℤ)
#align free_abelian_group.to_finsupp FreeAbelianGroup.toFinsupp

/-- The group homomorphism `(X →₀ ℤ) →+ free_abelian_group X`. -/
def Finsupp.toFreeAbelianGroup : (X →₀ ℤ) →+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)
#align finsupp.to_free_abelian_group Finsupp.toFreeAbelianGroup

open Finsupp FreeAbelianGroup

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) :=
  by
  ext
  simp only [AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply, one_smul,
    to_free_abelian_group, Finsupp.liftAddHom_apply_single]
#align finsupp.to_free_abelian_group_comp_single_add_hom Finsupp.toFreeAbelianGroup_comp_singleAddHom

@[simp]
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup :
    toFinsupp.comp toFreeAbelianGroup = AddMonoidHom.id (X →₀ ℤ) :=
  by
  ext (x y); simp only [AddMonoidHom.id_comp]
  rw [AddMonoidHom.comp_assoc, Finsupp.toFreeAbelianGroup_comp_singleAddHom]
  simp only [to_finsupp, AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply,
    one_smul, lift.of, AddMonoidHom.flip_apply, smulAddHom_apply, AddMonoidHom.id_apply]
#align free_abelian_group.to_finsupp_comp_to_free_abelian_group FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) :=
  by
  ext
  rw [to_free_abelian_group, to_finsupp, AddMonoidHom.comp_apply, lift.of,
    lift_add_hom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]
#align finsupp.to_free_abelian_group_comp_to_finsupp Finsupp.toFreeAbelianGroup_comp_toFinsupp

@[simp]
theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    x.toFinsupp.toFreeAbelianGroup = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAbelianGroup_comp_toFinsupp, AddMonoidHom.id_apply]
#align finsupp.to_free_abelian_group_to_finsupp Finsupp.toFreeAbelianGroup_toFinsupp

namespace FreeAbelianGroup

open Finsupp

variable {X}

@[simp]
theorem toFinsupp_of (x : X) : toFinsupp (of x) = Finsupp.single x 1 := by
  simp only [to_finsupp, lift.of]
#align free_abelian_group.to_finsupp_of FreeAbelianGroup.toFinsupp_of

@[simp]
theorem toFinsupp_toFreeAbelianGroup (f : X →₀ ℤ) : f.toFreeAbelianGroup.toFinsupp = f := by
  rw [← AddMonoidHom.comp_apply, to_finsupp_comp_to_free_abelian_group, AddMonoidHom.id_apply]
#align free_abelian_group.to_finsupp_to_free_abelian_group FreeAbelianGroup.toFinsupp_toFreeAbelianGroup

variable (X)

/-- The additive equivalence between `free_abelian_group X` and `(X →₀ ℤ)`. -/
@[simps]
def equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ)
    where
  toFun := toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add
#align free_abelian_group.equiv_finsupp FreeAbelianGroup.equivFinsupp

/-- `A` is a basis of the ℤ-module `free_abelian_group A`. -/
noncomputable def basis (α : Type _) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩
#align free_abelian_group.basis FreeAbelianGroup.basis

/-- Isomorphic free ablian groups (as modules) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupLinearEquiv {α β : Type _}
    (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _
#align free_abelian_group.equiv.of_free_abelian_group_linear_equiv FreeAbelianGroup.Equiv.ofFreeAbelianGroupLinearEquiv

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupEquiv {α β : Type _} (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) :
    α ≃ β :=
  Equiv.ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv
#align free_abelian_group.equiv.of_free_abelian_group_equiv FreeAbelianGroup.Equiv.ofFreeAbelianGroupEquiv

/-- Isomorphic free groups have equivalent bases. -/
def Equiv.ofFreeGroupEquiv {α β : Type _} (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  Equiv.ofFreeAbelianGroupEquiv e.abelianizationCongr.toAdditive
#align free_abelian_group.equiv.of_free_group_equiv FreeAbelianGroup.Equiv.ofFreeGroupEquiv

open IsFreeGroup

/-- Isomorphic free groups have equivalent bases (`is_free_group` variant`). -/
def Equiv.ofIsFreeGroupEquiv {G H : Type _} [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H]
    (e : G ≃* H) : Generators G ≃ Generators H :=
  Equiv.ofFreeGroupEquiv <| MulEquiv.trans (toFreeGroup G).symm <| MulEquiv.trans e <| toFreeGroup H
#align free_abelian_group.equiv.of_is_free_group_equiv FreeAbelianGroup.Equiv.ofIsFreeGroupEquiv

variable {X}

/-- `coeff x` is the additive group homomorphism `free_abelian_group X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : FreeAbelianGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp toFinsupp
#align free_abelian_group.coeff FreeAbelianGroup.coeff

/-- `support a` for `a : free_abelian_group X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.toFinsupp.support
#align free_abelian_group.support FreeAbelianGroup.support

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 :=
  by
  rw [support, Finsupp.mem_support_iff]
  exact Iff.rfl
#align free_abelian_group.mem_support_iff FreeAbelianGroup.mem_support_iff

theorem not_mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 :=
  by
  rw [support, Finsupp.not_mem_support_iff]
  exact Iff.rfl
#align free_abelian_group.not_mem_support_iff FreeAbelianGroup.not_mem_support_iff

@[simp]
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, AddMonoidHom.map_zero]
#align free_abelian_group.support_zero FreeAbelianGroup.support_zero

@[simp]
theorem support_of (x : X) : support (of x) = {x} := by
  simp only [support, to_finsupp_of, Finsupp.support_single_ne_zero _ one_ne_zero]
#align free_abelian_group.support_of FreeAbelianGroup.support_of

@[simp]
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, AddMonoidHom.map_neg, Finsupp.support_neg]
#align free_abelian_group.support_neg FreeAbelianGroup.support_neg

@[simp]
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) : support (k • a) = support a :=
  by
  ext x
  simp only [mem_support_iff, AddMonoidHom.map_zsmul]
  simp only [h, zsmul_int_int, false_or_iff, Ne.def, mul_eq_zero]
#align free_abelian_group.support_zsmul FreeAbelianGroup.support_zsmul

@[simp]
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) : support (k • a) = support a :=
  by
  apply support_zsmul k _ a
  exact_mod_cast h
#align free_abelian_group.support_nsmul FreeAbelianGroup.support_nsmul

open Classical

theorem support_add (a b : FreeAbelianGroup X) : support (a + b) ⊆ a.support ∪ b.support :=
  by
  simp only [support, AddMonoidHom.map_add]
  apply Finsupp.support_add
#align free_abelian_group.support_add FreeAbelianGroup.support_add

end FreeAbelianGroup

