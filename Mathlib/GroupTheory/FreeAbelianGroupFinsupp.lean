/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

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

variable {X : Type*}

/-- The group homomorphism `FreeAbelianGroup X →+ (X →₀ ℤ)`. -/
def FreeAbelianGroup.toFinsupp : FreeAbelianGroup X →+ X →₀ ℤ :=
  FreeAbelianGroup.lift fun x => Finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ FreeAbelianGroup X`. -/
def Finsupp.toFreeAbelianGroup : (X →₀ ℤ) →+ FreeAbelianGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAbelianGroup X)).flip (FreeAbelianGroup.of x)

open Finsupp FreeAbelianGroup

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) := by
  ext
  simp only [AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply, one_smul,
    toFreeAbelianGroup, Finsupp.liftAddHom_apply_single]

@[simp]
theorem FreeAbelianGroup.toFinsupp_comp_toFreeAbelianGroup :
    toFinsupp.comp toFreeAbelianGroup = AddMonoidHom.id (X →₀ ℤ) := by
  ext x y; simp only [AddMonoidHom.id_comp]
  rw [AddMonoidHom.comp_assoc, Finsupp.toFreeAbelianGroup_comp_singleAddHom]
  simp only [toFinsupp, AddMonoidHom.coe_comp, Finsupp.singleAddHom_apply, Function.comp_apply,
    one_smul, lift.of, AddMonoidHom.flip_apply, smulAddHom_apply, AddMonoidHom.id_apply]

@[simp]
theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  rw [toFreeAbelianGroup, toFinsupp, AddMonoidHom.comp_apply, lift.of,
    liftAddHom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]

@[simp]
theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAbelianGroup_comp_toFinsupp, AddMonoidHom.id_apply]

namespace FreeAbelianGroup

open Finsupp

@[simp]
theorem toFinsupp_of (x : X) : toFinsupp (of x) = Finsupp.single x 1 := by
  simp only [toFinsupp, lift.of]

@[simp]
theorem toFinsupp_toFreeAbelianGroup (f : X →₀ ℤ) :
    FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) = f := by
  rw [← AddMonoidHom.comp_apply, toFinsupp_comp_toFreeAbelianGroup, AddMonoidHom.id_apply]

variable (X)

/-- The additive equivalence between `FreeAbelianGroup X` and `(X →₀ ℤ)`. -/
@[simps!]
def equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ) where
  toFun := toFinsupp
  invFun := toFreeAbelianGroup
  left_inv := toFreeAbelianGroup_toFinsupp
  right_inv := toFinsupp_toFreeAbelianGroup
  map_add' := toFinsupp.map_add

/-- `A` is a basis of the ℤ-module `FreeAbelianGroup A`. -/
noncomputable def basis (α : Type*) : Basis α ℤ (FreeAbelianGroup α) :=
  ⟨(FreeAbelianGroup.equivFinsupp α).toIntLinearEquiv⟩

/-- Isomorphic free abelian groups (as modules) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupLinearEquiv {α β : Type*}
    (e : FreeAbelianGroup α ≃ₗ[ℤ] FreeAbelianGroup β) : α ≃ β :=
  let t : Basis α ℤ (FreeAbelianGroup β) := (FreeAbelianGroup.basis α).map e
  t.indexEquiv <| FreeAbelianGroup.basis _

/-- Isomorphic free abelian groups (as additive groups) have equivalent bases. -/
def Equiv.ofFreeAbelianGroupEquiv {α β : Type*} (e : FreeAbelianGroup α ≃+ FreeAbelianGroup β) :
    α ≃ β :=
  Equiv.ofFreeAbelianGroupLinearEquiv e.toIntLinearEquiv

/-- Isomorphic free groups have equivalent bases. -/
def Equiv.ofFreeGroupEquiv {α β : Type*} (e : FreeGroup α ≃* FreeGroup β) : α ≃ β :=
  Equiv.ofFreeAbelianGroupEquiv (MulEquiv.toAdditive e.abelianizationCongr)

open IsFreeGroup

/-- Isomorphic free groups have equivalent bases (`IsFreeGroup` variant). -/
def Equiv.ofIsFreeGroupEquiv {G H : Type*} [Group G] [Group H] [IsFreeGroup G] [IsFreeGroup H]
    (e : G ≃* H) : Generators G ≃ Generators H :=
  Equiv.ofFreeGroupEquiv <| MulEquiv.trans (toFreeGroup G).symm <| MulEquiv.trans e <| toFreeGroup H

variable {X}

/-- `coeff x` is the additive group homomorphism `FreeAbelianGroup X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : FreeAbelianGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp toFinsupp

/-- `support a` for `a : FreeAbelianGroup X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : FreeAbelianGroup X) : Finset X :=
  a.toFinsupp.support

theorem mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]
  exact Iff.rfl

theorem not_mem_support_iff (x : X) (a : FreeAbelianGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support, Finsupp.not_mem_support_iff]
  exact Iff.rfl

@[simp]
theorem support_zero : support (0 : FreeAbelianGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, AddMonoidHom.map_zero]

@[simp]
theorem support_of (x : X) : support (of x) = {x} := by
  rw [support, toFinsupp_of, Finsupp.support_single_ne_zero _ one_ne_zero]

@[simp]
theorem support_neg (a : FreeAbelianGroup X) : support (-a) = support a := by
  simp only [support, AddMonoidHom.map_neg, Finsupp.support_neg]

@[simp]
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  ext x
  simp only [mem_support_iff, AddMonoidHom.map_zsmul]
  simp only [h, zsmul_int_int, false_or, Ne, mul_eq_zero]

@[simp]
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    support (k • a) = support a := by
  apply support_zsmul k _ a
  exact mod_cast h

open scoped Classical

theorem support_add (a b : FreeAbelianGroup X) : support (a + b) ⊆ a.support ∪ b.support := by
  simp only [support, AddMonoidHom.map_add]
  apply Finsupp.support_add

end FreeAbelianGroup
