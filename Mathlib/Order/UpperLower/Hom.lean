/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.upper_lower.hom
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Hom.CompleteLattice

/-!
# `upper_set.Ici` etc as `sup`/`Sup`/`inf`/`Inf`-homomorphisms

In this file we define `upper_set.iciSupHom` etc. These functions are `UpperSet.Ici` and
`LowerSet.Iic` bundled as `SupHom`s, `InfHom`s, `SupₛHom`s, or `InfₛHom`s.
-/


variable {α : Type _}

open OrderDual

namespace UpperSet

section SemilatticeSup

variable [SemilatticeSup α]

/-- `UpperSet.Ici` as a `SupHom`. -/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨Ici, Ici_sup⟩
#align upper_set.Ici_sup_hom UpperSet.iciSupHom

@[simp]
theorem coe_iciSupHom : (iciSupHom : α → UpperSet α) = Ici :=
  rfl
#align upper_set.coe_Ici_sup_hom UpperSet.coe_iciSupHom

@[simp]
theorem iciSupHom_apply (a : α) : iciSupHom a = Ici a :=
  rfl
#align upper_set.Ici_sup_hom_apply UpperSet.iciSupHom_apply

end SemilatticeSup

variable [CompleteLattice α]

/-- `UpperSet.Ici` as a `SupₛHom`. -/
def iciSupHomₓ : SupₛHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_supₛ s).trans supₛ_image.symm⟩
#align upper_set.Ici_Sup_hom UpperSet.iciSupHomₓ

@[simp]
theorem coe_iciSupHomₓ : (iciSupHom : α → UpperSet α) = Ici :=
  rfl
#align upper_set.coe_Ici_Sup_hom UpperSet.coe_iciSupHomₓ

@[simp]
theorem iciSupHom_applyₓ (a : α) : iciSupHom a = Ici a :=
  rfl
#align upper_set.Ici_Sup_hom_apply UpperSet.iciSupHom_applyₓ

end UpperSet

namespace LowerSet

section SemilatticeInf

variable [SemilatticeInf α]

/-- `LowerSet.Iic` as an `InfHom`. -/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨Iic, Iic_inf⟩
#align lower_set.Iic_inf_hom LowerSet.iicInfHom

@[simp]
theorem coe_iicInfHom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
#align lower_set.coe_Iic_inf_hom LowerSet.coe_iicInfHom

@[simp]
theorem iicInfHom_apply (a : α) : iicInfHom a = Iic a :=
  rfl
#align lower_set.Iic_inf_hom_apply LowerSet.iicInfHom_apply

end SemilatticeInf

variable [CompleteLattice α]

/-- `LowerSet.Iic` as an `InfₛHom`. -/
def iicInfHomₓ : InfₛHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_infₛ s).trans infₛ_image.symm⟩
#align lower_set.Iic_Inf_hom LowerSet.iicInfHomₓ

@[simp]
theorem coe_iicInfHomₓ : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
#align lower_set.coe_Iic_Inf_hom LowerSet.coe_iicInfHomₓ

@[simp]
theorem iicInfHom_applyₓ (a : α) : iicInfHom a = Iic a :=
  rfl
#align lower_set.Iic_Inf_hom_apply LowerSet.iicInfHom_applyₓ

end LowerSet
