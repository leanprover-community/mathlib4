/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Hom.CompleteLattice

#align_import order.upper_lower.hom from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# `UpperSet.Ici` etc as `Sup`/`sSup`/`Inf`/`sInf`-homomorphisms

In this file we define `UpperSet.iciSupHom` etc. These functions are `UpperSet.Ici` and
`LowerSet.Iic` bundled as `SupHom`s, `InfHom`s, `sSupHom`s, or `sInfHom`s.
-/


variable {α : Type*}

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

/-- `UpperSet.Ici` as a `sSupHom`. -/
def icisSupHom : sSupHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩
-- Porting note: `ₓ` because typeclass assumption changed
#align upper_set.Ici_Sup_hom UpperSet.icisSupHomₓ

@[simp]
theorem coe_icisSupHom : (icisSupHom : α → UpperSet α) = Ici :=
  rfl
-- Porting note: `ₓ` because typeclass assumption changed
#align upper_set.coe_Ici_Sup_hom UpperSet.coe_icisSupHomₓ

@[simp]
theorem icisSupHom_apply (a : α) : icisSupHom a = Ici a :=
  rfl
-- Porting note: `ₓ` because typeclass assumption changed
#align upper_set.Ici_Sup_hom_apply UpperSet.icisSupHom_applyₓ

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

/-- `LowerSet.Iic` as an `sInfHom`. -/
def iicsInfHom : sInfHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩
-- Porting note: `ₓ` because typeclass assumption changed
#align lower_set.Iic_Inf_hom LowerSet.iicsInfHomₓ

@[simp]
theorem coe_iicsInfHom : (iicsInfHom : α → LowerSet α) = Iic :=
  rfl
-- Porting note: `ₓ` because typeclass assumption changed
#align lower_set.coe_Iic_Inf_hom LowerSet.coe_iicsInfHomₓ

@[simp]
theorem iicsInfHom_apply (a : α) : iicsInfHom a = Iic a :=
  rfl
-- Porting note: `ₓ` because typeclass assumption changed
#align lower_set.Iic_Inf_hom_apply LowerSet.iicsInfHom_applyₓ

end LowerSet
