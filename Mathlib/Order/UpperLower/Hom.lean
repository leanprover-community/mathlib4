/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.upper_lower.hom
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.UpperLower.Basic
import Mathbin.Order.Hom.CompleteLattice

/-!
# `upper_set.Ici` etc as `sup`/`Sup`/`inf`/`Inf`-homomorphisms

In this file we define `upper_set.Ici_sup_hom` etc. These functions are `upper_set.Ici` and
`lower_set.Iic` bundled as `sup_hom`s, `inf_hom`s, `Sup_hom`s, or `Inf_hom`s.
-/


variable {α : Type _}

open OrderDual

namespace UpperSet

section SemilatticeSup

variable [SemilatticeSup α]

/-- `upper_set.Ici` as a `sup_hom`. -/
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

/- warning: upper_set.Ici_Sup_hom clashes with upper_set.Ici_sup_hom -> UpperSet.iciSupHom
warning: upper_set.Ici_Sup_hom -> UpperSet.iciSupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α], SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align upper_set.Ici_Sup_hom UpperSet.iciSupHomₓ'. -/
/-- `upper_set.Ici` as a `Sup_hom`. -/
def iciSupHom : SupₛHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_supₛ s).trans supₛ_image.symm⟩
#align upper_set.Ici_Sup_hom UpperSet.iciSupHom

/- warning: upper_set.coe_Ici_Sup_hom clashes with upper_set.coe_Ici_sup_hom -> UpperSet.coe_iciSupHom
warning: upper_set.coe_Ici_Sup_hom -> UpperSet.coe_iciSupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} ((fun (_x : SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (UpperSet.iciSupHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (fun (_x : SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (SupₛHom.hasCoeToFun.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (UpperSet.iciSupHom.{u1} α _inst_1)) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α], Eq.{succ u1} ((fun (_x : SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (UpperSet.iciSupHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (fun (_x : SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (SupHom.hasCoeToFun.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (UpperSet.iciSupHom.{u1} α _inst_1)) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align upper_set.coe_Ici_Sup_hom UpperSet.coe_iciSupHomₓ'. -/
@[simp]
theorem coe_iciSupHom : (iciSupHom : α → UpperSet α) = Ici :=
  rfl
#align upper_set.coe_Ici_Sup_hom UpperSet.coe_iciSupHom

/- warning: upper_set.Ici_Sup_hom_apply clashes with upper_set.Ici_sup_hom_apply -> UpperSet.iciSupHom_apply
warning: upper_set.Ici_Sup_hom_apply -> UpperSet.iciSupHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (coeFn.{succ u1, succ u1} (SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (fun (_x : SupₛHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (SupₛHom.hasCoeToFun.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (UpperSet.iciSupHom.{u1} α _inst_1) a) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} α] (a : α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (coeFn.{succ u1, succ u1} (SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (fun (_x : SupHom.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) => α -> (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (SupHom.hasCoeToFun.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) (SemilatticeSup.toHasSup.{u1} α _inst_1) (UpperSet.hasSup.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))) (UpperSet.iciSupHom.{u1} α _inst_1) a) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align upper_set.Ici_Sup_hom_apply UpperSet.iciSupHom_applyₓ'. -/
@[simp]
theorem iciSupHom_apply (a : α) : iciSupHom a = Ici a :=
  rfl
#align upper_set.Ici_Sup_hom_apply UpperSet.iciSupHom_apply

end UpperSet

namespace LowerSet

section SemilatticeInf

variable [SemilatticeInf α]

/-- `lower_set.Iic` as an `inf_hom`. -/
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

/- warning: lower_set.Iic_Inf_hom clashes with lower_set.Iic_inf_hom -> LowerSet.iicInfHom
warning: lower_set.Iic_Inf_hom -> LowerSet.iicInfHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α], InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align lower_set.Iic_Inf_hom LowerSet.iicInfHomₓ'. -/
/-- `lower_set.Iic` as an `Inf_hom`. -/
def iicInfHom : InfₛHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_infₛ s).trans infₛ_image.symm⟩
#align lower_set.Iic_Inf_hom LowerSet.iicInfHom

/- warning: lower_set.coe_Iic_Inf_hom clashes with lower_set.coe_Iic_inf_hom -> LowerSet.coe_iicInfHom
warning: lower_set.coe_Iic_Inf_hom -> LowerSet.coe_iicInfHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} ((fun (_x : InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (LowerSet.iicInfHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (fun (_x : InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (InfₛHom.hasCoeToFun.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (LowerSet.iicInfHom.{u1} α _inst_1)) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α], Eq.{succ u1} ((fun (_x : InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (LowerSet.iicInfHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (fun (_x : InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (InfHom.hasCoeToFun.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (LowerSet.iicInfHom.{u1} α _inst_1)) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align lower_set.coe_Iic_Inf_hom LowerSet.coe_iicInfHomₓ'. -/
@[simp]
theorem coe_iicInfHom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl
#align lower_set.coe_Iic_Inf_hom LowerSet.coe_iicInfHom

/- warning: lower_set.Iic_Inf_hom_apply clashes with lower_set.Iic_inf_hom_apply -> LowerSet.iicInfHom_apply
warning: lower_set.Iic_Inf_hom_apply -> LowerSet.iicInfHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (coeFn.{succ u1, succ u1} (InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (fun (_x : InfₛHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (InfₛHom.hasCoeToFun.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (LowerSet.iicInfHom.{u1} α _inst_1) a) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} α] (a : α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (coeFn.{succ u1, succ u1} (InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (fun (_x : InfHom.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) => α -> (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (InfHom.hasCoeToFun.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) (SemilatticeInf.toHasInf.{u1} α _inst_1) (LowerSet.hasInf.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))) (LowerSet.iicInfHom.{u1} α _inst_1) a) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align lower_set.Iic_Inf_hom_apply LowerSet.iicInfHom_applyₓ'. -/
@[simp]
theorem iicInfHom_apply (a : α) : iicInfHom a = Iic a :=
  rfl
#align lower_set.Iic_Inf_hom_apply LowerSet.iicInfHom_apply

end LowerSet

