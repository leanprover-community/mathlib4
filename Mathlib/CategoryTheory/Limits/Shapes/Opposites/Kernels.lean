/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels and cokernels in `C` and `Cᵒᵖ`

We construct kernels and cokernels in the opposite categories.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {J : Type u₂} [Category.{v₂} J]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- A colimit cokernel cofork gives a limit kernel fork in the opposite category -/
def CokernelCofork.IsColimit.ofπOp {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.op (show p.op ≫ f.op = 0 by rw [← op_comp, w, op_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.unop_op, Cofork.IsColimit.π_desc] using Quiver.Hom.op_inj hb)))

/-- A colimit cokernel cofork in the opposite category gives a limit kernel fork
in the original category -/
def CokernelCofork.IsColimit.ofπUnop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
    (w : f ≫ p = 0) (h : IsColimit (CokernelCofork.ofπ p w)) :
    IsLimit (KernelFork.ofι p.unop (show p.unop ≫ f.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  KernelFork.IsLimit.ofι _ _
    (fun x hx => (h.desc (CokernelCofork.ofπ x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Cofork.IsColimit.π_desc h))
    (fun x hx b hb => Quiver.Hom.op_inj (Cofork.IsColimit.hom_ext h
      (by simpa only [Quiver.Hom.op_unop, Cofork.IsColimit.π_desc] using Quiver.Hom.unop_inj hb)))

/-- A limit kernel fork gives a colimit cokernel cofork in the opposite category -/
def KernelFork.IsLimit.ofιOp {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.op
      (show f.op ≫ i.op = 0 by rw [← op_comp, w, op_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.unop (Quiver.Hom.op_inj hx))).op)
    (fun _ _ => Quiver.Hom.unop_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.unop_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.unop_op, Fork.IsLimit.lift_ι] using Quiver.Hom.op_inj hb)))

/-- A limit kernel fork in the opposite category gives a colimit cokernel cofork
in the original category -/
def KernelFork.IsLimit.ofιUnop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
    (w : i ≫ f = 0) (h : IsLimit (KernelFork.ofι i w)) :
    IsColimit (CokernelCofork.ofπ i.unop
      (show f.unop ≫ i.unop = 0 by rw [← unop_comp, w, unop_zero])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => (h.lift (KernelFork.ofι x.op (Quiver.Hom.unop_inj hx))).unop)
    (fun _ _ => Quiver.Hom.op_inj (Fork.IsLimit.lift_ι h))
    (fun x hx b hb => Quiver.Hom.op_inj (Fork.IsLimit.hom_ext h (by
      simpa only [Quiver.Hom.op_unop, Fork.IsLimit.lift_ι] using Quiver.Hom.unop_inj hb)))

end HasZeroMorphisms

end CategoryTheory.Limits
