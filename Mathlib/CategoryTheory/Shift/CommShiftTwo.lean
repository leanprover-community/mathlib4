/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Prod
import Mathlib.CategoryTheory.Shift.Twist
import Mathlib.CategoryTheory.Shift.Pullback

/-!
# Commutation to shifts of functors in two variables

-/

@[simps]
def AddMonoidHom.sum (M : Type*) [AddCommMonoid M] : M × M →+ M where
  toFun m := m.1 + m.2
  map_zero' := by simp
  map_add' := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    dsimp
    rw [add_assoc, ← add_assoc y₁, add_comm y₁, add_assoc, add_assoc]

namespace CategoryTheory

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]

section

variable (D) (M : Type*)
  [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]

structure CommShift₂Setup where
  twistShiftData : TwistShiftData (PullbackShift D (.sum M)) (M × M)
  ε (m n : M) : (CatCenter D)ˣ

end

namespace Functor

variable (G : C₁ ⥤ C₂ ⥤ D) {M : Type*}
  [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]

class CommShift₂ (h : CommShift₂Setup D M) where
  commShiftObj (X₁ : C₁) : (G.obj X₁).CommShift M
  commShift_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) : NatTrans.CommShift (G.map f) M
  commShiftFlipObj (X₂ : C₂) : (G.flip.obj X₂).CommShift M
  commShift_flip_map {X₂ Y₂ : C₂} (g : X₂ ⟶ Y₂) : NatTrans.CommShift (G.flip.map g) M
  comm (X₁ : C₁) (X₂ : C₂) (m n : M) :
      ((G.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
          (((G.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧' =
        ((G.flip.obj (X₂⟦n⟧)).commShiftIso m).hom.app X₁ ≫
          (((G.obj X₁).commShiftIso n).hom.app X₂)⟦m⟧' ≫
          (shiftComm ((G.obj X₁).obj X₂) m n).inv ≫ (h.ε m n).val.app _

namespace CommShift₂

attribute [instance] commShiftObj commShiftFlipObj
  commShift_map commShift_flip_map

end CommShift₂

end Functor

variable {M : Type*} [AddCommMonoid M] [HasShift C₁ M] [HasShift C₂ M] [HasShift D M]
variable (h : CommShift₂Setup D M)

namespace CommShift₂Setup

protected abbrev Category (h : CommShift₂Setup D M) := TwistShift h.twistShiftData

-- variable (G : C₁ × C₂ ⥤ h.Category) [G.CommShift (M × M)]
-- should be essentially equivalent to
-- variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

variable (F : C₁ ⥤ C₂ ⥤ D) [F.CommShift₂ h]

def uncurry : C₁ × C₂ ⥤ h.Category := CategoryTheory.uncurry.obj F

noncomputable def uncurryCommShiftIso (m n : M) :
    shiftFunctor (C₁ × C₂) (m, n) ⋙ h.uncurry F ≅
      h.uncurry F ⋙ shiftFunctor h.Category (m, n) :=
  fullyFaithfulCurry.preimageIso
    (NatIso.ofComponents
      (fun X₁ ↦ (NatIso.ofComponents (fun X₂ ↦
        (((F.obj (X₁⟦m⟧)).commShiftIso n).app X₂ ≪≫
        (shiftFunctor D n).mapIso (((F.flip.obj X₂).commShiftIso m).app X₁) ≪≫
        (shiftFunctorAdd D m n).symm.app _)) (fun {X₂ Y₂} f ↦ by
        dsimp [uncurry]
        simp only [Functor.map_id, NatTrans.id_app, Category.id_comp,
          Functor.commShiftIso_hom_naturality_assoc, Category.assoc, NatIso.cancel_natIso_hom_left,
          Functor.comp_obj]
        have := NatTrans.shift_app_comm (F.flip.map f) m X₁
        dsimp at this
        erw [← Functor.map_comp_assoc]
        rw [← this, Functor.map_comp_assoc]
        congr 1
        erw [← NatTrans.naturality]
        rfl))) (fun {X₁ Y₁} f ↦ by
        ext X₂
        dsimp [uncurry]
        simp only [Functor.map_id, Category.comp_id, Category.assoc]
        erw [← NatTrans.naturality]
        dsimp
        rw [← Functor.map_comp_assoc]
        have := ((F.flip.obj X₂).commShiftIso m).hom.naturality f
        dsimp at this
        rw [← this, Functor.map_comp_assoc, NatTrans.shift_app_comm_assoc (F.map (f⟦m⟧'))]))

lemma uncurryCommShiftIso_hom_app (X₁ : C₁) (X₂ : C₂) (m n : M) :
    (h.uncurryCommShiftIso F m n).hom.app (X₁, X₂) =
      ((F.obj (X₁⟦m⟧)).commShiftIso n).hom.app X₂ ≫
        ((((F.flip.obj X₂).commShiftIso m).hom.app X₁)⟦n⟧':) ≫
        (shiftFunctorAdd D m n).inv.app _ := by
  change 𝟙 _ ≫ (_ ≫ _ ≫ _) ≫ 𝟙 _ = _
  dsimp
  rw [Category.id_comp, Category.comp_id]

noncomputable instance : (h.uncurry F).CommShift (M × M) where
  iso mn := h.uncurryCommShiftIso F mn.1 mn.2
  zero := by
    ext ⟨X₁, X₂⟩
    dsimp
    rw [uncurryCommShiftIso_hom_app, Functor.commShiftIso_zero,
      Functor.commShiftIso_zero]
    simp [NatTrans.prod, uncurry]
    rw [pullbackShiftFunctorZero_inv_app, ← NatTrans.naturality_assoc,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
    dsimp
    congr 3
    sorry
  add := sorry

end CommShift₂Setup

end CategoryTheory
