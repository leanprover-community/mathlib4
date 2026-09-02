/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if `𝟭 D` is a pointwise
left Kan extension of `F` along itself, i.e. any `Y : D` is the
colimit of all `F.obj X` for all morphisms `F.obj X ⟶ Y` (which
is the condition `F.DenseAt Y`).

In the file `Mathlib/CategoryTheory/Functor/KanExtension/DenseAtYoneda`,
we obtain the density of the Yoneda embedding.
In `Mathlib/CategoryTheory/Functor/KanExtension/DenseIff`, we obtain
a characterization of the density for a full functor `F : C ⥤ D` in terms
of the fully faithfulness of the restricted Yoneda functor `D ⥤ Cᵒᵖ ⥤ Type _`.
In `Mathlib/CategoryTheory/Functor/KanExtension/StrongGenerator`, we show
that the range of a dense functor is a strong generator.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C']

namespace Functor

/-- A functor `F : C ⥤ D` is dense if any `Y : D` is a canonical colimit
relatively to `F`. -/
class IsDense (F : C ⥤ D) : Prop where
  isDenseAt (F) (Y : D) : F.isDenseAt Y

/-- This is a choice of structure `F.DenseAt Y` when `F : C ⥤ D`
is dense, and `Y : D`. -/
@[no_expose]
noncomputable def denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y :=
  (IsDense.isDenseAt F Y).some

lemma isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) :
    F.IsDense ↔
      Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension) :=
  ⟨fun _ ↦ ⟨fun _ ↦ F.denseAt _⟩, fun ⟨h⟩ ↦ ⟨fun _ ↦ ⟨h _⟩⟩⟩

instance (F : C ⥤ D) [F.IsDense] : Functor.IsLeftKanExtension (𝟭 D) (Functor.rightUnitor F).inv :=
  ((Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension F).mp ‹_›).some.isLeftKanExtension

instance (F : C ⥤ D) [F.IsDense] : F.HasPointwiseLeftKanExtension F :=
  fun X ↦ (Functor.IsDense.isDenseAt F X).some.hasPointwiseLeftKanExtensionAt

lemma IsDense.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsDense] :
    G.IsDense where
  isDenseAt Y := by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

lemma IsDense.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsDense ↔ G.IsDense :=
  ⟨fun _ ↦ of_iso e, fun _ ↦ of_iso e.symm⟩

variable (F : C ⥤ D)

instance (G : C' ⥤ C) [F.IsDense] [G.IsEquivalence] :
    (G ⋙ F).IsDense where
  isDenseAt Y := ⟨(F.denseAt Y).precompOfFinal G⟩

lemma IsDense.comp_left_iff_of_isEquivalence (G : C' ⥤ C) [G.IsEquivalence] :
    (G ⋙ F).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

instance (G : D ⥤ C') [F.IsDense] [G.IsEquivalence] :
    (F ⋙ G).IsDense where
  isDenseAt Y :=
    ⟨ letI e : Y ≅ G.obj (G.inv.obj Y) := G.asEquivalence.counitIso.symm.app Y
      DenseAt.ofIso (F.denseAt (G.inv.obj Y) |>.postcompEquivalence G) e.symm ⟩

lemma IsDense.comp_right_iff_of_isEquivalence (G : D ⥤ C') [G.IsEquivalence] :
    (F ⋙ G).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

/-- If `F` is dense, the left Kan extension of `F` along `F` is isomorphic to the identity. -/
noncomputable def IsDense.leftKanExtensionIso (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtension F ≅ 𝟭 D :=
  Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫ F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom =
      F.rightUnitor.inv := by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫ (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
      F.rightUnitor.inv.app _ :=
  congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

end Functor

end CategoryTheory
