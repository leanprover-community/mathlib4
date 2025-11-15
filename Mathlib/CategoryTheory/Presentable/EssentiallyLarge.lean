/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# Accessible categories are essentially large

If a category `C` satisfies `HasCardinalFilteredGenerator C κ` for `κ : Cardinal.{w}`
(e.g. it is locally `κ`-presentable or `κ`-accessible),
then `C` is equivalent to a `w`-large category, i.e. a category whose type
of objects is in `Type (w + 1)` and whose types of morphisms are in `Type w`.

-/

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

namespace ObjectProperty.IsCardinalFilteredGenerator

variable [LocallySmall.{w} C] {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    (hP : P.IsCardinalFilteredGenerator κ)

include hP in
lemma essentiallyLarge_top :
    ObjectProperty.EssentiallySmall.{w + 1} (C := C) ⊤ := by
  let e := equivSmallModel.{w} P.FullSubcategory
  let ι := Σ (J : Type w) (_ : SmallCategory J),
    { F : J ⥤ _ // HasColimit (F ⋙ e.inverse ⋙ P.ι) }
  let φ : ι → C := fun ⟨j, _, F, hF⟩ ↦ colimit (F ⋙ e.inverse ⋙ P.ι)
  refine ⟨ObjectProperty.ofObj φ, inferInstance, fun X _ ↦ ?_⟩
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  let G : J ⥤ P.FullSubcategory := P.lift p.diag p.prop_diag_obj
  let iso : (G ⋙ e.functor) ⋙ e.inverse ⋙ P.ι ≅ p.diag :=
    Functor.associator _ _ _ ≪≫
    G.isoWhiskerLeft ((Functor.associator _ _ _ ).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm P.ι) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor _) _
  have : HasColimit p.diag := ⟨_, p.isColimit⟩
  have := hasColimit_of_iso iso
  let i : ι := ⟨J, inferInstance, G ⋙ e.functor, inferInstance⟩
  exact ⟨_, ⟨i⟩, ⟨((IsColimit.precomposeHomEquiv iso _).2
    (p.isColimit)).coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

end ObjectProperty.IsCardinalFilteredGenerator

variable (C κ) in
lemma HasCardinalFilteredGenerator.exists_equivalence
    [HasCardinalFilteredGenerator C κ] :
    ∃ (J : Type (w + 1)) (_ : Category.{w} J), Nonempty (C ≌ J) := by
  rw [exists_equivalence_iff_of_locallySmall]
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  exact hP.essentiallyLarge_top

end CategoryTheory
