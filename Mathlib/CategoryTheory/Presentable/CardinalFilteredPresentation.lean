/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Presentable generators

Let `C` be a category, a regular cardinal `κ` and `P : ObjectProperty C`.
We define a predicate `P.IsCardinalFilteredGenerator κ` saying that
`P` consists of `κ`-presentable objects and that any objects in `C`
is a `κ`-filtered colimit of objects satisfying `P`.
We show that if this condition is satisfied, then `P` is a strong generator
(see `IsCardinalFilteredGenerator.isStrongGenerator`). Moreover,
if `C` is locally small, we show that any object in `C` is presentable
(see `IsCardinalFilteredGenerator.presentable`).

Finally, we define a typeclass `HasCardinalFilteredGenerator C κ` saying
that `C` is locally `w`-small and that there exists an (essentially) small `P`
such that `P.IsCardinalFilteredGenerator κ` holds.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Limits.ColimitPresentation

lemma isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : ColimitPresentation J X) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ (j : J), IsCardinalPresentable (p.diag.obj j) κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  have (k : J) : IsCardinalPresentable (p.diag.obj k) κ' := isCardinalPresentable_of_le _ h
  isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end Limits.ColimitPresentation

open Limits

namespace ObjectProperty

variable {P : ObjectProperty C}

lemma ColimitOfShape.isCardinalPresentable {X : C} {J : Type w} [SmallCategory J]
    (p : P.ColimitOfShape J X) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : P ≤ isCardinalPresentable C κ) [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow J) κ') :
    IsCardinalPresentable X κ' :=
  p.toColimitPresentation.isCardinalPresentable κ
    (fun j ↦ hP _ (p.prop_diag_obj j)) _ h hJ

variable {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (P κ) in
/-- The condition that `P : ObjectProperty C` consists of `κ`-presentable objects
and that any object of `C` is a `κ`-filtered colimit of objects satisfying `P`.
(This notion is particularly relevant when `C` is locally `w`-small and `P` is
essentially `w`-small, see `HasCardinalFilteredGenerators`, which appears in
the definitions of locally presentable and accessible categories.) -/
structure IsCardinalFilteredGenerator : Prop where
  le_isCardinalPresentable : P ≤ isCardinalPresentable C κ
  exists_colimitsOfShape (X : C) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
      P.colimitsOfShape J X

namespace IsCardinalFilteredGenerator

variable (h : P.IsCardinalFilteredGenerator κ) (X : C)

include h in
lemma of_le_isoClosure {P' : ObjectProperty C} (h₁ : P ≤ P'.isoClosure)
    (h₂ : P' ≤ isCardinalPresentable C κ) :
    P'.IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := h₂
  exists_colimitsOfShape X := by
    obtain ⟨J, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨J, inferInstance, inferInstance, by
      simpa only [colimitsOfShape_isoClosure] using colimitsOfShape_monotone J h₁ _ hX⟩

include h in
lemma isoClosure : P.isoClosure.IsCardinalFilteredGenerator κ :=
  h.of_le_isoClosure (P.le_isoClosure.trans P.isoClosure.le_isoClosure)
    (by simpa only [ObjectProperty.isoClosure_le_iff] using h.le_isCardinalPresentable)

lemma isoClosure_iff :
    P.isoClosure.IsCardinalFilteredGenerator κ ↔ P.IsCardinalFilteredGenerator κ :=
  ⟨fun h ↦ h.of_le_isoClosure (by rfl) (P.le_isoClosure.trans h.le_isCardinalPresentable),
    isoClosure⟩

include h in
lemma presentable [LocallySmall.{w} C] (X : C) :
    IsPresentable.{w} X := by
  obtain ⟨J, _, _, ⟨hX⟩⟩ := h.exists_colimitsOfShape X
  obtain ⟨κ', _, le, hκ'⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ ≤ κ'),
      HasCardinalLT (Arrow J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) ↦ Arrow J) (fun (_ : Unit) ↦ κ.ord.toType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := hX.isCardinalPresentable h.le_isCardinalPresentable _ le hκ'
  exact isPresentable_of_isCardinalPresentable _ κ'

include h in
lemma isStrongGenerator : P.IsStrongGenerator :=
  IsStrongGenerator.mk_of_exists_colimitsOfShape.{w} (fun X ↦ by
    obtain ⟨_, _, _, hX⟩ := h.exists_colimitsOfShape X
    exact ⟨_, _, hX⟩)

end IsCardinalFilteredGenerator

end ObjectProperty

/-- The property that a category `C` and a regular cardinal `κ`
satisfy `P.IsCardinalFilteredGenerators κ` for an suitable essentially
small `P : ObjectProperty C`. -/
class HasCardinalFilteredGenerator (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] : Prop extends LocallySmall.{w} C where
  exists_generator (C κ) [hC] [hκ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.EssentiallySmall.{w} P),
      P.IsCardinalFilteredGenerator κ

lemma ObjectProperty.IsCardinalFilteredGenerator.hasCardinalFilteredGenerator
    {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    [LocallySmall.{w} C] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
    (hP : P.IsCardinalFilteredGenerator κ) :
    HasCardinalFilteredGenerator C κ where
  exists_generator := ⟨P, inferInstance, hP⟩

lemma HasCardinalFilteredGenerator.exists_small_generator (C : Type u) [Category.{v} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [HasCardinalFilteredGenerator C κ] :
    ∃ (P : ObjectProperty C) (_ : ObjectProperty.Small.{w} P),
      P.IsCardinalFilteredGenerator κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  obtain ⟨Q, _, h₁, h₂⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  exact ⟨Q, inferInstance, hP.of_le_isoClosure h₂ (h₁.trans hP.le_isCardinalPresentable)⟩

@[deprecated (since := "2025-10-12")] alias AreCardinalFilteredGenerators :=
  ObjectProperty.IsCardinalFilteredGenerator
@[deprecated (since := "2025-10-12")] alias HasCardinalFilteredGenerators :=
  HasCardinalFilteredGenerator

end CategoryTheory
