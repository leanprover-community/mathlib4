/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Presentable generators

Let `C` be a category, `G : ι → C` a family of objects and `κ` a regular cardinal
(with `ι` and `κ` both in the same universe `w`). In this file, we
introduce a property `h : AreCardinalFilteredGenerators G κ`:
this property says that the objects `G i` are all `κ`-presentable and that
any object in `C` identifies as a `κ`-filtered colimit of these objects.
We show in the lemma `AreCardinalFilteredGenerators.presentable` that it
follows that any object `X` is presentable (relatively to a possibly
larger regular cardinal `κ'`).

Finally, we define a typeclass `HasCardinalFilteredGenerators C κ` saying
that `C` is locally `w`-small and that there exists a family `G : ι → C`
indexed by `ι : Type w` such that `AreCardinalFilteredGenerators G κ` holds.
This is used in the definition of locally presentable and accessible
categories in the file `CategoryTheory.Presentable.LocallyPresentable`.

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

section

variable {ι : Type w} (G : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- Given a regular cardinal `κ`, this is the property that a family
of objects `G : ι → C` consists of `κ`-presentable objects and that any
object in `C` identifies to a `κ`-filtered colimit of these objects. -/
structure AreCardinalFilteredGenerators : Prop where
  isCardinalPresentable (i : ι) : IsCardinalPresentable (G i) κ
  exists_colimitPresentation (X : C) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
      (p : ColimitPresentation J X),
        ∀ (j : J), ∃ (i : ι), Nonempty (p.diag.obj j ≅ G i)

namespace AreCardinalFilteredGenerators

variable {G κ} (h : AreCardinalFilteredGenerators G κ) (X : C)

/-- When `G : ι → C` is a family of objects such that `AreCardinalFilteredGenerators G κ`
holds, and `X : C`, this is the index category of a presentation of `X`
as a `κ`-filtered colimit of objects in the family `G`. -/
def J : Type w := (h.exists_colimitPresentation X).choose

noncomputable instance : SmallCategory (h.J X) :=
  (h.exists_colimitPresentation X).choose_spec.choose

noncomputable instance : IsCardinalFiltered (h.J X) κ :=
  (h.exists_colimitPresentation X).choose_spec.choose_spec.choose

/-- A choice of a presentation of an object `X` in a category `C`
as a `κ`-filtered colimit of objects in the family `G : ι → C`
when `h : AreCardinalFilteredGenerators G κ`. -/
noncomputable def colimitPresentation : ColimitPresentation (h.J X) X :=
  (h.exists_colimitPresentation X).choose_spec.choose_spec.choose_spec.choose

lemma exists_colimitPresentation_diag_obj_iso (j : h.J X) :
    ∃ (i : ι), Nonempty ((h.colimitPresentation X).diag.obj j ≅ G i) :=
  (h.exists_colimitPresentation X).choose_spec.choose_spec.choose_spec.choose_spec j

instance (j : h.J X) :
    IsCardinalPresentable.{w} ((h.colimitPresentation X).diag.obj j) κ := by
  obtain ⟨i, ⟨e⟩⟩ := h.exists_colimitPresentation_diag_obj_iso X j
  have := h.isCardinalPresentable
  exact isCardinalPresentable_of_iso e.symm κ

include h in
lemma isPresentable (i : ι) : IsPresentable.{w} (G i) :=
  have := h.isCardinalPresentable
  isPresentable_of_isCardinalPresentable _ κ

instance (j : h.J X) : IsPresentable.{w} ((h.colimitPresentation X).diag.obj j) :=
  isPresentable_of_isCardinalPresentable _ κ

include h in
lemma presentable [LocallySmall.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ', _, le, hκ'⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ ≤ κ'),
      HasCardinalLT (Arrow (h.J X)) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) ↦ Arrow (h.J X)) (fun (_ : Unit) ↦ κ.ord.toType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := (h.colimitPresentation X).isCardinalPresentable κ (by infer_instance) κ' le hκ'
  exact isPresentable_of_isCardinalPresentable _ κ'

end AreCardinalFilteredGenerators

end

/-- The property that a category `C` and a regular cardinal `κ`
satisfy `AreCardinalFilteredGenerators G κ` for a suitable family
of objects `G : ι → C`. -/
class HasCardinalFilteredGenerators (C : Type u) [hC : Category.{v} C]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] : Prop extends LocallySmall.{w} C where
  exists_generators (C κ) [hC] [hκ] : ∃ (ι : Type w) (G : ι → C),
    AreCardinalFilteredGenerators G κ

end CategoryTheory
