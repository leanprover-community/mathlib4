/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Presentable generators

Let `C` be a category and `κ` a regular cardinal in a universe `w`.
In this file, we introduce a structure `CardinalFilteredPresentation X κ`
which consists of a presentation of an object `X : C` as a colimit of a functor
from a `κ`-filtered category. This is used in order to introduce a property
`h : AreCardinalFilteredGenerators G κ` of a family `G : ι → C` on objects:
this property says that the objects `G i` are all `κ`-presentable and that
any object in `C` identifies as a `κ`-filtered colimit of these objects.
We show in the lemma `AreCardinalFilteredGenerators.presentable` that it
follows that any object `X` is presentable (relatively to a possibly
larger regular cardinal `κ'`).

Finally, we define a typeclass `HasCardinalFilteredGenerators C κ` saying
that `C` is locally `w`-small and that there exists a family `G : ι → C`
indexed `ι : Type w` such that `AreCardinalFilteredGenerators G κ` holds.
This is used in the definition of locally presentable and locally accessible
categories in the file `CategoryTheory.Presentable.LocallyPresentable`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C]

/-- Given an object `X` in a category `C` and a regular
cardinal `κ` (in the universe `w`), this is a presentation of `X` as the colimit
of a functor `J ⥤ C` where `J` is a `κ`-filtered category. -/
structure CardinalFilteredPresentation (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] where
  /-- the index category of the presentation -/
  J : Type w
  /-- the category structure on the index type -/
  category : Category.{w} J := by infer_instance
  isCardinalFiltered : IsCardinalFiltered J κ := by infer_instance
  /-- the functor that is part of the presentation -/
  F : J ⥤ C
  /-- the `ι` field of the cocone -/
  ι : F ⟶ (Functor.const _).obj X
  /-- `X` is the colimit of the functor `F` -/
  isColimit : IsColimit (Cocone.mk _ ι)

namespace CardinalFilteredPresentation

attribute [instance] category isCardinalFiltered

variable {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (p : CardinalFilteredPresentation X κ)

lemma isCardinalPresentable (h : ∀ (j : p.J), IsCardinalPresentable (p.F.obj j) κ)
    [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow p.J) κ') :
    IsCardinalPresentable X κ' := by
  have (k : p.J) : IsCardinalPresentable (p.F.obj k) κ' := isCardinalPresentable_of_le _ h
  exact isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end CardinalFilteredPresentation

/-- Constructor for `CardinalFilteredPresentation` -/
@[simps J F ι isColimit]
def CardinalFilteredPresentation.ofIsColimit {J : Type w} [Category.{w} J]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] :
    CardinalFilteredPresentation c.pt κ where
  J := J
  F := F
  ι := c.ι
  isColimit := hc

variable {ι : Type w} (G : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- Given a regular cardinal `κ`, this is the property that a family
of objects `G : ι → C` consists of `κ`-presentable objects and that any
object in `C` identifies as a `κ`-filtered colimit of these objects. -/
structure AreCardinalFilteredGenerators : Prop where
  isCardinalPresentable (i : ι) : IsCardinalPresentable (G i) κ
  exists_cardinalFilteredPresentation (X : C) :
    ∃ (p : CardinalFilteredPresentation X κ),
      ∀ (j : p.J), ∃ (i : ι), Nonempty (p.F.obj j ≅ G i)

namespace AreCardinalFilteredGenerators

variable {G κ} (h : AreCardinalFilteredGenerators G κ) (X : C)

/-- A choice of a presentation of an object `X` in a category `C`
as a `κ`-filtered colimit of objects in the family `G : ι → C`
when `h : AreCardinalFilteredGenerators G κ`. -/
noncomputable def presentation : CardinalFilteredPresentation X κ :=
  (h.exists_cardinalFilteredPresentation X).choose

lemma exists_presentation_obj_iso (j : (h.presentation X).J) :
    ∃ (i : ι), Nonempty ((h.presentation X).F.obj j ≅ G i) :=
  (h.exists_cardinalFilteredPresentation X).choose_spec j

instance (j : (h.presentation X).J) :
    IsCardinalPresentable.{w} ((h.presentation X).F.obj j) κ := by
  obtain ⟨i, ⟨e⟩⟩ := h.exists_presentation_obj_iso X j
  have := h.isCardinalPresentable
  exact isCardinalPresentable_of_iso e.symm κ

include h in
lemma isPresentable (i : ι) : IsPresentable.{w} (G i) := by
  have := h.isCardinalPresentable
  exact isPresentable_of_isCardinalPresentable _ κ

instance (j : (h.presentation X).J) : IsPresentable.{w} ((h.presentation X).F.obj j) :=
  isPresentable_of_isCardinalPresentable _ κ

include h in
lemma presentable [LocallySmall.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ', _, le, hκ'⟩ : ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular) (_ : κ ≤ κ'),
      HasCardinalLT (Arrow (h.presentation X).J) κ' := by
    obtain ⟨κ', h₁, h₂⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w}
      (Sum.elim (fun (_ : Unit) ↦ Arrow (h.presentation X).J) (fun (_ : Unit) ↦ κ.ord.toType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := (h.presentation X).isCardinalPresentable (by infer_instance) κ' le hκ'
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
