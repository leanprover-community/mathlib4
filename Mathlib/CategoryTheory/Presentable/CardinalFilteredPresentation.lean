/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Presentable.Limits

/-!
# Presentable generators

-/

universe w v u v' u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

structure CardinalFilteredPresentation (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] where
  J : Type w
  category : Category.{w} J := by infer_instance
  isCardinalFiltered : IsCardinalFiltered J κ := by infer_instance
  F : J ⥤ C
  ι : F ⟶ (Functor.const _).obj X
  isColimit : IsColimit (Cocone.mk _ ι)

namespace CardinalFilteredPresentation

attribute [instance] category isCardinalFiltered

section

variable {X : C} {κ : Cardinal.{w}} [Fact κ.IsRegular]

variable (p : CardinalFilteredPresentation X κ)

instance isFiltered : IsFiltered p.J := by
  apply isFiltered_of_isCardinalDirected _ κ

lemma isCardinalPresentable_pt (h : ∀ (j : p.J), IsCardinalPresentable (p.F.obj j) κ)
    [LocallySmall.{w} C]
    (κ' : Cardinal.{w}) [Fact κ'.IsRegular] (h : κ ≤ κ')
    (hJ : HasCardinalLT (Arrow p.J) κ') :
    IsCardinalPresentable X κ' := by
  have : ∀ (k : p.J), IsCardinalPresentable (p.F.obj k) κ' :=
    fun _ ↦ isCardinalPresentable_of_le _ h
  exact isCardinalPresentable_of_isColimit _ p.isColimit κ' hJ

end

@[simps J F ι isColimit]
def ofIsColimit {J : Type w} [Category.{w} J]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] :
    CardinalFilteredPresentation c.pt κ where
  J := J
  F := F
  ι := c.ι
  isColimit := hc

variable {J : Type u'} [Category.{v'} J] [EssentiallySmall.{w} J]
  {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

noncomputable def ofIsColimitOfEssentiallySmall :
    CardinalFilteredPresentation c.pt κ where
  isCardinalFiltered := IsCardinalFiltered.of_equivalence κ (equivSmallModel J)
  J := SmallModel J
  F := (equivSmallModel J).inverse ⋙ F
  ι := whiskerLeft (equivSmallModel J).inverse c.ι
  isColimit :=
    (IsColimit.whiskerEquivalenceEquiv (equivSmallModel J).symm).1 hc

lemma ofIsColimitOfEssentiallySmall_exists_f_obj_iso
    (j : (ofIsColimitOfEssentiallySmall c hc κ).J) :
    ∃ (j₀ : J), Nonempty ((ofIsColimitOfEssentiallySmall c hc κ).F.obj j ≅
      F.obj j₀) :=
  ⟨_, ⟨Iso.refl _⟩⟩

end CardinalFilteredPresentation


variable {ι : Type w} (G : ι → C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

structure AreCardinalFilteredGenerators : Prop where
  isCardinalPresentable (i : ι) : IsCardinalPresentable (G i) κ
  exists_cardinalFilteredPresentation (X : C) :
      ∃ (p : CardinalFilteredPresentation X κ),
        ∀ (j : p.J), ∃ (i : ι), Nonempty (p.F.obj j ≅ G i)

namespace AreCardinalFilteredGenerators

variable {G κ} (h : AreCardinalFilteredGenerators G κ) (X : C)

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
    obtain ⟨κ', h₁, h₂⟩ := exists_regular_cardinal'.{w}
      (Sum.elim (fun (_ : Unit) ↦ Arrow (h.presentation X).J) (fun (_ : Unit) ↦ κ.ord.toType))
    exact ⟨κ', ⟨h₁⟩,
      le_of_lt (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using h₂ (Sum.inr ⟨⟩)),
      h₂ (Sum.inl ⟨⟩)⟩
  have := (h.presentation X).isCardinalPresentable_pt (by infer_instance) κ' le hκ'
  exact isPresentable_of_isCardinalPresentable _ κ'

end AreCardinalFilteredGenerators

end CategoryTheory
