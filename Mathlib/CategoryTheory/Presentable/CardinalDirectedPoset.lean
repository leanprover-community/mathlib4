/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Order.Category.PartOrdEmb
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# The κ-accessible category of κ-directed posets

Given a regular cardinal `κ : Cardinal.{u}`, we define the
category `CardinalFilteredPoset κ` of `κ`-directed partially ordered
types (with order embeddings as morphisms), and we show that it is
a `κ`-accessible category.

-/

universe u

open CategoryTheory Limits

namespace PartOrdEmb

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The property of objects in `PartOrdEmb` that are
satisfied by partially ordered types of cardinality `< κ`. -/
abbrev isCardinalFiltered : ObjectProperty PartOrdEmb.{u} :=
    fun X ↦ IsCardinalFiltered X κ

@[simp]
lemma isCardinalFiltered_iff (X : PartOrdEmb.{u}) :
    isCardinalFiltered κ X ↔ IsCardinalFiltered X κ := Iff.rfl

instance : (isCardinalFiltered κ).IsClosedUnderIsomorphisms where
  of_iso e _ := .of_equivalence κ (orderIsoOfIso e).equivalence

namespace Limits.CoconePt

variable {κ} {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ PartOrdEmb.{u}} {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

lemma isCardinalFiltered_pt (hF : ∀ j, IsCardinalFiltered (F.obj j) κ) :
    letI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  letI := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k ↦ Types.jointly_surjective_of_isColimit hc (f k)
  let j := IsCardinalFiltered.max j₀ hK
  let x₁ (k : K) : F.obj j := F.map (IsCardinalFiltered.toMax j₀ hK k) (x₀ k)
  have hx₁ (k : K) : c.ι.app j (x₁ k) = c.ι.app (j₀ k) (x₀ k) :=
    congr_fun (c.w (IsCardinalFiltered.toMax j₀ hK k))  _
  refine ⟨(cocone hc).ι.app j (IsCardinalFiltered.max x₁ hK),
    fun k ↦ ?_⟩
  rw [← hx₀, ← hx₁]
  exact ((cocone hc).ι.app j).hom.monotone
    (leOfHom (IsCardinalFiltered.toMax x₁ hK k))

end Limits.CoconePt

instance (J : Type u) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFiltered κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    have := isFiltered_of_isCardinalFiltered J κ
    rintro X ⟨p⟩
    simp only [(isCardinalFiltered κ).prop_iff_of_iso
      (p.isColimit.coconePointUniqueUpToIso
        (Limits.isColimitCocone (colimit.isColimit (p.diag ⋙ forget PartOrdEmb)))),
      isCardinalFiltered_iff, Limits.cocone_pt_coe]
    exact Limits.CoconePt.isCardinalFiltered_pt _ p.prop_diag_obj

end PartOrdEmb

namespace CategoryTheory

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The category of `κ`-filtered partially ordered types,
with morphisms given by order embeddings. -/
abbrev CardinalFilteredPoset :=
  (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

variable {κ} in
/-- The embedding of the category of `κ`-filtered
partially ordered types in the category of partially
ordered types. -/
abbrev CardinalFilteredPoset.ι :
    CardinalFilteredPoset κ ⥤ PartOrdEmb :=
  ObjectProperty.ι _

namespace CardinalFilteredPoset

instance (J : CardinalFilteredPoset κ) : IsCardinalFiltered J.obj κ := J.property

instance : HasCardinalFilteredColimits (CardinalFilteredPoset κ) κ where
  hasColimitsOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

/-- The property of posets in `CardinalFilteredPoset κ` that are
of cardinality `< κ` and have terminal object. -/
def hasCardinalLTWithTerminal : ObjectProperty (CardinalFilteredPoset κ) :=
  fun J ↦ HasCardinalLT J.obj κ ∧ HasTerminal J.obj

instance : ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ) where
  exists_small_le' := by
    obtain ⟨X, hX⟩ : ∃ (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.toType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalFilteredPoset κ :=
      { obj := .of a.1
        property := a.2.2.1.1 }
    refine ⟨.ofObj ι, inferInstance, fun J ⟨hJ, _⟩ ↦ ?_⟩
    obtain ⟨f⟩ : Cardinal.mk J.obj ≤ Cardinal.mk X := by
      simpa [hX] using ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 hJ).le
    let e := Equiv.ofInjective _ f.injective
    letI : PartialOrder (Set.range f) := PartialOrder.lift e.symm e.symm.injective
    let e' : Set.range f ≃o J.obj := { toEquiv := e.symm, map_rel_iff' := by rfl }
    exact ⟨_, ⟨⟨Set.range f, inferInstance,
      ⟨⟨IsCardinalFiltered.of_equivalence κ e'.symm.equivalence⟩⟩⟩⟩,
        ⟨CardinalFilteredPoset.ι.preimageIso (PartOrdEmb.Iso.mk (by exact e'.symm))⟩⟩

lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := sorry
  exists_colimitsOfShape := sorry

instance : IsCardinalAccessibleCategory (CardinalFilteredPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

end CardinalFilteredPoset

end CategoryTheory
