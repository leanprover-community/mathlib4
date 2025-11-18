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

variable {κ} in
/-- Constructor for objects in `CardinalFilteredPoset κ`. -/
abbrev of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalFilteredPoset κ where
  obj := J
  property := inferInstance

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

namespace cocone

variable {κ} (J : CardinalFilteredPoset κ)

def indexSet : Set (Set J.obj) := setOf (fun S ↦ HasCardinalLT S κ ∧ HasTerminal S)

instance (S : indexSet J) : HasTerminal S := S.prop.2

instance (S : indexSet J) : IsCardinalFiltered S κ := isCardinalFiltered_of_hasTerminal _ _

variable {J} in
lemma singleton_mem_indexSet (j : J.obj) : {j} ∈ indexSet J :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

instance : IsCardinalFiltered (indexSet J) κ :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k ↦ (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) ∪ {m}
    let : OrderTop S :=
      { top := ⟨m, by simp [S]⟩
        le_top := by
          rintro ⟨s, hs⟩
          simp [S] at hs
          obtain rfl | ⟨k, hs⟩ := hs
          · simp
          · simp only [Subtype.mk_le_mk]
            exact leOfHom ((by exact terminal.from (C := (α k).val) ⟨_, hs⟩) ≫
              IsCardinalFiltered.toMax _ hK k)
          }
    refine ⟨⟨S, ?_, isTerminalTop.hasTerminal⟩, fun k ↦ ?_⟩
    · have hκ : Cardinal.aleph0 ≤ κ :=  Cardinal.IsRegular.aleph0_le Fact.out
      exact hasCardinalLT_union hκ (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).2.1))
        (hasCardinalLT_of_finite _ _ hκ)
    · simp only [← Subtype.coe_le_coe, Set.le_eq_subset]
      exact subset_trans (Set.subset_iUnion_of_subset k (subset_refl _)) Set.subset_union_left )

instance : IsFiltered (indexSet J) := isFiltered_of_isCardinalFiltered _ κ

@[simps]
def functor : indexSet J ⥤ CardinalFilteredPoset κ where
  obj S := of (PartOrdEmb.of S.val)
  map {j₁ j₂} f := PartOrdEmb.ofHom
    { toFun x := ⟨x, leOfHom f x.2⟩
      inj' := by rintro ⟨x, _⟩ ⟨y, _⟩ h; simpa using h
      map_rel_iff' := by rfl }

end cocone

variable {κ} in
@[simps]
def cocone (J : CardinalFilteredPoset κ) : Cocone (cocone.functor J) where
  pt := J
  ι.app _ := PartOrdEmb.ofHom (OrderEmbedding.subtype _)

variable {κ} in
open cocone in
noncomputable def isColimitCocone (J : CardinalFilteredPoset κ) :
    IsColimit (cocone J) :=
  isColimitOfReflects (CardinalFilteredPoset.ι ⋙ forget PartOrdEmb) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j ⟨x, _⟩ ⟨y, _⟩ h ↦ ?_)
    · exact ⟨⟨_, singleton_mem_indexSet x⟩, ⟨x, rfl⟩, rfl⟩
    · obtain rfl : x = y := by simpa using h
      exact ⟨j, 𝟙 _, rfl⟩)

protected lemma isCardinalPresentable_iff (J : CardinalFilteredPoset κ) :
    IsCardinalPresentable J κ ↔ HasCardinalLT J.obj κ := by
  refine ⟨fun _ ↦ ?_, fun hJ ↦ ?_⟩
  · have : IsCardinalPresentable J.cocone.pt κ := by assumption
    obtain ⟨X, f, hf⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ (isColimitCocone J) (𝟙 _)
    have : IsSplitMono f := ⟨_, hf⟩
    exact X.2.1.of_injective f
      ((mono_iff_injective _).1 (inferInstanceAs (Mono ((forget _).map f))))
  · sorry

lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff]
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.2 }⟩⟩

instance : IsCardinalAccessibleCategory (CardinalFilteredPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

end CardinalFilteredPoset

end CategoryTheory
