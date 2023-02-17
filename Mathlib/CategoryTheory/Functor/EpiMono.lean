/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.functor.epi_mono
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi
import Mathbin.CategoryTheory.LiftingProperties.Adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)
#align category_theory.functor.preserves_monomorphisms CategoryTheory.Functor.PreservesMonomorphisms

instance map_mono (F : C ⥤ D) [PreservesMonomorphisms F] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (F.map f) :=
  PreservesMonomorphisms.preserves f
#align category_theory.functor.map_mono CategoryTheory.Functor.map_mono

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)
#align category_theory.functor.preserves_epimorphisms CategoryTheory.Functor.PreservesEpimorphisms

instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f
#align category_theory.functor.map_epi CategoryTheory.Functor.map_epi

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f
#align category_theory.functor.reflects_monomorphisms CategoryTheory.Functor.ReflectsMonomorphisms

theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h
#align category_theory.functor.mono_of_mono_map CategoryTheory.Functor.mono_of_mono_map

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f
#align category_theory.functor.reflects_epimorphisms CategoryTheory.Functor.ReflectsEpimorphisms

theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h
#align category_theory.functor.epi_of_epi_map CategoryTheory.Functor.epi_of_epi_map

instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G)
    where preserves X Y f h := by
    rw [comp_map]
    exact inferInstance
#align category_theory.functor.preserves_monomorphisms_comp CategoryTheory.Functor.preservesMonomorphisms_comp

instance preservesEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesEpimorphisms F]
    [PreservesEpimorphisms G] : PreservesEpimorphisms (F ⋙ G)
    where preserves X Y f h := by
    rw [comp_map]
    exact inferInstance
#align category_theory.functor.preserves_epimorphisms_comp CategoryTheory.Functor.preservesEpimorphisms_comp

instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G)
    where reflects X Y f h := F.mono_of_mono_map (G.mono_of_mono_map h)
#align category_theory.functor.reflects_monomorphisms_comp CategoryTheory.Functor.reflectsMonomorphisms_comp

instance reflectsEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsEpimorphisms F]
    [ReflectsEpimorphisms G] : ReflectsEpimorphisms (F ⋙ G)
    where reflects X Y f h := F.epi_of_epi_map (G.epi_of_epi_map h)
#align category_theory.functor.reflects_epimorphisms_comp CategoryTheory.Functor.reflectsEpimorphisms_comp

theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun X Y f hf => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects

theorem preservesMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms (F ⋙ G)] [ReflectsMonomorphisms G] : PreservesMonomorphisms F :=
  ⟨fun X Y f hf => G.mono_of_mono_map <| show Mono ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesMonomorphisms_of_preserves_of_reflects

theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun X Y f hf => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsEpimorphisms_of_preserves_of_reflects

theorem reflectsMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms G] [ReflectsMonomorphisms (F ⋙ G)] : ReflectsMonomorphisms F :=
  ⟨fun X Y f hf => (F ⋙ G).mono_of_mono_map <| show Mono (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsMonomorphisms_of_preserves_of_reflects

theorem PreservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  {
    preserves := fun X Y f h =>
      by
      haveI : mono (F.map f ≫ (α.app Y).Hom) := mono_comp _ _
      convert (mono_comp _ _ : mono ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.preserves_monomorphisms.of_iso CategoryTheory.Functor.PreservesMonomorphisms.of_iso

theorem PreservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun h => preserves_monomorphisms.of_iso α, fun h => preserves_monomorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_monomorphisms.iso_iff CategoryTheory.Functor.PreservesMonomorphisms.iso_iff

theorem PreservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) :
    PreservesEpimorphisms G :=
  {
    preserves := fun X Y f h =>
      by
      haveI : epi (F.map f ≫ (α.app Y).Hom) := epi_comp _ _
      convert (epi_comp _ _ : epi ((α.app X).inv ≫ F.map f ≫ (α.app Y).Hom))
      rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.preserves_epimorphisms.of_iso CategoryTheory.Functor.PreservesEpimorphisms.of_iso

theorem PreservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun h => preserves_epimorphisms.of_iso α, fun h => preserves_epimorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_epimorphisms.iso_iff CategoryTheory.Functor.PreservesEpimorphisms.iso_iff

theorem ReflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G :=
  {
    reflects := fun X Y f h => by
      apply F.mono_of_mono_map
      haveI : mono (G.map f ≫ (α.app Y).inv) := mono_comp _ _
      convert (mono_comp _ _ : mono ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.reflects_monomorphisms.of_iso CategoryTheory.Functor.ReflectsMonomorphisms.of_iso

theorem ReflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun h => reflects_monomorphisms.of_iso α, fun h => reflects_monomorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_monomorphisms.iso_iff CategoryTheory.Functor.ReflectsMonomorphisms.iso_iff

theorem ReflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) :
    ReflectsEpimorphisms G :=
  {
    reflects := fun X Y f h => by
      apply F.epi_of_epi_map
      haveI : epi (G.map f ≫ (α.app Y).inv) := epi_comp _ _
      convert (epi_comp _ _ : epi ((α.app X).Hom ≫ G.map f ≫ (α.app Y).inv))
      rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality] }
#align category_theory.functor.reflects_epimorphisms.of_iso CategoryTheory.Functor.ReflectsEpimorphisms.of_iso

theorem ReflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun h => reflects_epimorphisms.of_iso α, fun h => reflects_epimorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_epimorphisms.iso_iff CategoryTheory.Functor.ReflectsEpimorphisms.iso_iff

theorem preserves_epimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F :=
  {
    preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv X Z) H
        rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left, cancel_epi,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_epimorphsisms_of_adjunction CategoryTheory.Functor.preserves_epimorphsisms_of_adjunction

instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preserves_epimorphsisms_of_adjunction (Adjunction.ofLeftAdjoint F)
#align category_theory.functor.preserves_epimorphisms_of_is_left_adjoint CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint

theorem preservesMonomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesMonomorphisms G :=
  {
    preserves := fun X Y f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.hom_equiv Z Y).symm H
        rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm, cancel_mono,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_monomorphisms_of_adjunction CategoryTheory.Functor.preservesMonomorphisms_of_adjunction

instance (priority := 100) preservesMonomorphisms_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] :
    PreservesMonomorphisms F :=
  preservesMonomorphisms_of_adjunction (Adjunction.ofRightAdjoint F)
#align category_theory.functor.preserves_monomorphisms_of_is_right_adjoint CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint

instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F
    where reflects X Y f hf :=
    ⟨fun Z g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
#align category_theory.functor.reflects_monomorphisms_of_faithful CategoryTheory.Functor.reflectsMonomorphisms_of_faithful

instance (priority := 100) reflectsEpimorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsEpimorphisms F
    where reflects X Y f hf :=
    ⟨fun Z g h hgh =>
      F.map_injective ((cancel_epi (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
#align category_theory.functor.reflects_epimorphisms_of_faithful CategoryTheory.Functor.reflectsEpimorphisms_of_faithful

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.section_, _⟩
    apply F.map_injective
    simp only [map_comp, image_preimage, map_id]
    apply split_epi.id
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.functor.split_epi_equiv CategoryTheory.Functor.splitEpiEquiv

@[simp]
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f :=
  by
  constructor
  · intro h
    exact is_split_epi.mk' ((split_epi_equiv F f).invFun h.exists_split_epi.some)
  · intro h
    exact is_split_epi.mk' ((split_epi_equiv F f).toFun h.exists_split_epi.some)
#align category_theory.functor.is_split_epi_iff CategoryTheory.Functor.isSplitEpi_iff

/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/
def splitMonoEquiv [Full F] [Faithful F] : SplitMono f ≃ SplitMono (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.retraction, _⟩
    apply F.map_injective
    simp only [map_comp, image_preimage, map_id]
    apply split_mono.id
  left_inv := by tidy
  right_inv := by tidy
#align category_theory.functor.split_mono_equiv CategoryTheory.Functor.splitMonoEquiv

@[simp]
theorem isSplitMono_iff [Full F] [Faithful F] : IsSplitMono (F.map f) ↔ IsSplitMono f :=
  by
  constructor
  · intro h
    exact is_split_mono.mk' ((split_mono_equiv F f).invFun h.exists_split_mono.some)
  · intro h
    exact is_split_mono.mk' ((split_mono_equiv F f).toFun h.exists_split_mono.some)
#align category_theory.functor.is_split_mono_iff CategoryTheory.Functor.isSplitMono_iff

@[simp]
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f
#align category_theory.functor.epi_map_iff_epi CategoryTheory.Functor.epi_map_iff_epi

@[simp]
theorem mono_map_iff_mono [hF₁ : PreservesMonomorphisms F] [hF₂ : ReflectsMonomorphisms F] :
    Mono (F.map f) ↔ Mono f := by
  constructor
  · exact F.mono_of_mono_map
  · intro h
    exact F.map_mono f
#align category_theory.functor.mono_map_iff_mono CategoryTheory.Functor.mono_map_iff_mono

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `split_epi_category`,
then `D` also is. -/
def splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun X Y f => by
    intro
    rw [← F.inv.is_split_epi_iff f]
    apply is_split_epi_of_epi⟩
#align category_theory.functor.split_epi_category_imp_of_is_equivalence CategoryTheory.Functor.splitEpiCategoryImpOfIsEquivalence

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type _} [Category C] [Category D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [h₁ : F'.PreservesMonomorphisms]
    [h₂ : F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.has_lifting_property_iff]
    infer_instance⟩
#align category_theory.adjunction.strong_epi_map_of_strong_epi CategoryTheory.Adjunction.strongEpi_map_of_strongEpi

instance strongEpi_map_of_isEquivalence [IsEquivalence F] (f : A ⟶ B) [h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f
#align category_theory.adjunction.strong_epi_map_of_is_equivalence CategoryTheory.Adjunction.strongEpi_map_of_isEquivalence

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type _} [Category C] [Category D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[simp]
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  · intro
    have e : arrow.mk f ≅ arrow.mk (F.inv.map (F.map f)) :=
      arrow.iso_of_nat_iso F.as_equivalence.unit_iso (arrow.mk f)
    rw [strong_epi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance
#align category_theory.functor.strong_epi_map_iff_strong_epi_of_is_equivalence CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalence

end CategoryTheory.Functor

