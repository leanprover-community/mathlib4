/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

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
  /-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

instance map_mono (F : C ⥤ D) [PreservesMonomorphisms F] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (F.map f) :=
  PreservesMonomorphisms.preserves f

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
   /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f

theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
      epimorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f

theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    exact inferInstance

instance preservesEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesEpimorphisms F]
    [PreservesEpimorphisms G] : PreservesEpimorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    exact inferInstance

instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where
  reflects _ h := F.mono_of_mono_map (G.mono_of_mono_map h)

instance reflectsEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsEpimorphisms F]
    [ReflectsEpimorphisms G] : ReflectsEpimorphisms (F ⋙ G) where
  reflects _ h := F.epi_of_epi_map (G.epi_of_epi_map h)

theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun f _ => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩

theorem preservesMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms (F ⋙ G)] [ReflectsMonomorphisms G] : PreservesMonomorphisms F :=
  ⟨fun f _ => G.mono_of_mono_map <| show Mono ((F ⋙ G).map f) from inferInstance⟩

theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun f _ => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩

theorem reflectsMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms G] [ReflectsMonomorphisms (F ⋙ G)] : ReflectsMonomorphisms F :=
  ⟨fun f _ => (F ⋙ G).mono_of_mono_map <| show Mono (G.map (F.map f)) from inferInstance⟩

theorem preservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  { preserves := fun {X} {Y} f h => by
      suffices G.map f = (α.app X).inv ≫ F.map f ≫ (α.app Y).hom from this ▸ mono_comp _ _
      rw [Iso.eq_inv_comp, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }

theorem preservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => preservesMonomorphisms.of_iso α, fun _ => preservesMonomorphisms.of_iso α.symm⟩

theorem preservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) :
    PreservesEpimorphisms G :=
  { preserves := fun {X} {Y} f h => by
      suffices G.map f = (α.app X).inv ≫ F.map f ≫ (α.app Y).hom from this ▸ epi_comp _ _
      rw [Iso.eq_inv_comp, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }

theorem preservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun _ => preservesEpimorphisms.of_iso α, fun _ => preservesEpimorphisms.of_iso α.symm⟩

theorem reflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.mono_of_mono_map
      suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
      rw [← Category.assoc, Iso.eq_comp_inv, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }

theorem reflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => reflectsMonomorphisms.of_iso α, fun _ => reflectsMonomorphisms.of_iso α.symm⟩

theorem reflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) :
    ReflectsEpimorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.epi_of_epi_map
      suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ epi_comp _ _
      rw [← Category.assoc, Iso.eq_comp_inv, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }

theorem reflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun _ => reflectsEpimorphisms.of_iso α, fun _ => reflectsEpimorphisms.of_iso α.symm⟩

theorem preservesEpimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.homEquiv X Z) H
        rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
          Equiv.apply_eq_iff_eq] at H⟩ }

instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphsisms_of_adjunction (Adjunction.ofIsLeftAdjoint F)

theorem preservesMonomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesMonomorphisms G :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        replace H := congr_arg (adj.homEquiv Z Y).symm H
        rwa [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm, cancel_mono,
          Equiv.apply_eq_iff_eq] at H⟩ }

instance (priority := 100) preservesMonomorphisms_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] :
    PreservesMonomorphisms F :=
  preservesMonomorphisms_of_adjunction (Adjunction.ofIsRightAdjoint F)

instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F where
  reflects {X} {Y} f hf :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩

instance (priority := 100) reflectsEpimorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsEpimorphisms F where
  reflects {X} {Y} f hf :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_epi (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
noncomputable def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by aesop_cat
  right_inv x := by aesop_cat

@[simp]
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/
noncomputable def splitMonoEquiv [Full F] [Faithful F] : SplitMono f ≃ SplitMono (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.retraction, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitMono.id⟩
  left_inv := by aesop_cat
  right_inv x := by aesop_cat

@[simp]
theorem isSplitMono_iff [Full F] [Faithful F] : IsSplitMono (F.map f) ↔ IsSplitMono f := by
  constructor
  · intro h
    exact IsSplitMono.mk' ((splitMonoEquiv F f).invFun h.exists_splitMono.some)
  · intro h
    exact IsSplitMono.mk' ((splitMonoEquiv F f).toFun h.exists_splitMono.some)

@[simp]
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

@[simp]
theorem mono_map_iff_mono [hF₁ : PreservesMonomorphisms F] [hF₂ : ReflectsMonomorphisms F] :
    Mono (F.map f) ↔ Mono f := by
  constructor
  · exact F.mono_of_mono_map
  · intro h
    exact F.map_mono f

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `split_epi_category`,
then `D` also is. -/
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [h₁ : F'.PreservesMonomorphisms]
    [h₂ : F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

instance strongEpi_map_of_isEquivalence [F.IsEquivalence] (f : A ⟶ B) [_h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

instance (adj : F ⊣ F') {X : C} {Y : D} (f : F.obj X ⟶ Y) [hf : Mono f] [F.ReflectsMonomorphisms] :
    Mono (adj.homEquiv _ _ f) :=
  F.mono_of_mono_map <| by
    rw [← (homEquiv adj X Y).symm_apply_apply f] at hf
    exact mono_of_mono_fac adj.homEquiv_counit.symm

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[simp]
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  · intro
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    infer_instance
  · intro
    infer_instance

end CategoryTheory.Functor
