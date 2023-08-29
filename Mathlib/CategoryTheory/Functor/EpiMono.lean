/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

#align_import category_theory.functor.epi_mono from "leanprover-community/mathlib"@"32253a1a1071173b33dc7d6a218cf722c6feb514"

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
#align category_theory.functor.preserves_monomorphisms CategoryTheory.Functor.PreservesMonomorphisms

instance map_mono (F : C ⥤ D) [PreservesMonomorphisms F] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (F.map f) :=
  PreservesMonomorphisms.preserves f
#align category_theory.functor.map_mono CategoryTheory.Functor.map_mono

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)
#align category_theory.functor.preserves_epimorphisms CategoryTheory.Functor.PreservesEpimorphisms

instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f
#align category_theory.functor.map_epi CategoryTheory.Functor.map_epi

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
   /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f
#align category_theory.functor.reflects_monomorphisms CategoryTheory.Functor.ReflectsMonomorphisms

theorem mono_of_mono_map (F : C ⥤ D) [ReflectsMonomorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Mono (F.map f)) : Mono f :=
  ReflectsMonomorphisms.reflects f h
#align category_theory.functor.mono_of_mono_map CategoryTheory.Functor.mono_of_mono_map

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
      epimorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f
#align category_theory.functor.reflects_epimorphisms CategoryTheory.Functor.ReflectsEpimorphisms

theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h
#align category_theory.functor.epi_of_epi_map CategoryTheory.Functor.epi_of_epi_map

instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    -- ⊢ Mono (G.map (F.map f))
    exact inferInstance
    -- 🎉 no goals
#align category_theory.functor.preserves_monomorphisms_comp CategoryTheory.Functor.preservesMonomorphisms_comp

instance preservesEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesEpimorphisms F]
    [PreservesEpimorphisms G] : PreservesEpimorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    -- ⊢ Epi (G.map (F.map f))
    exact inferInstance
    -- 🎉 no goals
#align category_theory.functor.preserves_epimorphisms_comp CategoryTheory.Functor.preservesEpimorphisms_comp

instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where
  reflects _ h := F.mono_of_mono_map (G.mono_of_mono_map h)
#align category_theory.functor.reflects_monomorphisms_comp CategoryTheory.Functor.reflectsMonomorphisms_comp

instance reflectsEpimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsEpimorphisms F]
    [ReflectsEpimorphisms G] : ReflectsEpimorphisms (F ⋙ G) where
  reflects _ h := F.epi_of_epi_map (G.epi_of_epi_map h)
#align category_theory.functor.reflects_epimorphisms_comp CategoryTheory.Functor.reflectsEpimorphisms_comp

theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun f _ => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects

theorem preservesMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms (F ⋙ G)] [ReflectsMonomorphisms G] : PreservesMonomorphisms F :=
  ⟨fun f _ => G.mono_of_mono_map <| show Mono ((F ⋙ G).map f) from inferInstance⟩
#align category_theory.functor.preserves_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.preservesMonomorphisms_of_preserves_of_reflects

theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun f _ => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_epimorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsEpimorphisms_of_preserves_of_reflects

theorem reflectsMonomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesMonomorphisms G] [ReflectsMonomorphisms (F ⋙ G)] : ReflectsMonomorphisms F :=
  ⟨fun f _ => (F ⋙ G).mono_of_mono_map <| show Mono (G.map (F.map f)) from inferInstance⟩
#align category_theory.functor.reflects_monomorphisms_of_preserves_of_reflects CategoryTheory.Functor.reflectsMonomorphisms_of_preserves_of_reflects

theorem preservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  { preserves := fun {X} {Y} f h => by
      haveI : Mono (F.map f ≫ (α.app Y).hom) := mono_comp _ _
      -- ⊢ Mono (G.map f)
      convert (mono_comp _ _ : Mono ((α.app X).inv ≫ F.map f ≫ (α.app Y).hom))
      -- ⊢ G.map f = (α.app X).inv ≫ F.map f ≫ (α.app Y).hom
      rw [Iso.eq_inv_comp, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }
      -- 🎉 no goals
#align category_theory.functor.preserves_monomorphisms.of_iso CategoryTheory.Functor.preservesMonomorphisms.of_iso

theorem preservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => preservesMonomorphisms.of_iso α, fun _ => preservesMonomorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_monomorphisms.iso_iff CategoryTheory.Functor.preservesMonomorphisms.iso_iff

theorem preservesEpimorphisms.of_iso {F G : C ⥤ D} [PreservesEpimorphisms F] (α : F ≅ G) :
    PreservesEpimorphisms G :=
  { preserves := fun {X} {Y} f h => by
      haveI : Epi (F.map f ≫ (α.app Y).hom) := epi_comp _ _
      -- ⊢ Epi (G.map f)
      convert (epi_comp _ _ : Epi ((α.app X).inv ≫ F.map f ≫ (α.app Y).hom))
      -- ⊢ G.map f = (α.app X).inv ≫ F.map f ≫ (α.app Y).hom
      rw [Iso.eq_inv_comp, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }
      -- 🎉 no goals
#align category_theory.functor.preserves_epimorphisms.of_iso CategoryTheory.Functor.preservesEpimorphisms.of_iso

theorem preservesEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesEpimorphisms F ↔ PreservesEpimorphisms G :=
  ⟨fun _ => preservesEpimorphisms.of_iso α, fun _ => preservesEpimorphisms.of_iso α.symm⟩
#align category_theory.functor.preserves_epimorphisms.iso_iff CategoryTheory.Functor.preservesEpimorphisms.iso_iff

theorem reflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.mono_of_mono_map
      -- ⊢ Mono (F.map f)
      haveI : Mono (G.map f ≫ (α.app Y).inv) := mono_comp _ _
      -- ⊢ Mono (F.map f)
      convert (mono_comp _ _ : Mono ((α.app X).hom ≫ G.map f ≫ (α.app Y).inv))
      -- ⊢ F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv
      rw [← Category.assoc, Iso.eq_comp_inv, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }
      -- 🎉 no goals
#align category_theory.functor.reflects_monomorphisms.of_iso CategoryTheory.Functor.reflectsMonomorphisms.of_iso

theorem reflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => reflectsMonomorphisms.of_iso α, fun _ => reflectsMonomorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_monomorphisms.iso_iff CategoryTheory.Functor.reflectsMonomorphisms.iso_iff

theorem reflectsEpimorphisms.of_iso {F G : C ⥤ D} [ReflectsEpimorphisms F] (α : F ≅ G) :
    ReflectsEpimorphisms G :=
  { reflects := fun {X} {Y} f h => by
      apply F.epi_of_epi_map
      -- ⊢ Epi (F.map f)
      haveI : Epi (G.map f ≫ (α.app Y).inv) := epi_comp _ _
      -- ⊢ Epi (F.map f)
      convert (epi_comp _ _ : Epi ((α.app X).hom ≫ G.map f ≫ (α.app Y).inv))
      -- ⊢ F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv
      rw [← Category.assoc, Iso.eq_comp_inv, Iso.app_hom, Iso.app_hom, NatTrans.naturality] }
      -- 🎉 no goals
#align category_theory.functor.reflects_epimorphisms.of_iso CategoryTheory.Functor.reflectsEpimorphisms.of_iso

theorem reflectsEpimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsEpimorphisms F ↔ ReflectsEpimorphisms G :=
  ⟨fun _ => reflectsEpimorphisms.of_iso α, fun _ => reflectsEpimorphisms.of_iso α.symm⟩
#align category_theory.functor.reflects_epimorphisms.iso_iff CategoryTheory.Functor.reflectsEpimorphisms.iso_iff

theorem preservesEpimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        -- ⊢ g = h
        replace H := congr_arg (adj.homEquiv X Z) H
        -- ⊢ g = h
        rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_epimorphsisms_of_adjunction CategoryTheory.Functor.preservesEpimorphsisms_of_adjunction

instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphsisms_of_adjunction (Adjunction.ofLeftAdjoint F)
#align category_theory.functor.preserves_epimorphisms_of_is_left_adjoint CategoryTheory.Functor.preservesEpimorphisms_of_isLeftAdjoint

theorem preservesMonomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesMonomorphisms G :=
  { preserves := fun {X} {Y} f hf =>
      ⟨by
        intro Z g h H
        -- ⊢ g = h
        replace H := congr_arg (adj.homEquiv Z Y).symm H
        -- ⊢ g = h
        rwa [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_right_symm, cancel_mono,
          Equiv.apply_eq_iff_eq] at H⟩ }
#align category_theory.functor.preserves_monomorphisms_of_adjunction CategoryTheory.Functor.preservesMonomorphisms_of_adjunction

instance (priority := 100) preservesMonomorphisms_of_isRightAdjoint (F : C ⥤ D) [IsRightAdjoint F] :
    PreservesMonomorphisms F :=
  preservesMonomorphisms_of_adjunction (Adjunction.ofRightAdjoint F)
#align category_theory.functor.preserves_monomorphisms_of_is_right_adjoint CategoryTheory.Functor.preservesMonomorphisms_of_isRightAdjoint

instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F
    where reflects {X} {Y} f hf :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
                                                     -- 🎉 no goals
#align category_theory.functor.reflects_monomorphisms_of_faithful CategoryTheory.Functor.reflectsMonomorphisms_of_faithful

instance (priority := 100) reflectsEpimorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsEpimorphisms F
    where reflects {X} {Y} f hf :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_epi (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩
                                                    -- 🎉 no goals
#align category_theory.functor.reflects_epimorphisms_of_faithful CategoryTheory.Functor.reflectsEpimorphisms_of_faithful

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.section_, _⟩
    -- ⊢ F.preimage s.section_ ≫ f = 𝟙 Y
    apply F.map_injective
    -- ⊢ F.map (F.preimage s.section_ ≫ f) = F.map (𝟙 Y)
    simp only [map_comp, image_preimage, map_id]
    -- ⊢ s.section_ ≫ F.map f = 𝟙 (F.obj Y)
    apply SplitEpi.id
    -- 🎉 no goals
  left_inv := by aesop_cat
                 -- 🎉 no goals
  right_inv := by
      simp only [Function.RightInverse,Function.LeftInverse]
      -- ⊢ ∀ (x : SplitEpi (F.map f)), SplitEpi.map (SplitEpi.mk (F.preimage x.section_ …
      intro x
      -- ⊢ SplitEpi.map (SplitEpi.mk (F.preimage x.section_)) F = x
      simp only [SplitEpi.map, preimage]
      -- ⊢ SplitEpi.mk (F.map (Full.preimage x.section_)) = x
      aesop_cat
      -- 🎉 no goals
#align category_theory.functor.split_epi_equiv CategoryTheory.Functor.splitEpiEquiv

@[simp]
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f := by
  constructor
  -- ⊢ IsSplitEpi (F.map f) → IsSplitEpi f
  · intro h
    -- ⊢ IsSplitEpi f
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
    -- 🎉 no goals
  · intro h
    -- ⊢ IsSplitEpi (F.map f)
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)
    -- 🎉 no goals
#align category_theory.functor.is_split_epi_iff CategoryTheory.Functor.isSplitEpi_iff

/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/
def splitMonoEquiv [Full F] [Faithful F] : SplitMono f ≃ SplitMono (F.map f)
    where
  toFun f := f.map F
  invFun s := by
    refine' ⟨F.preimage s.retraction, _⟩
    -- ⊢ f ≫ F.preimage s.retraction = 𝟙 X
    apply F.map_injective
    -- ⊢ F.map (f ≫ F.preimage s.retraction) = F.map (𝟙 X)
    simp only [map_comp, image_preimage, map_id]
    -- ⊢ F.map f ≫ s.retraction = 𝟙 (F.obj X)
    apply SplitMono.id
    -- 🎉 no goals
  left_inv := by aesop_cat
                 -- 🎉 no goals
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse]
    -- ⊢ ∀ (x : SplitMono (F.map f)), SplitMono.map (SplitMono.mk (F.preimage x.retra …
    intro x
    -- ⊢ SplitMono.map (SplitMono.mk (F.preimage x.retraction)) F = x
    simp only [SplitMono.map,preimage]
    -- ⊢ SplitMono.mk (F.map (Full.preimage x.retraction)) = x
    aesop_cat
    -- 🎉 no goals
#align category_theory.functor.split_mono_equiv CategoryTheory.Functor.splitMonoEquiv

@[simp]
theorem isSplitMono_iff [Full F] [Faithful F] : IsSplitMono (F.map f) ↔ IsSplitMono f := by
  constructor
  -- ⊢ IsSplitMono (F.map f) → IsSplitMono f
  · intro h
    -- ⊢ IsSplitMono f
    exact IsSplitMono.mk' ((splitMonoEquiv F f).invFun h.exists_splitMono.some)
    -- 🎉 no goals
  · intro h
    -- ⊢ IsSplitMono (F.map f)
    exact IsSplitMono.mk' ((splitMonoEquiv F f).toFun h.exists_splitMono.some)
    -- 🎉 no goals
#align category_theory.functor.is_split_mono_iff CategoryTheory.Functor.isSplitMono_iff

@[simp]
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  -- ⊢ Epi (F.map f) → Epi f
  · exact F.epi_of_epi_map
    -- 🎉 no goals
  · intro h
    -- ⊢ Epi (F.map f)
    exact F.map_epi f
    -- 🎉 no goals
#align category_theory.functor.epi_map_iff_epi CategoryTheory.Functor.epi_map_iff_epi

@[simp]
theorem mono_map_iff_mono [hF₁ : PreservesMonomorphisms F] [hF₂ : ReflectsMonomorphisms F] :
    Mono (F.map f) ↔ Mono f := by
  constructor
  -- ⊢ Mono (F.map f) → Mono f
  · exact F.mono_of_mono_map
    -- 🎉 no goals
  · intro h
    -- ⊢ Mono (F.map f)
    exact F.map_mono f
    -- 🎉 no goals
#align category_theory.functor.mono_map_iff_mono CategoryTheory.Functor.mono_map_iff_mono

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `split_epi_category`,
then `D` also is. -/
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    -- ⊢ IsSplitEpi f
    rw [← F.inv.isSplitEpi_iff f]
    -- ⊢ IsSplitEpi ((inv F).map f)
    apply isSplitEpi_of_epi⟩
    -- 🎉 no goals
#align category_theory.functor.split_epi_category_imp_of_is_equivalence CategoryTheory.Functor.splitEpiCategoryImpOfIsEquivalence

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [h₁ : F'.PreservesMonomorphisms]
    [h₂ : F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    -- ⊢ HasLiftingProperty (F.map f) Z
    rw [adj.hasLiftingProperty_iff]
    -- ⊢ HasLiftingProperty f (F'.map Z)
    infer_instance⟩
    -- 🎉 no goals
#align category_theory.adjunction.strong_epi_map_of_strong_epi CategoryTheory.Adjunction.strongEpi_map_of_strongEpi

instance strongEpi_map_of_isEquivalence [IsEquivalence F] (f : A ⟶ B) [_h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f
#align category_theory.adjunction.strong_epi_map_of_is_equivalence CategoryTheory.Adjunction.strongEpi_map_of_isEquivalence

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[simp]
theorem strongEpi_map_iff_strongEpi_of_isEquivalence [IsEquivalence F] :
    StrongEpi (F.map f) ↔ StrongEpi f := by
  constructor
  -- ⊢ StrongEpi (F.map f) → StrongEpi f
  · intro
    -- ⊢ StrongEpi f
    have e : Arrow.mk f ≅ Arrow.mk (F.inv.map (F.map f)) :=
      Arrow.isoOfNatIso F.asEquivalence.unitIso (Arrow.mk f)
    rw [StrongEpi.iff_of_arrow_iso e]
    -- ⊢ StrongEpi ((inv F).map (F.map f))
    infer_instance
    -- 🎉 no goals
  · intro
    -- ⊢ StrongEpi (F.map f)
    infer_instance
    -- 🎉 no goals
#align category_theory.functor.strong_epi_map_iff_strong_epi_of_is_equivalence CategoryTheory.Functor.strongEpi_map_iff_strongEpi_of_isEquivalence

end CategoryTheory.Functor
