/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/

@[expose] public section


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

to_dual_name_hint Left Right

/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
class PreservesMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], Mono (F.map f)

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
@[to_dual]
class PreservesEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], Epi (F.map f)

attribute [to_dual existing] PreservesEpimorphisms.preserves PreservesEpimorphisms.mk

@[to_dual]
instance map_epi (F : C ⥤ D) [PreservesEpimorphisms F] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (F.map f) :=
  PreservesEpimorphisms.preserves f

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
monomorphisms. -/
class ReflectsMonomorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
  monomorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Mono (F.map f) → Mono f

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
epimorphisms. -/
@[to_dual]
class ReflectsEpimorphisms (F : C ⥤ D) : Prop where
  /-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
  epimorphisms. -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), Epi (F.map f) → Epi f

attribute [to_dual existing] ReflectsEpimorphisms.reflects ReflectsEpimorphisms.mk

@[to_dual]
theorem epi_of_epi_map (F : C ⥤ D) [ReflectsEpimorphisms F] {X Y : C} {f : X ⟶ Y}
    (h : Epi (F.map f)) : Epi f :=
  ReflectsEpimorphisms.reflects f h

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
instance preservesMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [PreservesMonomorphisms F]
    [PreservesMonomorphisms G] : PreservesMonomorphisms (F ⋙ G) where
  preserves f h := by
    rw [comp_map]
    exact inferInstance

@[to_dual]
instance reflectsMonomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [ReflectsMonomorphisms F]
    [ReflectsMonomorphisms G] : ReflectsMonomorphisms (F ⋙ G) where
  reflects _ h := F.mono_of_mono_map (G.mono_of_mono_map h)

@[to_dual]
theorem preservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesEpimorphisms F :=
  ⟨fun f _ => G.epi_of_epi_map <| show Epi ((F ⋙ G).map f) from inferInstance⟩

@[to_dual]
theorem reflectsEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [PreservesEpimorphisms G] [ReflectsEpimorphisms (F ⋙ G)] : ReflectsEpimorphisms F :=
  ⟨fun f _ => (F ⋙ G).epi_of_epi_map <| show Epi (G.map (F.map f)) from inferInstance⟩

@[to_dual]
lemma PreservesMonomorphisms.of_natTrans {F G : C ⥤ D} [PreservesMonomorphisms F]
    (f : G ⟶ F) [∀ X, Mono (f.app X)] :
    PreservesMonomorphisms G where
  preserves {X Y} π hπ := by
    suffices Mono (G.map π ≫ f.app Y) from mono_of_mono (G.map π) (f.app Y)
    rw [f.naturality π]
    infer_instance

@[to_dual]
theorem PreservesMonomorphisms.of_iso {F G : C ⥤ D} [PreservesMonomorphisms F] (α : F ≅ G) :
    PreservesMonomorphisms G :=
  of_natTrans α.inv

@[to_dual]
theorem PreservesMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    PreservesMonomorphisms F ↔ PreservesMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[to_dual]
theorem ReflectsMonomorphisms.of_iso {F G : C ⥤ D} [ReflectsMonomorphisms F] (α : F ≅ G) :
    ReflectsMonomorphisms G where
  reflects {X Y} f h := by
    apply F.mono_of_mono_map
    suffices F.map f = (α.app X).hom ≫ G.map f ≫ (α.app Y).inv from this ▸ mono_comp _ _
    simp

@[to_dual]
theorem ReflectsMonomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    ReflectsMonomorphisms F ↔ ReflectsMonomorphisms G :=
  ⟨fun _ => of_iso α, fun _ => of_iso α.symm⟩

@[deprecated (since := "2026-06-25")]
alias preservedMonomorphisms.of_natTrans := PreservesMonomorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservedMonomorphisms.of_iso := PreservesMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservedMonomorphisms.iso_iff := PreservesMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.of_iso := ReflectsMonomorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsMonomorphisms.iso_iff := ReflectsMonomorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias preservedEpimorphisms.of_natTrans := PreservesEpimorphisms.of_natTrans
@[deprecated (since := "2026-06-25")]
alias preservedEpimorphisms.of_iso := PreservesEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias preservedEpimorphisms.iso_iff := PreservesEpimorphisms.iso_iff
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.of_iso := ReflectsEpimorphisms.of_iso
@[deprecated (since := "2026-06-25")]
alias reflectsEpimorphisms.iso_iff := ReflectsEpimorphisms.iso_iff

@[to_dual]
theorem preservesEpimorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    PreservesEpimorphisms F where
  preserves {X Y} f hf := ⟨by
    intro Z g h H
    replace H := congr_arg (adj.homEquiv X Z) H
    rwa [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left, cancel_epi,
      Equiv.apply_eq_iff_eq] at H⟩

@[to_dual]
instance (priority := 100) preservesEpimorphisms_of_isLeftAdjoint (F : C ⥤ D) [IsLeftAdjoint F] :
    PreservesEpimorphisms F :=
  preservesEpimorphisms_of_adjunction (Adjunction.ofIsLeftAdjoint F)

@[to_dual]
instance (priority := 100) reflectsMonomorphisms_of_faithful (F : C ⥤ D) [Faithful F] :
    ReflectsMonomorphisms F where
  reflects {X} {Y} f _ :=
    ⟨fun {Z} g h hgh =>
      F.map_injective ((cancel_mono (F.map f)).1 (by rw [← F.map_comp, hgh, F.map_comp]))⟩

@[to_dual]
instance {F G : C ⥤ D} (f : F ⟶ G) [IsSplitEpi f] (X : C) : IsSplitEpi (f.app X) :=
  inferInstanceAs (IsSplitEpi (((evaluation C D).obj X).map f))

@[to_dual]
lemma PreservesEpimorphisms.ofRetract {F G : C ⥤ D} (r : Retract G F) [F.PreservesEpimorphisms] :
    G.PreservesEpimorphisms where
  preserves := (PreservesEpimorphisms.of_natTrans r.r).preserves

@[deprecated (since := "2026-06-25")]
alias preservesEpimorphisms.ofRetract := PreservesEpimorphisms.ofRetract
@[deprecated (since := "2026-06-25")]
alias preservesMonomorphisms.ofRetract := PreservesMonomorphisms.ofRetract

section

variable (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
@[to_dual
/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/]
noncomputable def splitEpiEquiv [Full F] [Faithful F] : SplitEpi f ≃ SplitEpi (F.map f) where
  toFun f := f.map F
  invFun s := ⟨F.preimage s.section_, by
    apply F.map_injective
    simp only [map_comp, map_preimage, map_id]
    apply SplitEpi.id⟩
  left_inv := by cat_disch
  right_inv x := by cat_disch

@[to_dual (attr := simp)]
theorem isSplitEpi_iff [Full F] [Faithful F] : IsSplitEpi (F.map f) ↔ IsSplitEpi f := by
  constructor
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).invFun h.exists_splitEpi.some)
  · intro h
    exact IsSplitEpi.mk' ((splitEpiEquiv F f).toFun h.exists_splitEpi.some)

@[to_dual (attr := simp)]
theorem epi_map_iff_epi [hF₁ : PreservesEpimorphisms F] [hF₂ : ReflectsEpimorphisms F] :
    Epi (F.map f) ↔ Epi f := by
  constructor
  · exact F.epi_of_epi_map
  · intro h
    exact F.map_epi f

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitEpiCategory`,
then `D` also is. -/
@[to_dual
/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `SplitMonoCategory`,
then `D` also is. -/]
theorem splitEpiCategoryImpOfIsEquivalence [IsEquivalence F] [SplitEpiCategory C] :
    SplitEpiCategory D :=
  ⟨fun {X} {Y} f => by
    intro
    rw [← F.inv.isSplitEpi_iff f]
    apply isSplitEpi_of_epi⟩

end

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

@[to_dual]
theorem strongEpi_map_of_strongEpi (adj : F ⊣ F') (f : A ⟶ B) [F'.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] [StrongEpi f] : StrongEpi (F.map f) :=
  ⟨inferInstance, fun X Y Z => by
    intro
    rw [adj.hasLiftingProperty_iff]
    infer_instance⟩

@[to_dual]
instance strongEpi_map_of_isEquivalence [F.IsEquivalence] (f : A ⟶ B) [_h : StrongEpi f] :
    StrongEpi (F.map f) :=
  F.asEquivalence.toAdjunction.strongEpi_map_of_strongEpi f

@[to_dual]
instance (adj : F ⊣ F') {X : C} {Y : D} (f : F.obj X ⟶ Y) [hf : Mono f] [F.ReflectsMonomorphisms] :
    Mono (adj.homEquiv _ _ f) :=
  F.mono_of_mono_map <| by
    rw [← (homEquiv adj X Y).symm_apply_apply f] at hf
    exact mono_of_mono_fac (adj.homEquiv_counit _ _ _).symm

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[to_dual (attr := simp)]
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
