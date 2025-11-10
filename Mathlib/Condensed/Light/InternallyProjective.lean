/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Internal
import Mathlib.Condensed.Light.Epi
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Monoidal
/-!

# Characterization of internal projectivity in light condensed modules

This file gives an explicit condition on light condensed modules over a ring `R` to be internally
projective, namely the following:

`internallyProjective_iff_tensor_condition`: `P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the diagram
```
P ⊗ R[S'] ⟶ A
  |          |
  v          v
P ⊗ R[S]  ⟶ B
```
commute.

We also provide the analogous characterization with the tensor product commuted the other way around
(see `internallyProjective_iff_tensor_condition'`), and the special cases when `P` is the free
condensed module on a condensed set (`free_internallyProjective_iff_tensor_condition`,
`free_internallyProjective_iff_tensor_condition'`) and when `P` is the free condensed module on a
light profinite set (`free_lightProfinite_internallyProjective_iff_tensor_condition`/
`free_lightProfinite_internallyProjective_iff_tensor_condition'`).
-/

universe u

open CategoryTheory MonoidalCategory

variable (R : Type u) [CommRing R]

namespace LightCondensed

/--
The `S`-valued points of the internal hom `A ⟶[LightCondMod R] B` are in bijection with
morpisms `A ⊗ R[S] ⟶ B`.
-/
noncomputable def ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) :
    (A ⟶[LightCondMod R] B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :=
  (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm

lemma ihomPoints_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⟶[LightCondMod R] B).val.obj ⟨S⟩) :
    ihomPoints R A B S x = (MonoidalClosed.uncurry (((freeForgetAdjunction R).homEquiv _ _).symm
      ((coherentTopology LightProfinite.{u}).yonedaEquiv.symm x))) :=
  rfl

lemma ihomPoints_symm_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :
    (ihomPoints R A B S).symm x = (coherentTopology LightProfinite.{u}).yonedaEquiv
      ((freeForgetAdjunction R).homEquiv _ _ (MonoidalClosed.curry x)) := by
  rfl

lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
    (x : (P ⟶[LightCondMod R] A).val.obj ⟨S⟩) :
    (((ihom P).map e).val.app ⟨S⟩) x = (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e) := by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, Equiv.apply_symm_apply]
  rw [← MonoidalClosed.uncurry_natural_right, ← Adjunction.homEquiv_naturality_right_symm]
  congr
  ext
  simp
  rfl

lemma ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : P ⊗ (free R).obj S'.toCondensed ⟶ B) :
    (ihomPoints R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ((P ⟶[LightCondMod R] B).val.map π.op) ((ihomPoints R P B S').symm f) := by
  simp only [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply,
    Functor.comp_obj, Functor.map_comp, Adjunction.unit_naturality_assoc]
  rw [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_comp,
    GrothendieckTopology.yonedaEquiv_apply, GrothendieckTopology.yonedaEquiv_apply]
  have : (lightProfiniteToLightCondSet.map π).val.app (Opposite.op S) (𝟙 S) =
      S'.toCondensed.val.map π.op (𝟙 S') := rfl
  rw [this]
  simp
  rfl

/--
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : P ⊗ R[S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : P ⊗ R[S'] ⟶ A`, making the diagram
```
P ⊗ R[S'] ⟶ A
  |          |
  v          v
P ⊗ R[S]  ⟶ B
```
commute.
-/
lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  refine ⟨fun ⟨h⟩ A B e he S g ↦ ?_, fun h ↦ ⟨⟨fun {A B} e he ↦ ?_⟩⟩⟩
  · have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this]
    rfl

/--
`P : LightCondMod R` is internally projective if and
only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S] ⊗ P ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : R[S'] ⊗ P ⟶ A`, making the diagram
```
R[S'] ⊗ P ⟶ A
  |          |
  v          v
R[S] ⊗ P  ⟶ B
```
commute.
-/
lemma internallyProjective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : (free R).obj S.toCondensed ⊗ P ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCondensed ⊗ P ⟶ A),
          (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

/--
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is internally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the diagram
```
R[P × S'] ⟶ A
  |          |
  v          v
R[P × S]  ⟶ B
```
commute.
-/
lemma free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (P ⊗ S.toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗  S'.toCondensed) ⟶ A),
            ((free R).map (P ◁ ((lightProfiniteToLightCondSet).map π))) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, Functor.OplaxMonoidal.δ_natural_right,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh, ← Category.assoc, ← Category.assoc]
    -- Generated by `simp? [← Functor.LaxMonoidal.μ_natural_right]`.
    -- Leaving it unsqueezed is too slow
    simp only [Functor.comp_obj, Functor.comp_map, Functor.Monoidal.μIso_hom,
      ← Functor.LaxMonoidal.μ_natural_right, Functor.Monoidal.μIso_inv, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

/--
Given a `P : LightCondSet`, the light free light condensed module `R[P]` is internally projective if
and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the diagram
```
R[S' × P] ⟶ A
  |          |
  v          v
R[S × P]  ⟶ B
```
commute.
-/
lemma free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (S.toCondensed ⊗ P) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S'.toCondensed ⊗ P) ⟶ A),
            ((free R).map (((lightProfiniteToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    -- Generated by `simp?`. Leaving it unsqueezed is too slow
    simp only [Functor.Monoidal.μIso_inv, Functor.comp_obj, Functor.comp_map,
      Functor.Monoidal.μIso_hom, Functor.LaxMonoidal.μ_natural_left_assoc,
      Functor.Monoidal.δ_μ_assoc]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh, ← Category.assoc, ← Category.assoc]
    -- Generated by `simp? [← Functor.LaxMonoidal.μ_natural_left]`
    -- Leaving it unsqueezed is too slow.
    simp only [Functor.comp_obj, Functor.comp_map, Functor.Monoidal.μIso_hom,
      ← Functor.LaxMonoidal.μ_natural_left, Functor.Monoidal.μIso_inv, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

/--
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is internally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[P × S] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : R[P × S'] ⟶ A`, making the diagram
```
R[P × S'] ⟶ A
  |          |
  v          v
R[P × S]  ⟶ B
```
commute.
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((P ⊗ S).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗ S').toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp [-Functor.map_comp, ← Functor.map_comp_assoc]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp [-Functor.map_comp, ← Functor.map_comp_assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc]

/--
Given a `P : LightProfinite`, the light free light condensed module `R[P]` is internally projective
if and only if, for all `A B : LightCondMod R`, for all epimorphisms `e : A ⟶ B`, for all
`S : LightProfinite` and all morphisms `g : R[S × P] ⟶ B`, there exists a `S' : LightProfinite`
with a surjeciton `π : S' ⟶ S` and a morphism `g' : R[S' × P] ⟶ A`, making the diagram
```
R[S' × P] ⟶ A
  |          |
  v          v
R[S × P]  ⟶ B
```
commute.
-/
lemma free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((S ⊗ P).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S' ⊗ P).toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp [-Functor.map_comp, ← Functor.map_comp_assoc]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp [-Functor.map_comp, ← Functor.map_comp_assoc, ← Functor.LaxMonoidal.μ_natural_left_assoc]

end LightCondensed
