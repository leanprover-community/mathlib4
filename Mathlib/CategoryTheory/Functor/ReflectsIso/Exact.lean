/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exactness properties of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of exact functors between abelian categories.
Assume that they jointly reflect isomorphisms. We show that a short complex in `C`
is exact (resp. short exact) iff it is so after applying the functor `Fᵢ`.
Similar results are obtained for the detection of quasi-isomorphisms
between short complexes or homological complexes in `C`.
(Corresponding results for a single functor are
`HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology` and
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` in the files
`Mathlib/Algebra/Homology/QuasiIso.lean` and
`ShortComplex.quasiIso_map_iff_of_preservesLeftHomology`
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`.)

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type*} [Category* C] {I : Type*} {D : I → Type*} [∀ i, Category* (D i)]
  {F : ∀ i, C ⥤ D i}

namespace JointlyReflectIsomorphisms

variable (hP : JointlyReflectIsomorphisms F)

include hP

section

variable [HasZeroMorphisms C] [∀ i, HasZeroMorphisms (D i)]
  [∀ i, (F i).PreservesZeroMorphisms]

lemma isZero_iff [HasZeroObject C] {X : C} :
    IsZero X ↔ ∀ (i : I), IsZero ((F i).obj X) := by
  refine ⟨fun hX _ ↦ Functor.map_isZero _ hX, fun hX ↦ ?_⟩
  let φ : 0 ⟶ X := 0
  have : IsIso φ := by
    rw [hP.isIso_iff]
    exact fun i ↦ (Functor.map_isZero _ (isZero_zero _)).isIso (hX i) _
  exact (isZero_zero C).of_iso (asIso φ).symm

variable [CategoryWithHomology C] [∀ i, (F i).PreservesHomology]

lemma exact_iff [HasZeroObject C] (S : ShortComplex C) :
    S.Exact ↔ ∀ (i : I), (S.map (F i)).Exact := by
  refine ⟨fun hS i ↦ hS.map _, fun hS ↦ ?_⟩
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [hP.isZero_iff]
  exact fun i ↦ (hS i).of_iso (S.mapHomologyIso (F i)).symm

lemma exactAt_iff [HasZeroObject C] {α : Type*} {c : ComplexShape α}
    (K : HomologicalComplex C c) (a : α) :
    K.ExactAt a ↔ ∀ (i : I), (((F i).mapHomologicalComplex c).obj K).ExactAt a :=
  hP.exact_iff _

end

section

variable [Abelian C] [∀ i, Abelian (D i)] [CategoryWithHomology C]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]

lemma shortExact_iff (S : ShortComplex C) :
    S.ShortExact ↔ ∀ (i : I), (S.map (F i)).ShortExact := by
  refine ⟨fun hS i ↦ ?_, fun hS ↦ ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    exact hS.map (F i)
  · have : Mono S.f := by
      rw [hP.jointlyReflectMonomorphisms.mono_iff]
      exact fun i ↦ (hS i).mono_f
    have : Epi S.g := by
      rw [hP.jointlyReflectEpimorphisms.epi_iff]
      exact fun i ↦ (hS i).epi_g
    exact { exact := (hP.exact_iff S).2 (fun i ↦ (hS i).exact) }

lemma shortComplexQuasiIso_iff {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso f ↔
      ∀ (i : I), ShortComplex.QuasiIso ((F i).mapShortComplex.map f) := by
  refine ⟨fun hf i ↦ inferInstance, fun hf ↦ ?_⟩
  simp only [ShortComplex.quasiIso_iff] at hf ⊢
  rw [hP.isIso_iff]
  exact fun i ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso (F i))).app
      (Arrow.mk f))).1 (hf i)

section

variable {α : Type*} {c : ComplexShape α} {K L : HomologicalComplex C c}

lemma quasiIsoAt_iff (f : K ⟶ L) (a : α) :
    QuasiIsoAt f a ↔ ∀ (i : I), QuasiIsoAt (((F i).mapHomologicalComplex c).map f) a  := by
  simpa only [quasiIsoAt_iff' _ _ _ _ rfl rfl] using
    hP.shortComplexQuasiIso_iff _

lemma quasiIso_iff (f : K ⟶ L) :
    QuasiIso f ↔ ∀ (i : I), QuasiIso (((F i).mapHomologicalComplex c).map f) := by
  simp only [_root_.quasiIso_iff, hP.quasiIsoAt_iff]
  tauto

end

end

end JointlyReflectIsomorphisms

end CategoryTheory
