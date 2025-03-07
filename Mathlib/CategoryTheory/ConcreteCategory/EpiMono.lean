/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.MorphismProperty.Concrete
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Epi and mono in concrete categories

In this file, we relate epimorphisms and monomorphisms in a concrete category `C`
to surjective and injective morphisms, and we show that if `C` has
strong epi mono factorizations and is such that `forget C` preserves
both epi and mono, then any morphism in `C` can be factored in a
functorial manner as a composition of a surjective morphism followed
by an injective morphism.

-/

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

open Limits MorphismProperty

namespace ConcreteCategory

section

/-- In any concrete category, injective morphisms are monomorphisms. -/
theorem mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) :
    Mono f :=
  (forget C).mono_of_mono_map ((mono_iff_injective ((forget C).map f)).2 i)

instance forget₂_preservesMonomorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [HasForget.{w} C] [Category.{v'} D] [HasForget.{w} D]
    [HasForget₂ C D] [(forget C).PreservesMonomorphisms] :
    (forget₂ C D).PreservesMonomorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesMonomorphisms_of_preserves_of_reflects _ (forget D)

instance forget₂_preservesEpimorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [HasForget.{w} C] [Category.{v'} D] [HasForget.{w} D]
    [HasForget₂ C D] [(forget C).PreservesEpimorphisms] :
    (forget₂ C D).PreservesEpimorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget D)

variable (C)

lemma surjective_le_epimorphisms :
    MorphismProperty.surjective C ≤ epimorphisms C :=
  fun _ _ _ hf => (forget C).epi_of_epi_map ((epi_iff_surjective _).2 hf)

lemma injective_le_monomorphisms :
    MorphismProperty.injective C ≤ monomorphisms C :=
  fun _ _ _ hf => (forget C).mono_of_mono_map ((mono_iff_injective _).2 hf)

lemma surjective_eq_epimorphisms_iff :
    MorphismProperty.surjective C = epimorphisms C ↔ (forget C).PreservesEpimorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : epimorphisms C f)
    rw [epi_iff_surjective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (surjective_le_epimorphisms C)
    intro _ _ f hf
    have : Epi f := hf
    change Function.Surjective ((forget C).map f)
    rw [← epi_iff_surjective]
    infer_instance

lemma injective_eq_monomorphisms_iff :
    MorphismProperty.injective C = monomorphisms C ↔ (forget C).PreservesMonomorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : monomorphisms C f)
    rw [mono_iff_injective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (injective_le_monomorphisms C)
    intro _ _ f hf
    have : Mono f := hf
    change Function.Injective ((forget C).map f)
    rw [← mono_iff_injective]
    infer_instance

lemma injective_eq_monomorphisms [(forget C).PreservesMonomorphisms] :
    MorphismProperty.injective C = monomorphisms C := by
  rw [injective_eq_monomorphisms_iff]
  infer_instance

lemma surjective_eq_epimorphisms [(forget C).PreservesEpimorphisms] :
    MorphismProperty.surjective C = epimorphisms C := by
  rw [surjective_eq_epimorphisms_iff]
  infer_instance

variable [HasStrongEpiMonoFactorisations C] [(forget C).PreservesMonomorphisms]
  [(forget C).PreservesEpimorphisms]

/-- A concrete category with strong epi mono factorizations and such that
the forget functor preserves mono and epi admits functorial surjective/injective
factorizations. -/
noncomputable def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData C :=
  (functorialEpiMonoFactorizationData C).ofLE
    (by rw [surjective_eq_epimorphisms])
    (by rw [injective_eq_monomorphisms])

instance (priority := 100) : HasFunctorialSurjectiveInjectiveFactorization C where
  nonempty_functorialFactorizationData :=
    ⟨functorialSurjectiveInjectiveFactorizationData C⟩

end

section

open CategoryTheory.Limits

theorem injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f]
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Function.Injective f :=
  (mono_iff_injective ((forget C).map f)).mp inferInstance

theorem mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y)
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Mono f ↔ Function.Injective f :=
  ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
theorem epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) :
    Epi f :=
  (forget C).epi_of_epi_map ((epi_iff_surjective ((forget C).map f)).2 s)

theorem surjective_of_epi_of_preservesPushout {X Y : C} (f : X ⟶ Y) [Epi f]
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Function.Surjective f :=
  (epi_iff_surjective ((forget C).map f)).mp inferInstance

theorem epi_iff_surjective_of_preservesPushout {X Y : C} (f : X ⟶ Y)
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Epi f ↔ Function.Surjective f :=
  ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)

theorem bijective_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f := by
  rw [← isIso_iff_bijective]
  infer_instance

/-- If the forgetful functor of a concrete category reflects isomorphisms, being an isomorphism
is equivalent to being bijective. -/
theorem isIso_iff_bijective [(forget C).ReflectsIsomorphisms]
    {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f := by
  rw [← CategoryTheory.isIso_iff_bijective]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ isIso_of_reflects_iso f (forget C)⟩

end

end ConcreteCategory

end CategoryTheory
