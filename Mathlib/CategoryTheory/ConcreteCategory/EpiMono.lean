/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.MorphismProperty.Concrete
import Mathlib.CategoryTheory.Types

/-!
# Epi and mono in concrete categories

In this file, we relate epimorphisms and monomorphisms in a concrete category `C`
to surjective and injective morphisms, and we show that if `C` has
strong epi mono factorizations and is such that `forget C` preserves
both epi and mono, then any morphism in `C` can be factored in a
functorial manner as a composition of a surjective morphism followed
by an injective morphism.

-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [ConcreteCategory.{w} C]

open Limits MorphismProperty

namespace ConcreteCategory

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

end ConcreteCategory

end CategoryTheory
