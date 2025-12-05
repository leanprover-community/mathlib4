/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Types.EffectiveEpi

/-!
# Epimorphisms of functors to types are effective epimorphisms

We show that epimorphisms of functors to types are regular
epimorphisms. In particular, they are effective epimorphisms.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.FunctorToTypes

open Limits

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type w} (p : F ⟶ G)

/-- If `p` is an epimorphism in a category of functors to of types,
it is also a regular epimorphism. -/
noncomputable def regularEpiOfEpi [Epi p] : RegularEpi p where
  W := pullback p p
  left := pullback.fst _ _
  right := pullback.snd _ _
  w := pullback.condition
  isColimit :=
    evaluationJointlyReflectsColimits _
      (fun j ↦ (isColimitMapCoconeCoforkEquiv _ _).2
        (Types.isColimitCoforkOfIsPullbackOfSurjective
          ((IsPullback.of_hasPullback p p).map ((evaluation _ _).obj j)) (by
            rw [← epi_iff_surjective]
            infer_instance)))

lemma effectiveEpi_of_epi [Epi p] : EffectiveEpi p := by
  have := regularEpiOfEpi p
  infer_instance

end CategoryTheory.FunctorToTypes
