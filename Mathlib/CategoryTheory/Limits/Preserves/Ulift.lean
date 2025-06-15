/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Junyan Xu, Sophie Morel
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Data.Set.Subsingleton

/-!
# `ULift` creates small (co)limits


This file shows that `uliftFunctor.{v, u}` preserves all limits and colimits, including those
potentially too big to exist in `Type u`.

As this functor is fully faithful, we also deduce that it creates `u`-small limits and
colimits.

-/

universe v w w' u

namespace CategoryTheory.Limits.Types

/--
The equivalence between `K.sections` and `(K ⋙ uliftFunctor.{v, u}).sections`. This is used to show
that `uliftFunctor` preserves limits that are potentially too large to exist in the source
category.
-/
def sectionsEquiv {J : Type*} [Category J] (K : J ⥤ Type u) :
    K.sections ≃ (K ⋙ uliftFunctor.{v, u}).sections where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` preserves limits of arbitrary size.
-/
noncomputable instance : PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesLimitsOfShape {J} := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        rw [Types.isLimit_iff ((uliftFunctor.{v, u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext _ _ (hx₁ i),
          fun y hy => ULift.ext _ _ (hx₂ y.down fun i ↦ ULift.ext_iff.mp (hy i))⟩ } }

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` creates `u`-small limits.
-/
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

variable {J : Type*} [Category J] {K : J ⥤ Type u} {c : Cocone K} (hc : IsColimit c)
variable {lc : Cocone (K ⋙ uliftFunctor.{v, u})}

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` preserves colimits of arbitrary size.
-/
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} ↦
    { preserves := fun {c} hc ↦ by
        rw [isColimit_iff_bijective_desc, ← Function.Bijective.of_comp_iff _
          (quotQuotUliftEquiv F).bijective, Quot.desc_quotQuotUliftEquiv]
        exact ULift.up_bijective.comp ((isColimit_iff_bijective_desc c).mp (Nonempty.intro hc)) } }

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` creates `u`-small colimits.
-/
noncomputable instance : CreatesColimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape :=
    { CreatesColimit := fun {_} ↦ createsColimitOfReflectsIsomorphismsOfPreserves }

end CategoryTheory.Limits.Types
