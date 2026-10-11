/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Endofunctor.EquivInserter
public import Mathlib.CategoryTheory.Inserter.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Colimits of (co)algebras

Let `F : C ⥤ C` be an endofunctor. We show that the
category `Algebra F` has all colimits preserved by `F`, and that the
forgetful functor `Algebra F ⥤ C` preserves and reflect these colimits.

# TODO: dualise to limits

-/

@[expose] public section

namespace CategoryTheory.Endofunctor

variable {C J : Type*} [Category* C] [Category* J] {F G : C ⥤ C}

open Limits

namespace Algebra

instance hasColimit (K : J ⥤ Algebra F) [HasColimit (K ⋙ forget F)]
    [PreservesColimit (K ⋙ forget F) F] : HasColimit K :=
  let K' : J ⥤ Inserter F (𝟭 C) := K ⋙ (equivInserter F).functor
  have : HasColimit (K' ⋙ Inserter.proj _ _) := show HasColimit (K ⋙ forget F) by assumption
  have : PreservesColimit (K' ⋙ Inserter.proj _ _) F :=
    show PreservesColimit (K ⋙ forget F) F by assumption
  have : HasColimit K' := by infer_instance
  Adjunction.hasColimit_of_comp_equivalence _ (equivInserter F).functor

instance hasColimitsOfShape [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    HasColimitsOfShape J (Algebra F) where

instance preservesColimitsOfShape_forget [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J (forget F) where
  preservesColimit {K} := by
    constructor
    intro c hc
    constructor
    let hc₁ := isColimitOfPreserves (equivInserter F).functor hc
    let e : (K ⋙ (equivInserter F).functor) ⋙ Inserter.proj F (𝟭 C) ≅ K ⋙ forget F :=
      .refl _
    exact IsColimit.equivOfNatIsoOfIso e _ ((forget F).mapCocone c)
      (Cocone.ext (.refl _) (fun j ↦ by simp [e]))
      (isColimitOfPreserves (Inserter.proj _ _) hc₁)

instance reflectsColimitsOfShape_proj [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    ReflectsColimitsOfShape J (forget F) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Algebra

namespace Coalgebra

instance hasColimit (K : J ⥤ Coalgebra F) [HasColimit (K ⋙ forget F)]
    [PreservesColimit (K ⋙ forget F) F] : HasColimit K :=
  let K' : J ⥤ Inserter (𝟭 C) F := K ⋙ (equivInserter F).functor
  have : HasColimit (K' ⋙ Inserter.proj _ _) := show HasColimit (K ⋙ forget F) by assumption
  have : PreservesColimit (K' ⋙ Inserter.proj _ _) F :=
    show PreservesColimit (K ⋙ forget F) F by assumption
  have : HasColimit K' := by infer_instance
  Adjunction.hasColimit_of_comp_equivalence _ (equivInserter F).functor

instance hasColimitsOfShape [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    HasColimitsOfShape J (Coalgebra F) where

instance preservesColimitsOfShape_forget [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J (forget F) where
  preservesColimit {K} := by
    constructor
    intro c hc
    constructor
    let hc₁ := isColimitOfPreserves (equivInserter F).functor hc
    let e : (K ⋙ (equivInserter F).functor) ⋙ Inserter.proj (𝟭 C) F ≅ K ⋙ forget F :=
      .refl _
    exact IsColimit.equivOfNatIsoOfIso e _ ((forget F).mapCocone c)
      (Cocone.ext (.refl _) (fun j ↦ by simp [e]))
      (isColimitOfPreserves (Inserter.proj _ _) hc₁)

instance reflectsColimitsOfShape_proj [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    ReflectsColimitsOfShape J (forget F) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Coalgebra

end CategoryTheory.Endofunctor
