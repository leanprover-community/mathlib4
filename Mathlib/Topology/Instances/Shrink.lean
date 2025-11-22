/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Logic.Small.Defs
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Topological space structure on `Shrink X`
-/

@[expose] public section

universe v u

namespace Shrink

noncomputable instance (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    TopologicalSpace (Shrink.{v} X) :=
  .induced (equivShrink X).symm inferInstance

-- trying a tweaked definition doesn't seem to help either...
/-- `equivShrink` as a homeomorphism. -/
@[simps toEquiv]
noncomputable def homeomorph2 (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    Shrink.{v} X ≃ₜ X where
  __ := equivShrink X |>.symm
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    convert continuous_induced_dom
    simp only [Equiv.invFun_as_coe, Equiv.symm_symm]
    sorry -- rfl

/-- `equivShrink` as a homeomorphism. -/
@[simps toEquiv]
noncomputable def homeomorph (X : Type u) [TopologicalSpace X] [Small.{v} X] :
    X ≃ₜ Shrink.{v} X where
  __ := equivShrink X
  continuous_toFun := by
    sorry
  continuous_invFun := continuous_induced_dom

end Shrink
