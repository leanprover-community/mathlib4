/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Generators

/-!
# Quasicategories and internal homs

A simplicial set `X` is a quasicategory if and only if the induced map on internal homs
`Fun(Δ[2], X) ⟶ Fun(Λ[2, 1], X)` is an inner fibration.
-/

public section

universe u

open CategoryTheory Limits MonoidalClosed Functor

open scoped Simplicial

namespace SSet

lemma quasicategory_iff_innerFibration_pre_horn₂₁ (X : SSet.{u}) :
    Quasicategory X ↔ InnerFibration ((pre Λ[2, 1].ι).app X) := by
  rw [quasicategory_iff_innerFibration]
  exact horn₂₁.innerFibration_iff_pullbackObjObjπ
    (PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal)

lemma quasicategory_iff_rlp_monomorphisms_pre_horn₂₁ (X : SSet.{u}) :
    Quasicategory X ↔
      (MorphismProperty.monomorphisms SSet).rlp ((pre Λ[2, 1].ι).app X) := by
  rw [quasicategory_iff_innerFibration]
  exact horn₂₁.innerFibration_iff_rlp_monomorphisms_pullbackObjObjπ
    (PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal)


end SSet
