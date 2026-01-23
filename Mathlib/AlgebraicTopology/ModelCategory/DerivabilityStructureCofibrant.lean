/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CofibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# The left derivability structure attached to a model category

We show that the inclusion of the full subcategory of cofibrant objects
in a model category is a left derivability structure. This is the dual to
Corollaire 10.10 in [the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008].

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v u

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]

namespace CofibrantObject

instance {X : C} (R : (localizerMorphism C).LeftResolution X) :
    WeakEquivalence R.w := by
  simpa only [weakEquivalence_iff] using R.hw

instance (X : C) : IsConnected ((localizerMorphism C).LeftResolution X) := by
  let R₀ : (localizerMorphism C).LeftResolution X :=
    { X₁ := mk (HoCat.resolutionObj X)
      w := HoCat.pResolutionObj X
      hw := by simpa using mem_weakEquivalences (HoCat.pResolutionObj X) }
  have hR₀ (R) : Nonempty (Zigzag R R₀) := by
    have sq : CommSq (initial.to _) (initial.to _) R₀.w R.w := ⟨by simp⟩
    exact ⟨Zigzag.of_hom { f := homMk (sq.lift) }⟩
  have : Nonempty ((localizerMorphism C).LeftResolution X) := ⟨R₀⟩
  exact zigzag_isConnected (fun R₁ R₂ ↦ (hR₀ R₁).some.trans (hR₀ R₂).some.symm)

instance : (localizerMorphism C).arrow.HasLeftResolutions :=
  fun f ↦ ⟨{
    X₁ := Arrow.mk (homMk (HoCat.resolutionMap f.hom))
    w := Arrow.homMk (HoCat.pResolutionObj f.left) (HoCat.pResolutionObj f.right)
      (HoCat.resolutionMap_fac f.hom).symm
    hw := ⟨mem_weakEquivalences (HoCat.pResolutionObj f.left),
      mem_weakEquivalences (HoCat.pResolutionObj f.right)⟩ }⟩

instance : (localizerMorphism C).IsLeftDerivabilityStructure := .mk' _

end CofibrantObject

end HomotopicalAlgebra
