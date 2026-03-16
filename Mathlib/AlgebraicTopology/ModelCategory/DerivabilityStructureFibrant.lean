/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# The right derivability structure attached to a model category

We show that the inclusion of the full subcategory of fibrant objects
in a model category is a right derivability structure. This is
Corollaire 10.10 in [the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008].

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v u

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

namespace FibrantObject

instance {X : C} (R : (localizerMorphism C).RightResolution X) :
    WeakEquivalence R.w := by
  simpa only [weakEquivalence_iff] using R.hw

instance (X : C) : IsConnected ((localizerMorphism C).RightResolution X) := by
  let R₀ : (localizerMorphism C).RightResolution X :=
    { X₁ := mk (HoCat.resolutionObj X)
      w := HoCat.iResolutionObj X
      hw := by simpa using mem_weakEquivalences (HoCat.iResolutionObj X) }
  have hR₀ (R) : Nonempty (Zigzag R R₀) := by
    have sq : CommSq R.w R₀.w (terminal.from _) (terminal.from _) := ⟨by simp⟩
    exact ⟨Zigzag.of_inv { f := homMk sq.lift }⟩
  have : Nonempty ((localizerMorphism C).RightResolution X) := ⟨R₀⟩
  exact zigzag_isConnected (fun R₁ R₂ ↦ (hR₀ R₁).some.trans (hR₀ R₂).some.symm)

instance : (localizerMorphism C).arrow.HasRightResolutions :=
  fun f ↦ ⟨{
    X₁ := Arrow.mk (homMk (HoCat.resolutionMap f.hom))
    w := Arrow.homMk (HoCat.iResolutionObj f.left) (HoCat.iResolutionObj f.right)
      (HoCat.resolutionMap_fac f.hom)
    hw := ⟨mem_weakEquivalences (HoCat.iResolutionObj f.left),
      mem_weakEquivalences (HoCat.iResolutionObj f.right)⟩ }⟩

instance : (localizerMorphism C).IsRightDerivabilityStructure := .mk' _

end FibrantObject

end HomotopicalAlgebra
