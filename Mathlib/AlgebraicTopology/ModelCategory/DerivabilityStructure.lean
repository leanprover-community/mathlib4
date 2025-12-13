/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma1
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# Derivability structures attached to model categories

-/

@[expose] public section

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C]

namespace CofibrantObject

instance (X : CofibrantObject C) : IsCofibrant ((localizerMorphism C).functor.obj X) := by
  dsimp; infer_instance

instance {X : C} (R : (localizerMorphism C).LeftResolution X) :
    WeakEquivalence R.w := by
  simpa only [weakEquivalence_iff] using R.hw

instance (X : C) : IsConnected ((localizerMorphism C).LeftResolution X) := by
  let R₀ : (localizerMorphism C).LeftResolution X :=
    { w := π.pResolutionObj _
      hw := mem_weakEquivalences (π.pResolutionObj X) }
  have hR₀ (R) : Nonempty (Zigzag R R₀) := by
    have sq : CommSq (initial.to _) (initial.to _) R₀.w R.w := ⟨by simp⟩
    exact ⟨Zigzag.of_hom
      { f := sq.lift }⟩
  have : Nonempty ((localizerMorphism C).LeftResolution X) := ⟨R₀⟩
  exact zigzag_isConnected (fun R₁ R₂ ↦ (hR₀ R₁).some.trans (hR₀ R₂).some.symm)

instance : (localizerMorphism C).arrow.HasLeftResolutions := by
  intro f
  exact
   ⟨{ X₁ := Arrow.mk (π.resolutionMap f.hom)
      w := Arrow.homMk (π.pResolutionObj f.left) (π.pResolutionObj f.right)
        (π.resolutionMap_fac f.hom).symm
      hw := ⟨mem_weakEquivalences (π.pResolutionObj f.left),
        mem_weakEquivalences (π.pResolutionObj f.right)⟩}⟩

/-instance : (localizerMorphism C).IsLeftDerivabilityStructure := by
  -- needs the dual of `LocalizerMorphism.IsRightDerivabilityStructure.mk'`
  sorry-/

end CofibrantObject


end HomotopicalAlgebra
