/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# ...

## References
* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*, IV.2][gabriel-zisman-1967]

-/

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra MonoidalCategory

open scoped Simplicial

namespace SSet

namespace modelCategoryQuillen

lemma fibration_iff_hasLiftingProperty_unionProd_horn_one_boundary {E B : SSet.{u}} (p : E ⟶ B) :
    Fibration p ↔
      ∀ (n : ℕ) (i : Fin 2), HasLiftingProperty (Subcomplex.unionProd.{u} Λ[1, i] ∂Δ[n]).ι p := by
  refine ⟨fun _ n i ↦ prodStdSimplex.anodyneExtensions_unionProd_ι i n _ (mem_fibrations p),
    fun _ ↦ ?_⟩
  rw [fibration_iff]
  rintro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  sorry

end modelCategoryQuillen

end SSet
