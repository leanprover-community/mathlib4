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

namespace horn

def retractArrowCastSuccι {n : ℕ} (i : Fin (n + 1)) :
    RetractArrow Λ[n + 1, i.castSucc].ι (Subcomplex.unionProd.{u} Λ[1, 0] ∂Δ[n + 1]).ι := by
  sorry

def retractArrowSuccι {n : ℕ} (i : Fin (n + 1)) :
    RetractArrow Λ[n + 1, i.succ].ι (Subcomplex.unionProd.{u} Λ[1, 1] ∂Δ[n + 1]).ι := by
  sorry

end horn

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
  obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · exact (horn.retractArrowCastSuccι i).leftLiftingProperty _
  · exact (horn.retractArrowSuccι (Fin.last n)).leftLiftingProperty _

end modelCategoryQuillen

end SSet
