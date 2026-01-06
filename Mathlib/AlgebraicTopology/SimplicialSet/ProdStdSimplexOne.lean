/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne

/-!
# Binary products `Δ[n] ⊗ Δ[1]`

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

namespace prodStdSimplex

variable {p : ℕ}

namespace nonDegenerateEquiv₁

def toFun (i : Fin (p + 1)) : (Δ[p] ⊗ Δ[1]).nonDegenerate (p + 1) :=
  ⟨⟨stdSimplex.objEquiv.symm (SimplexCategory.σ i),
    stdSimplex.objMk₁ i.succ.castSucc⟩, by
  sorry⟩

end nonDegenerateEquiv₁

noncomputable def nonDegenerateEquiv₁ :
    Fin (p + 1) ≃ (Δ[p] ⊗ Δ[1] : SSet.{u}).nonDegenerate (p + 1) :=
  Equiv.ofBijective nonDegenerateEquiv₁.toFun (by
    refine ⟨fun _ _ h ↦ ?_, ?_⟩
    · simpa using stdSimplex.objMk₁_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
    · sorry)

@[simp]
lemma nonDegenerateEquiv₁_fst (i : Fin (p + 1)) :
    (nonDegenerateEquiv₁ i).1.1 =
      (stdSimplex.objEquiv (m := (op ⦋p + 1⦌))).symm (SimplexCategory.σ i) := rfl

@[simp]
lemma nonDegenerateEquiv₁_snd (i : Fin (p + 1)) :
    (nonDegenerateEquiv₁ i).1.2 =
      stdSimplex.objMk₁ i.succ.castSucc := rfl

end prodStdSimplex

end SSet
