/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# ...

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable (X : SSet.{u})

class IsWeaklyPolyhedralLike where
  mono {n : ℕ} (x : X.nonDegenerate n) : Mono (yonedaEquiv.symm x.val)

attribute [instance] IsWeaklyPolyhedralLike.mono

lemma nonDegenerate_δ [X.IsWeaklyPolyhedralLike]
    {n : ℕ} {x : X _⦋n + 1⦌} (hx : x ∈ X.nonDegenerate _)
    (i : Fin (n + 2)) :
    X.δ i x ∈ X.nonDegenerate _ := by
  have : Mono (yonedaEquiv.symm x) := IsWeaklyPolyhedralLike.mono ⟨x, hx⟩
  have : X.δ i x = (yonedaEquiv.symm x).app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) := rfl
  rw [this, nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply]
  infer_instance

end SSet
