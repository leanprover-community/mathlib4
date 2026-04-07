/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

@[expose] public section

open CategoryTheory HomotopicalAlgebra MorphismProperty Simplicial

universe u

namespace SSet

namespace modelCategoryJoyal

/-- The family of morphisms in `SSet` which consists of inner horn inclusions
`Λ[n, i].ι : Λ[n, i] ⟶ Δ[n]` (for `0 < i < n`). -/
def J : MorphismProperty SSet.{u} :=
  .ofHoms (fun p : { p : (n : ℕ) × Fin (n + 3) // 0 < p.2 ∧ p.2 < Fin.last (p.1 + 2) } ↦
    Λ[p.1.1 + 2, p.1.2].ι)

lemma horn_ι_mem_J (n : ℕ) (i : Fin (n + 3))
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) : J (horn.{u} (n + 2) i).ι :=
  .mk (⟨⟨n, i⟩, ⟨h0, hn⟩⟩ : { p : (n : ℕ) × Fin (n + 3) // 0 < p.2 ∧ p.2 < Fin.last (p.1 + 2) })

lemma J_le_modelCategoryQuillen_J : J.{u} ≤ modelCategoryQuillen.J := by
  rintro _ _ _ ⟨⟩
  apply modelCategoryQuillen.horn_ι_mem_J

lemma innerHornInclusions_le_monomorphisms :
    J.{u} ≤ monomorphisms SSet :=
  J_le_modelCategoryQuillen_J.trans modelCategoryQuillen.J_le_monomorphisms

def innerFibrations := J.rlp

end modelCategoryJoyal

end SSet
