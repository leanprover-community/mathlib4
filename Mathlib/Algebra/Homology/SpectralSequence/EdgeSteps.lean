/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeStep

/-!
# The infinity page of a spectral sequence

-/

@[expose] public section

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable (E : SpectralSequence C c r₀)

class HasEdgeMonoAtFrom (pq : ι) (r : ℤ) : Prop where
  hasEdgeMonoAt (r' : ℤ) (hr' : r ≤ r') : E.HasEdgeMonoAt pq r'

/-- Auxiliary definition for `edgeMonoSteps`. -/
noncomputable def edgeMonoSteps' (k : ℕ) :
    (E.page (r + k) (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAtFrom pq r)).X pq := by
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)
      (by have := E.le₀_of_hasEdgeMonoAtFrom pq r; lia)).hom
  | succ k hk => exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ hk

end SpectralSequence

end CategoryTheory
