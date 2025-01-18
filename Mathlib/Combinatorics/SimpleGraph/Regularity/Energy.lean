/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Rat.BigOperators

/-!
# Energy of a partition

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/


open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma. -/
def energy : ℚ :=
  ((∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : ℚ) / (#P.parts : ℚ) ^ 2

theorem energy_nonneg : 0 ≤ P.energy G := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| sq_nonneg _

theorem energy_le_one : P.energy G ≤ 1 :=
  div_le_of_le_mul₀ (sq_nonneg _) zero_le_one <|
    calc
      ∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 ≤ #P.parts.offDiag • (1 : ℚ) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
          (sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 <| G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul_one_eq_cast _
      _ ≤ _ := by
        rw [offDiag_card, one_mul]
        norm_cast
        rw [sq]
        exact tsub_le_self

@[simp, norm_cast]
theorem coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    (P.energy G : 𝕜) =
      (∑ uv ∈ P.parts.offDiag, (G.edgeDensity uv.1 uv.2 : 𝕜) ^ 2) / (#P.parts : 𝕜) ^ 2 := by
  rw [energy]; norm_cast

end Finpartition
