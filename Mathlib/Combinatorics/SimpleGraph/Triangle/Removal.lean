/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
import Mathlib.Data.Finset.CastCard

/-!
# Triangle removal lemma

In this file, we prove the triangle removal lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

open Finset Fintype Nat SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]
  {s t : Finset α} {P : Finpartition (univ : Finset α)} {ε : ℝ}

namespace SimpleGraph

/-- An explicit form for the constant in the triangle removal lemma.

Note that this depends on `SzemerediRegularity.bound`, which is a tower-type exponential. This means
`triangleRemovalBound` is in practice absolutely tiny. -/
noncomputable def triangleRemovalBound (ε : ℝ) : ℝ :=
  min (2 * ⌈4/ε⌉₊^3)⁻¹ ((1 - min 1 ε/4) * (ε/(16 * bound (ε/8) ⌈4/ε⌉₊))^3)

lemma triangleRemovalBound_pos (hε : 0 < ε) : 0 < triangleRemovalBound ε := by
  have : 0 < 1 - min 1 ε/4 := by have := min_le_left 1 ε; linarith
  unfold triangleRemovalBound
  positivity

lemma triangleRemovalBound_nonpos (hε : ε ≤ 0) : triangleRemovalBound ε ≤ 0 := by
  rw [triangleRemovalBound, ceil_eq_zero.2 (div_nonpos_of_nonneg_of_nonpos _ hε)] <;> simp

lemma triangleRemovalBound_mul_cube_lt (hε : 0 < ε) :
    triangleRemovalBound ε * ⌈4 / ε⌉₊ ^ 3 < 1 := by
  calc
    _ ≤ (2 * ⌈4 / ε⌉₊ ^ 3 : ℝ)⁻¹ * ↑⌈4 / ε⌉₊ ^ 3 := by gcongr; exact min_le_left _ _
    _ = 2⁻¹ := by rw [mul_inv, inv_mul_cancel_right₀]; positivity
    _ < 1 := by norm_num

lemma triangleRemovalBound_le (hε₁ : ε ≤ 1) :
    triangleRemovalBound ε ≤ (1 - ε/4) * (ε/(16 * bound (ε/8) ⌈4/ε⌉₊)) ^ 3 := by
  simp [triangleRemovalBound, hε₁]

private lemma aux {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) : n < 2 * k * (n / k) := by
  rw [mul_assoc, two_mul, ← add_lt_add_iff_right (n % k), add_right_comm, add_assoc,
    mod_add_div n k, add_comm, add_lt_add_iff_right]
  apply (mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)

private lemma card_bound (hP₁ : P.IsEquipartition) (hP₃ : #P.parts ≤ bound (ε / 8) ⌈4 / ε⌉₊)
    (hX : s ∈ P.parts) : card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊ : ℝ) ≤ #s := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ ≤ card α / (2 * #P.parts : ℝ) := by gcongr
    _ ≤ ↑(card α / #P.parts) :=
      (div_le_iff₀' (by positivity)).2 <| mod_cast (aux ‹_› P.card_parts_le_card).le
    _ ≤ (#s : ℝ) := mod_cast hP₁.average_le_card_part hX

private lemma triangle_removal_aux (hε : 0 < ε) (hε₁ : ε ≤ 1) (hP₁ : P.IsEquipartition)
    (hP₃ : #P.parts ≤ bound (ε / 8) ⌈4 / ε⌉₊)
    (ht : t ∈ (G.regularityReduced P (ε / 8) (ε / 4)).cliqueFinset 3) :
    triangleRemovalBound ε * card α ^ 3 ≤ #(G.cliqueFinset 3) := by
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
  obtain ⟨x, y, z, ⟨-, s, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩,
                   ⟨-, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩,
                   ⟨-, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩, rfl⟩ := ht
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩)
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩)
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩)
  have dXY := P.disjoint hX hY nXY
  have dXZ := P.disjoint hX hZ nXZ
  have dYZ := P.disjoint hY hZ nYZ
  have that : 2 * (ε/8) = ε/4 := by ring
  have : 0 ≤ 1 - 2 * (ε / 8) := by
    have : ε / 4 ≤ 1 := ‹ε / 4 ≤ _›.trans (by exact mod_cast G.edgeDensity_le_one _ _); linarith
  calc
    _ ≤ (1 - ε/4) * (ε/(16 * bound (ε/8) ⌈4/ε⌉₊))^3 * card α ^ 3 := by
      gcongr; exact triangleRemovalBound_le hε₁
    _ = (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) *
          (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) := by
      ring
    _ ≤ (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * #s * #Y * #Z := by
      gcongr <;> exact card_bound hP₁ hP₃ ‹_›
    _ ≤ _ :=
      triangle_counting G (by rwa [that]) uXY dXY (by rwa [that]) uXZ dXZ (by rwa [that]) uYZ dYZ

lemma regularityReduced_edges_card_aux [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
    (hPε : P.IsUniform G (ε / 8)) (hP' : 4 / ε ≤ #P.parts) :
    2 * (#G.edgeFinset - #(G.regularityReduced P (ε/8) (ε/4)).edgeFinset : ℝ)
      < 2 * ε * (card α ^ 2 : ℕ) := by
  let A := (P.nonUniforms G (ε/8)).biUnion fun (U, V) ↦ U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε/4)).biUnion fun (U, V) ↦ G.interedges U V
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) ↦
          G.Adj x y ∧ ¬(G.regularityReduced P (ε / 8) (ε /4)).Adj x y) : ℝ) := by
      rw [univ_product_univ, mul_sub, filter_and_not, cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset, two_mul_card_edgeFinset]
      · exact monotone_filter_right _ fun xy hxy ↦ regularityReduced_le hxy
    _ ≤ #(A ∪ B ∪ C) := by gcongr; exact unreduced_edges_subset
    _ ≤ #(A ∪ B) + #C := mod_cast (card_union_le _ _)
    _ ≤ #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * (ε / 8) * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty (by positivity) hPε
    _ ≤ _ + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : ℕ) := by norm_cast; ring

/-- **Triangle Removal Lemma**. If not all triangles can be removed by removing few edges (on the
order of `(card α)^2`), then there were many triangles to start with (on the order of
`(card α)^3`). -/
lemma FarFromTriangleFree.le_card_cliqueFinset (hG : G.FarFromTriangleFree ε) :
    triangleRemovalBound ε * card α ^ 3 ≤ #(G.cliqueFinset 3) := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  obtain hε | hε := le_or_gt ε 0
  · apply (mul_nonpos_of_nonpos_of_nonneg (triangleRemovalBound_nonpos hε) _).trans <;> positivity
  let l : ℕ := ⌈4 / ε⌉₊
  have hl : 4/ε ≤ l := le_ceil (4/ε)
  rcases le_total (card α) l with hl' | hl'
  · calc
      _ ≤ triangleRemovalBound ε * ↑l ^ 3 := by
        gcongr; exact (triangleRemovalBound_pos hε).le
      _ ≤ (1 : ℝ) := (triangleRemovalBound_mul_cube_lt hε).le
      _ ≤ _ := by simpa [one_le_iff_ne_zero] using (hG.cliqueFinset_nonempty hε).card_pos.ne'
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G (by positivity : 0 < ε / 8) hl'
  have : 4/ε ≤ #P.parts := hl.trans (cast_le.2 hP₂)
  have k := regularityReduced_edges_card_aux hε hP₁ hP₄ this
  rw [mul_assoc] at k
  replace k := lt_of_mul_lt_mul_left k zero_le_two
  obtain ⟨t, ht⟩ := hG.cliqueFinset_nonempty' regularityReduced_le k
  exact triangle_removal_aux hε hP₁ hP₃ ht

/-- **Triangle Removal Lemma**. If there are not too many triangles (on the order of `(card α)^3`)
then they can all be removed by removing a few edges (on the order of `(card α)^2`). -/
lemma triangle_removal (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3) :
    ∃ G' ≤ G, ∃ _ : DecidableRel G'.Adj,
      (#G.edgeFinset - #G'.edgeFinset : ℝ) < ε * (card α^2 : ℕ) ∧ G'.CliqueFree 3 := by
  by_contra! h
  refine hG.not_ge (farFromTriangleFree_iff.2 ?_).le_card_cliqueFinset
  intro G' _ hG hG'
  exact le_of_not_gt fun i ↦ h G' hG _ i hG'

end SimpleGraph

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq SimpleGraph

/-- Extension for the `positivity` tactic: `SimpleGraph.triangleRemovalBound ε` is positive
if `ε` is. -/
@[positivity triangleRemovalBound _]
def evalTriangleRemovalBound : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(triangleRemovalBound $ε) =>
    let .positive hε ← core q(inferInstance) q(inferInstance) ε | failure
    assertInstancesCommute
    pure (.positive q(triangleRemovalBound_pos $hε))
  | _, _, _ => throwError "failed to match on Int.ceil application"

example (ε : ℝ) (hε : 0 < ε) : 0 < triangleRemovalBound ε := by positivity

end Mathlib.Meta.Positivity
