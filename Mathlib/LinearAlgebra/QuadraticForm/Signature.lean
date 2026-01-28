/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Signature of a quadratic form

We define the signature of a quadratic form over a linearly ordered field, and show that it can be
computed from any sum-of-squares representation.

## Main results and definitions

* `QuadraticForm.sigPos`, `QuadraticForm.sigNeg`: for a quadratic form `Q`, the maximal dimension
  of a subspace on which `Q` is positive-definite (resp. negative-definite).
* `QuadraticForm.sigPos_of_equiv_weightedSumOfSquares`,
  `QuadraticForm.sigNeg_of_equiv_weightedSumOfSquares`: for any isomorphism from `Q` to a
  weighted sum of squares, `Q.sigPos` and `Q.sigNeg` are the number of positive and negative
  weights. (This is the uniqueness part of **Sylvester's law of inertia**; the existence is proved
  elsewhere.)

## Acknowledgements

This file is based on work carried out by Sina Keller, Philipp Schumann, and Nicolas Trutmann in
the course of their studies at ETH Zürich.

-/
open Finset QuadraticMap

@[expose] public noncomputable section

variable {R M M' : Type*} [AddCommGroup M] [AddCommGroup M']

section LinearOrder

variable [CommRing R] [LinearOrder R] [Module R M] (Q : QuadraticForm R M)
  [Module R M'] {Q' : QuadraticForm R M'} {V : Submodule R M}

section Equiv
variable {Q}

@[simp] lemma QuadraticMap.IsometryEquiv.map_posDef_iff (e : IsometryEquiv Q Q') :
    (Q'.restrict (V.map e.toLinearMap)).PosDef ↔ (Q.restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]

@[simp] lemma QuadraticMap.IsometryEquiv.map_negDef_iff (e : IsometryEquiv Q Q') :
    ((-Q').restrict (V.map e.toLinearMap)).PosDef ↔ ((-Q).restrict V).PosDef := by
  simp [PosDef, -Submodule.mem_map_equiv]

end Equiv

open Classical in
/-- The maximal rank of a positive-definite submodule of `M`. -/
-- Note this proof is absurdly overcomplicated in order to avoid assuming `Nontrivial R`.
noncomputable def sigPos : ℕ := max'
  {r ∈ Iic (Module.finrank R M) | ∃ V : Submodule R M,
    Module.finrank R V = r ∧ (Q.restrict V).PosDef}
  ⟨if Nontrivial R then 0 else 1, by
    split_ifs with h
    · simp only [mem_filter, mem_Iic, zero_le, true_and]
      exact ⟨⊥, finrank_bot _ _, fun x hx' ↦ (hx' <| Subsingleton.elim x 0).elim⟩
    · have : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
      simp only [mem_filter, mem_Iic, Module.finrank_subsingleton, true_and, le_refl]
      exact ⟨⊥, fun x hx' ↦ (hx' <| Subsingleton.elim x 0).elim⟩⟩

lemma sigPos_le_finrank : sigPos Q ≤ Module.finrank R M := by
  classical
  exact mem_Iic.mp <| mem_of_mem_filter _ <| max'_mem _ _

/-- Defining property of `sigPos`. -/
lemma sigPos_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | ∃ V : Submodule R M, Module.finrank R V = r ∧ (Q.restrict V).PosDef} (sigPos Q) := by
  classical
  refine ⟨(mem_filter.mp <| max'_mem _ _).2, ?_⟩
  rintro _ ⟨V, rfl, hV⟩
  apply le_max'
  rw [mem_filter, mem_Iic]
  exact ⟨V.finrank_le, V, rfl, hV⟩

open Classical in
/-- The maximal dimension of a negative-definite subspace of `M`. -/
noncomputable def sigNeg : ℕ := sigPos (-Q)

/-- Defining property of `sigNeg`. -/
lemma sigNeg_isGreatest [Module.Finite R M] [StrongRankCondition R] : IsGreatest
    {r | ∃ V : Submodule R M, Module.finrank R V = r ∧ ((-Q).restrict V).PosDef} (sigNeg Q) :=
  sigPos_isGreatest (-Q)

variable {Q}

lemma QuadraticMap.Equivalent.sigPos_eq (h : Equivalent Q Q') : sigPos Q = sigPos Q' := by
  obtain ⟨e⟩ := h
  unfold sigPos
  congr! with j
  · apply (Submodule.orderIsoMapComap e.toLinearEquiv).exists_congr
    intro V
    refine .and ?_ (IsometryEquiv.map_posDef_iff _).symm
    revert j
    rw [eq_iff_eq_cancel_right]
    exact (e.finrank_map_eq _).symm
  · exact e.toLinearEquiv.finrank_eq

lemma QuadraticMap.Equivalent.sigNeg_eq (h : Equivalent Q Q') : sigNeg Q = sigNeg Q' :=
  sigPos_eq <| match h with | ⟨e⟩ => ⟨e, by simp⟩

end LinearOrder

section Field
namespace QuadraticForm

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [Module 𝕜 M] [Module 𝕜 M'] {Q : QuadraticForm 𝕜 M}

/-- Key lemma for Sylvester's law of inertia: the sum of `sigPos Q` and the dimension of any
negative-semidefinite subspace is bounded above by the dimension of the whole space. -/
lemma sigPos_add_finrank_le_of_nonpos [FiniteDimensional 𝕜 M]
    {V : Subspace 𝕜 M} (hV : ∀ x ∈ V, Q x ≤ 0) :
    sigPos Q + Module.finrank 𝕜 V ≤ Module.finrank 𝕜 M := by
  obtain ⟨Vp, hr, hVp⟩ := (sigPos_isGreatest Q).1
  rw [← hr]
  apply Submodule.finrank_add_finrank_le_of_disjoint
  intro W hWp hWm
  rw [le_bot_iff, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx'
  have := hVp ⟨x, hWp hx⟩ (by simpa using hx')
  have := hV x (hWm hx)
  simp_all only [restrict_apply]
  grind

variable {ι : Type*} [Fintype ι] {w : ι → 𝕜} [IsStrictOrderedRing 𝕜]

private lemma posDef_spanSubset (s : Set ι) (hs : ∀ i ∈ s, 0 < w i) :
    (weightedSumSquares 𝕜 w).restrict (Pi.spanSubset 𝕜 s) |>.PosDef := by
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply, weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i ∈ s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [Pi.mem_spanSubset_iff.mp hv i hi]
  · simp only [ne_eq, Submodule.mk_eq_zero, funext_iff, not_forall, Pi.zero_apply] at hv'
    obtain ⟨i, hi⟩ := hv'
    refine ⟨i, mem_univ _, ?_⟩
    have : i ∈ s := by
      contrapose hi
      exact Pi.mem_spanSubset_iff.mp hv i hi
    exact smul_pos (hs i this) (mul_self_pos.mpr hi)

private lemma negSemidef_spanSubset (s : Set ι) (hs : ∀ i ∈ s, w i ≤ 0) :
    ∀ x ∈ Pi.spanSubset 𝕜 s, (weightedSumSquares 𝕜 w) x ≤ 0 := by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i ∈ s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [Pi.mem_spanSubset_iff.mp hx i hi, mul_zero, mul_zero]

/-- Key lemma for Sylvester's law of inertia: compute the signature of a weighted sum of squares. -/
lemma sigPos_weightedSumSquares :
    sigPos (weightedSumSquares 𝕜 w) = {i | 0 < w i}.ncard := by
  classical
  let p : Set ι := {i | 0 < w i}
  let m : Set ι := {i | w i ≤ 0}
  convert_to sigPos _ = p.ncard
  have : p.ncard + m.ncard = Nat.card ι := by
    convert Set.ncard_add_ncard_compl p
    ext
    grind
  have : p.ncard ≤ sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨Pi.spanSubset 𝕜 p, Pi.dim_spanSubset,
      posDef_spanSubset p (by grind)⟩
  suffices sigPos (weightedSumSquares 𝕜 w) + m.ncard ≤ Nat.card ι by lia
  simpa using sigPos_add_finrank_le_of_nonpos <| negSemidef_spanSubset m (fun _ hi ↦ hi)

lemma sigNeg_weightedSumSquares :
    sigNeg (weightedSumSquares 𝕜 w) = {i | w i < 0}.ncard := by
  simp only [sigNeg]
  convert sigPos_weightedSumSquares (w := -w) using 2
  · ext; simp
  · simp

private lemma sigPos_add_sigNeg_add_radical₁ :
    sigPos (weightedSumSquares 𝕜 w) + sigNeg (weightedSumSquares 𝕜 w) +
      Module.finrank 𝕜 (weightedSumSquares 𝕜 w).radical = Nat.card ι := by
  classical
  rw [radical_weightedSumSquares, sigPos_weightedSumSquares, sigNeg_weightedSumSquares,
    Pi.dim_spanSubset]
  calc {i | 0 < w i}.ncard + {i | w i < 0}.ncard + {i | w i = 0}.ncard
  _ = {i | 0 < w i}.ncard + {i | w i ≤ 0}.ncard := by
    rw [add_assoc, add_left_cancel_iff, ← Set.ncard_union_eq]
    · congr! 1
      ext
      grind
    · grind [disjoint_iff_ne]
  _ = Set.univ.ncard := by
    rw [← Set.ncard_union_eq]
    · congr! 1
      ext
      grind [le_iff_lt_or_eq]
    · grind [disjoint_iff_ne]
  _ = Nat.card ι := Set.ncard_univ _

lemma sigPos_add_sigNeg_add_radical [FiniteDimensional 𝕜 M] :
    sigPos Q + sigNeg Q + Module.finrank 𝕜 Q.radical = Module.finrank 𝕜 M := by
  have : Invertible (2 : 𝕜) := invertibleOfNonzero (NeZero.ne _)
  obtain ⟨w, e⟩ := Q.equivalent_weightedSumSquares
  rw [e.sigPos_eq, e.sigNeg_eq, e.rank_radical_eq]
  convert QuadraticForm.sigPos_add_sigNeg_add_radical₁ (w := w)
  exact Eq.symm (Nat.card_fin (Module.finrank 𝕜 M))

lemma sigPos_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigPos Q = {i | 0 < w i}.ncard := by
  rw [hQ.sigPos_eq]
  exact sigPos_weightedSumSquares

lemma sigNeg_of_equiv_weightedSumSquares (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    sigNeg Q = {i | w i < 0}.ncard := by
  rw [hQ.sigNeg_eq]
  exact sigNeg_weightedSumSquares

end QuadraticForm
