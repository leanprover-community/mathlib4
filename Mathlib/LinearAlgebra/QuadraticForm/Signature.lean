/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Signature of a quadratic form
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

variable {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] [Module 𝕜 M']
  {Q : QuadraticForm 𝕜 M}

/-- Key lemma for Sylvester's law of inertia: the sum of `sigPos Q` and the dimension of any
negative-semidefinite subspace is bounded above by the dimension of the whole space. -/
lemma sigPos_add_finrank_le_of_nonpos [LinearOrder 𝕜] [FiniteDimensional 𝕜 M]
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

variable {ι : Type*} [Fintype ι] {w : ι → 𝕜} [DecidableEq 𝕜]

variable (𝕜) in
private abbrev spanOfSet (s : Finset ι) : Submodule 𝕜 (ι → 𝕜) :=
  .span 𝕜 (s.image <| Pi.basisFun 𝕜 ι) -- todo: reimplement using `Module.Basis.mem_span_image`?

open Submodule in
private lemma mem_spanOfSet_iff {s : Finset ι} {v : ι → 𝕜} :
    v ∈ spanOfSet 𝕜 s ↔ ∀ i ∉ s, v i = 0 := by
  classical
  constructor
  · rw [mem_span_finset']
    rintro ⟨f, rfl⟩ i hi
    rw [Finset.sum_apply]
    refine sum_eq_zero fun ⟨x, hx⟩ _ ↦ ?_
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    simp [show i ≠ j by grind]
  · intro hv
    suffices v = ∑ i ∈ s, v i • Pi.basisFun 𝕜 ι i by
      rw [this]
      refine Submodule.sum_mem _ (fun j hj ↦ smul_mem _ (v j) ?_)
      exact mem_span_of_mem <| Finset.mem_coe.2 <| Finset.mem_image_of_mem _ hj
    ext j
    by_cases h : j ∈ s
    · simp [Pi.single_apply, if_pos h]
    · simp [Pi.single_apply, hv j h]

private lemma zero_spanOfSet (s : Finset ι)
    (v) (hv : v ∈ spanOfSet 𝕜 s) (i) (hi : i ∉ s) : v i = 0 :=
  (mem_spanOfSet_iff.mp hv) i hi

private lemma dim_spanOfSet (s : Finset ι) :
    Module.finrank 𝕜 (spanOfSet 𝕜 s) = #s := by
  classical
  rw [finrank_span_finset_eq_card, card_image_of_injective]
  · intro x y hxy
    simpa [Pi.single_apply] using _root_.congr_fun hxy x -- missing `protected`?
  · simpa using
      (Pi.linearIndependent_single_one _ _).linearIndepOn.mono (by tauto) |>.id_image

private lemma QuadraticForm.radical_sumSq_eq [NeZero (2 : 𝕜)] :
    radical (weightedSumSquares 𝕜 w) = spanOfSet 𝕜 {i | w i = 0} := by
  classical
  ext v
  simp only [mem_radical_iff', weightedSumSquares_apply, ← pow_two, smul_eq_mul, Pi.add_apply,
    add_sq, mul_add, sum_add_distrib, add_eq_right, mem_spanOfSet_iff, mem_filter, mem_univ,
    true_and]
  constructor
  · rintro ⟨hv, hvv'⟩ i
    simp only [hv, zero_add] at hvv'
    specialize hvv' (Pi.single i 1)
    simp_all [Pi.single_apply, NeZero.ne, or_iff_not_imp_left]
  · refine fun h ↦ ⟨?_, fun v ↦ ?_⟩ <;> [skip ; simp only [← sum_add_distrib]] <;>
    · apply sum_eq_zero
      grind [mul_eq_zero]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

private lemma posDef_spanOfSet (s : Finset ι) (hs : ∀ i ∈ s, 0 < w i) :
    (weightedSumSquares 𝕜 w).restrict (spanOfSet 𝕜 s) |>.PosDef := by
  intro ⟨v, hv⟩ hv'
  rw [restrict_apply, weightedSumSquares_apply]
  apply sum_pos'
  · intro i _
    by_cases hi : i ∈ s
    · exact smul_nonneg (hs i hi).le (mul_self_nonneg _)
    · simp [zero_spanOfSet s v hv i hi]
  · simp only [ne_eq, Submodule.mk_eq_zero, funext_iff, not_forall, Pi.zero_apply] at hv'
    obtain ⟨i, hi⟩ := hv'
    refine ⟨i, mem_univ _, ?_⟩
    have : i ∈ s := by
      contrapose hi
      exact zero_spanOfSet s v hv i hi
    exact smul_pos (hs i this) (mul_self_pos.mpr hi)

private lemma negSemidef_spanOfSet (s : Finset ι) (hs : ∀ i ∈ s, w i ≤ 0) :
    ∀ x ∈ spanOfSet 𝕜 s, (weightedSumSquares 𝕜 w) x ≤ 0 := by
  intro x hx
  simp only [weightedSumSquares_apply, smul_eq_mul]
  apply sum_nonpos
  intro i _
  by_cases hi : i ∈ s
  · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi) (mul_self_nonneg _)
  · rw [zero_spanOfSet s x hx i hi, mul_zero, mul_zero]

omit [DecidableEq 𝕜]

/-- Key lemma for Sylvester's law of inertia: compute the signature of a weighted sum of squares. -/
lemma QuadraticForm.sigPos_sumSq_eq :
    sigPos (weightedSumSquares 𝕜 w) = #{i | 0 < w i} := by
  classical
  let p : Finset ι := {i | 0 < w i}
  let m : Finset ι := {i | w i ≤ 0}
  convert_to sigPos _ = #p
  have : #p + #m = Fintype.card ι := by
    convert card_add_card_compl p
    grind [mem_compl]
  have : #p ≤ sigPos (weightedSumSquares 𝕜 w) :=
    (sigPos_isGreatest _).2 ⟨spanOfSet 𝕜 p, dim_spanOfSet _, posDef_spanOfSet p (by grind)⟩
  suffices sigPos (weightedSumSquares 𝕜 w) + #m ≤ Fintype.card ι by lia
  have : ∀ x ∈ spanOfSet 𝕜 m, (weightedSumSquares 𝕜 w) x ≤ 0 := negSemidef_spanOfSet m (by aesop)
  convert sigPos_add_finrank_le_of_nonpos this
  · exact (dim_spanOfSet m).symm
  · simp

lemma QuadraticForm.sigNeg_sumSq_eq :
    sigNeg (weightedSumSquares 𝕜 w) = #{i | w i < 0} := by
  simp only [sigNeg]
  convert sigPos_sumSq_eq (w := -w) using 2
  · ext; simp
  · simp

lemma QuadraticForm.sigPos_add_sigNeg_add_radical :
    sigPos (weightedSumSquares 𝕜 w) + sigNeg (weightedSumSquares 𝕜 w) +
      Module.finrank 𝕜 (weightedSumSquares 𝕜 w).radical = Fintype.card ι := by
  classical
  rw [radical_sumSq_eq, sigPos_sumSq_eq, sigNeg_sumSq_eq, dim_spanOfSet]
  calc #{i | 0 < w i} + #{i | w i < 0} + #{i | w i = 0}
  _ = #{i | 0 < w i} + #{i | w i ≤ 0} := by
    rw [add_assoc, add_left_cancel_iff, ← card_union_of_disjoint]
    · congr! 1
      grind
    · grind [disjoint_iff_ne]
  _ = #univ := by
    rw [← card_union_of_disjoint]
    · congr! 1
      grind [le_iff_lt_or_eq]
    · grind [disjoint_iff_ne]
  _ = Fintype.card ι := card_univ
