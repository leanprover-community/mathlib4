/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.SchauderBasis.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Basic Sequences in Banach Spaces

A **basic sequence** in a Banach space is a sequence that forms a Schauder basis for the closure of
its linear span. Basic sequences are a central tool in the structural theory of Banach spaces:
every infinite-dimensional Banach space contains a basic sequence,
and many constructions in the theory reduce to manipulations of basic sequences.

The key criterion for recognizing basic sequences is that all partial sums
`∑ i < m, a i · e i` are bounded by a constant `K` times the full sum
`∑ i < n, a i · e i` whenever `m ≤ n`.

## Main Definitions

* `IsBasicSequence`: A `Prop` asserting that initial partial sums of `e` are bounded by `K` times
  the full partial sum.
* `IsBasicSequence.toSchauderBasis`: Constructs a `SchauderBasis` on the algebraic span of a
  nonzero basic sequence.

## Main Results

* `IsBasicSequence.linearIndependent`: A nonzero basic sequence is linearly independent.
* `IsBasicSequence.coe_toSchauderBasis_apply`: The `n`-th basis vector of the constructed Schauder
  basis coerces to `e n` in the ambient space.
* `IsBasicSequence.enormProjBound_le`: The projection bound of the constructed basis is at most
  `ENNReal.ofReal K`.

## Implementation Notes

In the literature, a basic sequence is defined as a sequence that forms a Schauder basis for the
closure of its linear span. In this file, the `SchauderBasis` lives on the algebraic span
`Submodule.span 𝕜 (Set.range e)` rather than its topological closure. The construction proceeds by
building finite-rank partial-sum projections (`IsBasicSequence.proj`), assembling them into a
`SchauderBasis.RankOneDecomposition`, and converting that into a `SchauderBasis`. Working with the
algebraic span is easier to verify: the projection bound only needs to be checked on finite linear
combinations, so the basic sequence condition applies directly without density or extension
arguments.

## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A sequence `e` is a **basic sequence** with constant `K` if for all `m ≤ n` and all scalar
    sequences `a`, the norm of the partial sum `∑ i < m, a i • e i` is bounded by `K` times the
    norm of the longer partial sum `∑ i < n, a i • e i`. -/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) (K : ℝ) : Prop :=
  ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- `IsBasicSequence` is monotone in the constant: if `K ≤ K'` then
    `IsBasicSequence 𝕜 e K → IsBasicSequence 𝕜 e K'`. -/
theorem IsBasicSequence.mono {e : ℕ → X} {K K' : ℝ}
    (h : IsBasicSequence 𝕜 e K) (hKK' : K ≤ K') : IsBasicSequence 𝕜 e K' :=
  fun n m a hmn => (h n m a hmn).trans (mul_le_mul_of_nonneg_right hKK' (norm_nonneg _))

variable {e : ℕ → X} {K : ℝ}

/-- The basic sequence constant of a nonzero sequence is at least `1`. -/
theorem IsBasicSequence.one_le (h : IsBasicSequence 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) : 1 ≤ K := by
  have := h 1 1 (fun _ => 1) le_rfl
  simp only [Finset.range_one, one_smul, sum_singleton] at this
  exact le_of_mul_le_mul_right ((one_mul _).le.trans this) (norm_pos_iff.mpr (h_nz 0))

/-- A nonzero basic sequence is linearly independent. -/
lemma IsBasicSequence.linearIndependent (h_basic : IsBasicSequence 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
    LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  let c j := if j ∈ s then g j else 0
  let N := s.sup id + 1
  have hltN (j : ℕ) (hj : j ∈ s) : j < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have h_zero : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hltN j hj))
      (fun x _ hx ↦ by simp only [c, hx, ite_false, zero_smul])]
    exact (Finset.sum_congr rfl (fun j hj ↦ by simp [c, hj])).trans hg
  have h_part (m : ℕ) (hm : m ≤ N) : ∑ j ∈ Finset.range m, c j • e j = 0 :=
    norm_le_zero_iff.mp (by simpa [h_zero] using h_basic N m c hm)
  have hc : c i • e i = 0 := by
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j),
        h_part (i + 1) (hltN i hi), h_part i (hltN i hi).le, sub_zero]
  simpa [c, hi, h_nz i] using hc

/-- A basis representation summed over any finset containing the support equals the original
    element. -/
lemma sum_repr_eq_of_support_subset {ι : Type*} {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    (b : Module.Basis ι 𝕜 M) (x : M) {A : Finset ι} (hA : (b.repr x).support ⊆ A) :
    ∑ i ∈ A, b.repr x i • b i = x := by
  conv_rhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_subset hA fun i _ hi ↦ by simp [Finsupp.notMem_support_iff.mp hi]).symm

/-- The linear map projecting onto the first `k` coordinates in the algebraic span of a basic
    sequence, defined as `∑ i < k, (b.repr x i) • b i` where `b` is the `Module.Basis.span`
    basis. -/
noncomputable def IsBasicSequence.linearProj (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) (k : ℕ) :
    Submodule.span 𝕜 (Set.range e) →ₗ[𝕜] Submodule.span 𝕜 (Set.range e) :=
  let b_S := Module.Basis.span (h_basic.linearIndependent h_nz)
  ∑ i ∈ Finset.range k, ((Finsupp.lapply i).comp b_S.repr.toLinearMap).smulRight (b_S i)

/-- The basic sequence condition implies that `IsBasicSequence.linearProj` is bounded by `K`
    times the norm. -/
lemma IsBasicSequence.norm_linearProj_le (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) (k : ℕ) (x : Submodule.span 𝕜 (Set.range e)) :
    ‖h_basic.linearProj h_nz k x‖ ≤ K * ‖x‖ := by
  have h_indep := h_basic.linearIndependent h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS (n : ℕ) : (b_S n : X) = e n :=
    congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have h_sum (y : S) {N : ℕ} (hN : (b_S.repr y).support.sup id < N) :
      ∑ i ∈ Finset.range N, b_S.repr y i • b_S i = y :=
    sum_repr_eq_of_support_subset b_S y fun i hi ↦
      Finset.mem_range.2 ((Finset.le_sup (f := id) hi).trans_lt hN)
  have coe_sum (A : Finset ℕ) (c : ℕ → 𝕜) :
      (↑(∑ i ∈ A, c i • b_S i) : X) = ∑ i ∈ A, c i • e i := by
    simp [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, hbS]
  let a := b_S.repr x
  let N := max k (a.support.sup id + 1)
  have hN := (Nat.lt_succ_self _).trans_le (le_max_right k (a.support.sup id + 1))
  calc ‖h_basic.linearProj h_nz k x‖
    _ = ‖∑ i ∈ Finset.range k, a i • e i‖ := by rw [← norm_coe]; simp [linearProj, a]; rfl
    _ ≤ K * ‖∑ i ∈ Finset.range N, a i • e i‖ := h_basic N k a (le_max_left _ _)
    _ = K * ‖x‖ := by rw [← norm_coe, ← coe_sum, congrArg Subtype.val (h_sum x hN)]

/-- The continuous linear projection onto the first `k` coordinates in the algebraic span of a
    basic sequence, with operator norm at most `K`. -/
noncomputable def IsBasicSequence.proj (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) (k : ℕ) :
    Submodule.span 𝕜 (Set.range e) →L[𝕜] Submodule.span 𝕜 (Set.range e) :=
  (h_basic.linearProj h_nz k).mkContinuous K (h_basic.norm_linearProj_le h_nz k)

/-- The operator norm of the `k`-th partial sum projection is at most `K`. -/
lemma IsBasicSequence.opNorm_proj_le (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) (k : ℕ) :
    (h_basic.proj h_nz k).opNorm ≤ K := by
  have hK : 0 ≤ K := zero_le_one.trans (h_basic.one_le h_nz)
  exact ContinuousLinearMap.opNorm_le_bound _ hK (h_basic.norm_linearProj_le h_nz k)

/-- The rank-one decomposition data for the algebraic span of a basic sequence. The projections
    are `IsBasicSequence.proj` and the basis vectors come from `Module.Basis.span`.
    Use `IsBasicSequence.toSchauderBasis` for the resulting `SchauderBasis`. -/
noncomputable def IsBasicSequence.rankOneDecomposition (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) :
    SchauderBasis.RankOneDecomposition 𝕜 (Submodule.span 𝕜 (Set.range e)) := by
  have h_indep := h_basic.linearIndependent h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS (n : ℕ) : (b_S n : X) = e n :=
    congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have h_sum (x : S) {N : ℕ} (hN : (b_S.repr x).support.sup id < N) :
      ∑ i ∈ Finset.range N, b_S.repr x i • b_S i = x :=
    sum_repr_eq_of_support_subset b_S x fun i hi ↦
      Finset.mem_range.2 ((Finset.le_sup (f := id) hi).trans_lt hN)
  let P := h_basic.proj h_nz
  have hP (k : ℕ) (x : S) :
      P k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    change h_basic.linearProj h_nz k x = _
    exact Subtype.ext <| by simp [linearProj, AddSubmonoidClass.coe_finset_sum,
      SetLike.val_smul, hbS]; rfl
  have h_proj_basis (i n : ℕ) (hi : i < n) : P n (b_S i) = b_S i := by
    rw [hP, h_sum _ (by simp [b_S.repr_self, Finsupp.support_single_ne_zero, hi])]
  exact {
    P := P,
    e := b_S,
    proj_zero := by
      ext x
      change (P 0 x : X) = (0 : S)
      simp [hP]
    finrank_range := fun n ↦ by
      have h_range : (P n).toLinearMap.range =
          Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ b_S i)) := by
        apply le_antisymm
        · rintro _ ⟨_, rfl⟩
          rw [ContinuousLinearMap.coe_coe, hP]
          exact Submodule.sum_mem _ fun i hi ↦
            Submodule.smul_mem _ _
              (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact ⟨b_S i, h_proj_basis i n i.isLt⟩
      rw [h_range, finrank_span_eq_card]
      · exact Fintype.card_fin n
      · exact b_S.linearIndependent.comp _ Fin.val_injective
    proj_comp := fun n m y ↦ by
      change P n (P m y) = P (min n m) y
      simp only [hP, map_sum, map_smul, b_S.repr_self,
        Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
        ite_smul, zero_smul, ← Finset.sum_filter]
      congr
      grind
    proj_tendsto := fun x ↦ (Filter.tendsto_congr fun n ↦ hP n x).mpr
      (tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support.sup id + 1)
        fun n hn ↦ h_sum x ((Nat.lt_succ_self _).trans_le hn))
    e_mem_range := fun n ↦ ⟨b_S n, by
      change P (n + 1) (b_S n) - P n (b_S n) = b_S n
      simp [hP, Finset.sum_range_succ]⟩
    e_ne_zero := fun n h ↦ h_nz n (by simpa [hbS] using congrArg Subtype.val h) }

/-- A nonzero basic sequence with constant `K` forms a Schauder basis for its algebraic span
    `Submodule.span 𝕜 (Set.range e)`. The `n`-th basis vector coerces to `e n`
    (see `IsBasicSequence.coe_toSchauderBasis_apply`) and the projection bound is at most `K`
    (see `IsBasicSequence.enormProjBound_le`). -/
noncomputable def IsBasicSequence.toSchauderBasis (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) :
    SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range e)) :=
  (h_basic.rankOneDecomposition h_nz).basis

/-- The `n`-th basis vector of the Schauder basis constructed from a basic sequence coerces to
    `e n` in the ambient space. -/
@[simp]
lemma IsBasicSequence.coe_toSchauderBasis_apply (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) (n : ℕ) :
    (h_basic.toSchauderBasis h_nz n : X) = e n :=
  congrArg Subtype.val (Module.Basis.span_apply (h_basic.linearIndependent h_nz) n)

/-- The projection bound (`enormProjBound`) of the Schauder basis constructed from a basic
    sequence with constant `K` is at most `ENNReal.ofReal K`. -/
lemma IsBasicSequence.enormProjBound_le (h_basic : IsBasicSequence 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) :
    (h_basic.toSchauderBasis h_nz).enormProjBound ≤ ENNReal.ofReal K := by
  have hK : 0 ≤ K := zero_le_one.trans (h_basic.one_le h_nz)
  apply iSup_le
  intro n
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm]
  have h_proj : (h_basic.toSchauderBasis h_nz).proj n = h_basic.proj h_nz n :=
    congrFun (SchauderBasis.RankOneDecomposition.basis_proj
      (h_basic.rankOneDecomposition h_nz)) n
  rw [h_proj]
  exact h_basic.opNorm_proj_le h_nz n

end
