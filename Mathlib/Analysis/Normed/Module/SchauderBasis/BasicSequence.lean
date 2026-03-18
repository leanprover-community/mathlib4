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
every infinite-dimensional Banach space contains a basic sequence (the Bessaga–Pełczyński theorem),
and many constructions in the theory reduce to manipulations of basic sequences.

The key criterion for recognizing basic sequences is the **Grünblum condition**: a sequence `(eₙ)`
is basic if and only if all partial sums `∑_{i<m} aᵢeᵢ` are bounded by a constant `K` times the
full sum `∑_{i<n} aᵢeᵢ` whenever `m ≤ n`. The analogous condition for unconditional basic
sequences, where subsets replace initial segments, is called the **Nikolskii condition**.

## Main Definitions

* `BasicSequence`: A bundled ℕ-indexed sequence that forms a Schauder basis for its closed span.
* `UnconditionalBasicSequence`: A bundled sequence forming an unconditional Schauder basis.
* `IsBasicSequence`: Predicate for a sequence being a basic sequence.
* `IsUnconditionalBasicSequence`: Predicate for an unconditional basic sequence.
* `SatisfiesGrunblumCondition`: The Grünblum condition with constant `K`.
* `SatisfiesNikolskiiCondition`: The Nikolskii condition with constant `K`.

## Main Results

* `isBasicSequence_of_Grunblum_with_bound`: A nonzero sequence satisfying the Grünblum condition
  is a basic sequence, with an explicit bound on the basis constant.
* `isUnconditionalBasicSequence_of_Nikolskii`: The analogous result for unconditional basic
  sequences under the Nikolskii condition.
* `functional_vanishes_on_set_of_bound`: A functional with a lower bound on a scaling-closed set
  containing 0 must vanish on that set.
* `exists_functional_neg_one_and_vanishes_on_closed_submodule`: Hahn-Banach separation for
  a point outside a closed submodule.

## References

* [F. Albiac, N.J. Kalton, *Topics in Banach Space Theory*][albiac2016]
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A **basic sequence** in a normed space `X` over `𝕜` is an ℕ-indexed sequence that forms a
    Schauder basis for its closed linear span, with finite projection bound. -/
structure BasicSequence (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- The underlying sequence. -/
  toFun : ℕ → X
  /-- The Schauder basis for the closed span of the sequence. -/
  basis : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range toFun))
  /-- The basis vectors coincide with the sequence elements. -/
  basis_eq : ∀ i, (basis i : X) = toFun i
  /-- The basis constant is finite. -/
  basisConstant_lt_top : basis.enormProjBound < ⊤

instance : CoeFun (BasicSequence 𝕜 X) (fun _ ↦ ℕ → X) where
  coe b := b.toFun

/-- A sequence satisfies the **Grünblum Condition** with constant `K` if partial sums
    over initial segments are bounded by `K` times the full sum. -/
def SatisfiesGrunblumCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) (K : ℝ) : Prop :=
  ∀ (n m : ℕ) (a : ℕ → 𝕜), m ≤ n →
    ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖

/-- The Grünblum condition is monotone in the constant. -/
theorem SatisfiesGrunblumCondition.mono {e : ℕ → X} {K K' : ℝ}
    (h : SatisfiesGrunblumCondition 𝕜 e K) (hKK' : K ≤ K') :
    SatisfiesGrunblumCondition 𝕜 e K' :=
  fun n m a hmn => (h n m a hmn).trans (mul_le_mul_of_nonneg_right hKK' (norm_nonneg _))

namespace BasicSequence

/-- A sequence `e` is a basic sequence if there exists a `BasicSequence` structure
    whose underlying sequence is equal to `e` and whose projection bound is finite. -/
def IsBasicSequence (𝕜 : Type*) {X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) : Prop :=
  ∃ b : BasicSequence 𝕜 X, ⇑b = e

/-- A `BasicSequence` satisfies the `IsBasicSequence` predicate. -/
theorem isBasicSequence (b : BasicSequence 𝕜 X) : IsBasicSequence 𝕜 b := ⟨b, rfl⟩

/-- Extract a `BasicSequence` from a proof of `IsBasicSequence`. -/
noncomputable def IsBasicSequence.toBasicSequence {e : ℕ → X}
    (h : IsBasicSequence 𝕜 e) : BasicSequence 𝕜 X := h.choose

@[simp] theorem IsBasicSequence.coe_toBasicSequence {e : ℕ → X}
    (h : IsBasicSequence 𝕜 e) : ⇑h.toBasicSequence = e := h.choose_spec

variable (bs : BasicSequence 𝕜 X)

/-- The **Basis Constant** of a basic sequence. -/
def basicSequenceConstant : ℝ := bs.basis.enormProjBound.toReal

/-- A basic sequence with finite projection bound satisfies the Grünblum condition. -/
theorem basicSequence_satisfiesGrunblum :
    SatisfiesGrunblumCondition 𝕜 bs bs.basicSequenceConstant := by
  have hK_lt_top : bs.basis.enormProjBound ≠ ⊤ := bs.basisConstant_lt_top.ne
  refine fun n m a hmn => ?_
  let Y := Submodule.span 𝕜 (Set.range bs.toFun)
  have hsum_mem (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs i ∈ Y :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have h_proj_bound : ‖bs.basis.proj m‖ ≤ bs.basicSequenceConstant := by
    have h := bs.basis.norm_proj_le_enormProjBound m
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h
  let sum_n : Y := ⟨∑ i ∈ Finset.range n, a i • bs i, hsum_mem n⟩
  let sum_m : Y := ⟨∑ i ∈ Finset.range m, a i • bs i, hsum_mem m⟩
  have h_basis_eq : ∀ i, (bs.basis i : X) = bs i := bs.basis_eq
  have h_sum_n_basis : sum_n = ∑ j ∈ Finset.range n, a j • bs.basis j := by
    apply Subtype.ext
    simp only [sum_n, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  have h_proj_eq : bs.basis.proj m sum_n = sum_m := by
    rw [h_sum_n_basis, SchauderBasis.proj_sum_range bs.basis m n a hmn]
    apply Subtype.ext; simp only [sum_m, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  calc ‖∑ i ∈ Finset.range m, a i • bs i‖
    _ = ‖sum_m‖ := (norm_coe sum_m).symm
    _ = ‖bs.basis.proj m sum_n‖ := by rw [h_proj_eq]
    _ ≤ ‖bs.basis.proj m‖ * ‖sum_n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ bs.basicSequenceConstant * ‖∑ i ∈ Finset.range n, a i • bs i‖ :=
       (mul_le_mul_of_nonneg_right h_proj_bound (norm_nonneg _)).trans_eq
         (congr_arg _ (norm_coe sum_n))

/-- The Grünblum bound transfers through a norm-preserving map: if `b` is a basic sequence
    in `Y` and `J : X →L[𝕜] Y` satisfies `‖J y‖ = ‖y‖` with `J (x n) = b n`, then `x`
    satisfies the same Grünblum bound as `b`. -/
theorem Grunblum_bound_transfer {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (b : BasicSequence 𝕜 Y) (x : ℕ → X) (J : X →L[𝕜] Y)
    (hJ_iso : ∀ y, ‖J y‖ = ‖y‖) (hx_J : ∀ n, J (x n) = b n)
    (n m : ℕ) (a : ℕ → 𝕜) (hmn : m ≤ n) :
    ‖∑ i ∈ Finset.range m, a i • x i‖ ≤
      b.basicSequenceConstant * ‖∑ i ∈ Finset.range n, a i • x i‖ := by
  have h_sum_eq : ∀ k, J (∑ i ∈ Finset.range k, a i • x i) =
      ∑ i ∈ Finset.range k, a i • b i := by
    intro k; simp only [map_sum, ContinuousLinearMap.map_smul, hx_J]
  rw [← hJ_iso, h_sum_eq]
  exact (basicSequence_satisfiesGrunblum b n m a hmn).trans_eq (by rw [← h_sum_eq, hJ_iso])

/-- Elements of a basic sequence are nonzero. -/
lemma ne_zero (b : BasicSequence 𝕜 X) (n : ℕ) : b n ≠ 0 := fun h =>
  b.basis.linearIndependent.ne_zero n (Subtype.ext ((b.basis_eq n).trans h))

/-- The underlying function of a basic sequence is injective. -/
lemma injective (b : BasicSequence 𝕜 X) : Function.Injective ⇑b := by
  intro i j hij
  exact b.basis.linearIndependent.injective
    (Subtype.ext ((b.basis_eq i).trans (hij.trans (b.basis_eq j).symm)))

/-- The Grünblum constant must be at least 1 for any nonzero sequence. -/
theorem Grunblum_const_ge_1 {e : ℕ → X} {K : ℝ}
    (h : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) : 1 ≤ K := by
  have h0 := h 1 1 (fun _ => 1) le_rfl
  simp only [Finset.range_one, one_smul, sum_singleton] at h0
  exact le_of_mul_le_mul_right ((one_mul _).le.trans h0) (norm_pos_iff.mpr (h_nz 0))

/-- The basis constant of a basic sequence is at least 1. -/
theorem basicSequenceConstant_ge_one : 1 ≤ bs.basicSequenceConstant :=
  Grunblum_const_ge_1 (basicSequence_satisfiesGrunblum bs) bs.ne_zero

/-- A nonzero sequence satisfying the Grünblum condition is linearly independent. -/
lemma linearIndependent_of_Grunblum {e : ℕ → X} {K : ℝ}
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intros s g hg_sum i hi_s
  let c := fun j ↦ if j ∈ s then g j else 0
  let N := s.sup id + 1
  have h_bound : ∀ j ∈ s, j < N := fun j hj ↦ Nat.lt_succ_of_le (Finset.le_sup hj (f := id))
  have h_total : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (h_bound j hj))
      (fun x _ hj ↦ by simp [c, hj])]
    convert hg_sum using 1
    exact Finset.sum_congr rfl (fun j hj ↦ by simp [c, hj])
  have h_partial : ∀ m ≤ N, ∑ j ∈ Finset.range m, c j • e j = 0 := fun m hm ↦
    norm_le_zero_iff.1 <| by simpa [h_total] using h_grunblum N m c hm
  have h_term : c i • e i = 0 := by
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j),
        h_partial (i + 1) (h_bound i hi_s),
        h_partial i (le_of_lt (h_bound i hi_s)), sub_zero]
  simpa [c, hi_s, h_nz i] using h_term

/-- A version of `isBasicSequence_of_Grunblum` that also provides an explicit bound
    on the basis constant. If a sequence satisfies the Grünblum condition with constant K,
    the resulting basic sequence has basis constant at most K. -/
theorem isBasicSequence_of_Grunblum_with_bound {e : ℕ → X} {K : ℝ}
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
    ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ b.basicSequenceConstant ≤ K := by
  have h_indep := linearIndependent_of_Grunblum h_grunblum h_nz
  have hK : 0 ≤ K := zero_le_one.trans (Grunblum_const_ge_1 h_grunblum h_nz)
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  let e_Y : ℕ → S := b_S
  have hbS : ∀ n, (b_S n : X) = e n := Module.Basis.span_apply h_indep
  let P_span (k : ℕ) : S →ₗ[𝕜] S := b_S.constr 𝕜 (fun i => if i < k then b_S i else 0)
  have h_P_span_apply (k : ℕ) (x : S) :
      P_span k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    rw [Module.Basis.constr_apply, Finsupp.sum]
    refine Finset.sum_congr_of_eq_on_inter ?_ ?_ ?_ <;> intro i h1 h2
    · rw [if_neg (by simpa using h2), smul_zero]
    · rw [Finsupp.notMem_support_iff.mp h2, zero_smul]
    · rw [if_pos (by simpa using h2)]
  have h_P_span_bound (k : ℕ) (x : S) : ‖P_span k x‖ ≤ K * ‖x‖ := by
    let a := b_S.repr x
    let N := max k (a.support.sup id + 1)
    have hk_le_N : k ≤ N := le_max_left _ _
    have hx : (x : X) = ∑ i ∈ Finset.range N, (b_S.repr x) i • b_S i := by
      nth_rw 1 [← b_S.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply]
      rw [← h_P_span_apply N x]
      dsimp only [P_span]
      rw [b_S.constr_apply, Finsupp.sum_congr]
      intro i hi
      rw [if_pos]
      exact (Finset.le_sup hi (f := id)).trans_lt (Nat.lt_succ_self _)
        |>.trans_le (le_max_right _ _)
    rw [← norm_coe, ← norm_coe, hx, h_P_span_apply]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
    exact h_grunblum N k (b_S.repr x) hk_le_N
  let P (k : ℕ) : S →L[𝕜] S := LinearMap.mkContinuous (P_span k) K (h_P_span_bound k)
  have h0 : P 0 = 0 := by
    ext x; simp only [P, ContinuousLinearMap.zero_apply, LinearMap.mkContinuous_apply,
      h_P_span_apply, Finset.range_zero, Finset.sum_empty]
  have hdim (n : ℕ) : Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n := by
    let W := Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ b_S i))
    have h_range : LinearMap.range (P n).toLinearMap = W := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        simp only [ContinuousLinearMap.coe_coe, P, LinearMap.mkContinuous_apply]
        rw [h_P_span_apply]
        refine Submodule.sum_mem _ (fun i hi ↦ ?_)
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
      · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; use b_S i
        simp only [ContinuousLinearMap.coe_coe]; dsimp only [P]
        simp only [LinearMap.mkContinuous_apply]; dsimp only [P_span]
        rw [b_S.constr_basis, if_pos i.isLt]
    rw [h_range, finrank_span_eq_card]
    · exact Fintype.card_fin n
    · exact b_S.linearIndependent.comp (fun i : Fin n => i.val) Fin.val_injective
  have hcomp (n m : ℕ) (y : S) : P n (P m y) = P (min n m) y := by
    simp only [P, LinearMap.mkContinuous_apply]
    conv_lhs => rw [h_P_span_apply m y, h_P_span_apply]
    rw [h_P_span_apply]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp_rw [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
             smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
             ite_smul, zero_smul, ← Finset.sum_filter]
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have h_bound_P : ∀ n, ‖P n‖ ≤ K := fun n ↦
    ContinuousLinearMap.opNorm_le_bound _ hK (h_P_span_bound n)
  have hlim (x : S) : Filter.Tendsto (fun n ↦ P n x) Filter.atTop (nhds x) := by
    rw [Metric.tendsto_atTop]; intro ε hε
    use (b_S.repr x).support.sup id + 1; intro n hn
    simp only [P, LinearMap.mkContinuous_apply, dist_eq_norm]
    have h_eq : P_span n x = x := by
      rw [h_P_span_apply]
      conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply]
      exact (Finset.sum_subset (fun i hi => Finset.mem_range.mpr
        ((Finset.le_sup hi (f := id)).trans_lt (Nat.lt_succ_self _) |>.trans_le hn))
        (fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi])).symm
    rw [h_eq, sub_self, norm_zero]; exact hε
  have hbS_eq : ∀ n, b_S n = ⟨e n, subset_span (mem_range_self n)⟩ := fun n ↦
    Subtype.ext (hbS n)
  have he_in_range : ∀ n, ⟨e n, subset_span (mem_range_self n)⟩ ∈
      LinearMap.range (SchauderBasis.succSub P n).toLinearMap := fun n ↦ by
    rw [← hbS_eq, LinearMap.mem_range]
    use b_S n
    simp only [SchauderBasis.succSub, ContinuousLinearMap.coe_sub, P,
               LinearMap.mkContinuous_coe, LinearMap.sub_apply]
    rw [h_P_span_apply, h_P_span_apply, Finset.sum_range_succ, add_sub_cancel_left]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  have he_ne : ∀ n, (⟨e n, subset_span (mem_range_self n)⟩ : S) ≠ 0 := fun n h ↦
    h_nz n (by simpa using congrArg Subtype.val h)
  let D : SchauderBasis.ProjectionData 𝕜 S := {
    P := P
    e := e_Y
    projZero := h0
    finrankRange := hdim
    hcomp := hcomp
    hlim := hlim
    heInRange := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_in_range n
    heNe := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_ne n
  }
  let b_basis := D.basis
  have h_lt_top : b_basis.enormProjBound < ⊤ :=
    b_basis.enormProjBound_lt_top_of_bound (fun n ↦ by
      change ‖D.basis.proj n‖ ≤ K
      rw [SchauderBasis.ProjectionData.basis_proj D]; exact h_bound_P n)
  let seq : BasicSequence 𝕜 X := {
    toFun := e
    basis := b_basis
    basis_eq := fun n => by
      rw [SchauderBasis.ProjectionData.basis_coe D]; exact hbS n
    basisConstant_lt_top := h_lt_top
  }
  refine ⟨seq, rfl, ?_⟩
  dsimp only [basicSequenceConstant]
  have h_bound_ennreal : b_basis.enormProjBound ≤ ENNReal.ofReal K :=
    iSup_le fun n => by
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm,
        SchauderBasis.ProjectionData.basis_proj D]
      exact h_bound_P n
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound_ennreal).trans_eq
    (ENNReal.toReal_ofReal hK)

/-- Convenience wrapper: the Grünblum criterion as a predicate. -/
theorem isBasicSequence_of_Grunblum {e : ℕ → X} {K : ℝ} (h_nz : ∀ n, e n ≠ 0)
    (h : SatisfiesGrunblumCondition 𝕜 e K) : IsBasicSequence 𝕜 e := by
  obtain ⟨b, hb_eq, _⟩ := isBasicSequence_of_Grunblum_with_bound h h_nz
  exact ⟨b, hb_eq⟩

/-- The tail of a basic sequence (starting from index N) is also a basic sequence. -/
theorem tail_basic_sequence (bs : BasicSequence 𝕜 X) (N : ℕ) :
    IsBasicSequence 𝕜 (fun n => bs (n + N)) := by
  have hK_bound := basicSequence_satisfiesGrunblum bs
  have h_nz : ∀ n, bs (n + N) ≠ 0 := fun n => bs.ne_zero (n + N)
  refine isBasicSequence_of_Grunblum (K := bs.basicSequenceConstant) h_nz ?_
  intro n m a hnm
  let a' : ℕ → 𝕜 := fun i => if N ≤ i then a (i - N) else 0
  have h_sum_eq (k : ℕ) : ∑ i ∈ Finset.range k, a i • bs (i + N) =
      ∑ i ∈ Finset.range (k + N), a' i • bs i := by
    rw [← Finset.sum_range_add_sum_Ico (f := fun i => a' i • bs i) (Nat.le_add_left N k),
      show ∑ i ∈ Finset.range N, a' i • bs i = 0 from
        Finset.sum_eq_zero fun i hi => by
          simp [a', not_le.mpr (Finset.mem_range.mp hi)],
      zero_add, show Finset.Ico N (k + N) = (Finset.range k).map
        ⟨(· + N), fun _ _ h => Nat.add_right_cancel h⟩ from by
          ext j; simp only [Finset.mem_map, Finset.mem_range, Finset.mem_Ico,
            Function.Embedding.coeFn_mk]
          exact ⟨fun ⟨hN, hk⟩ => ⟨j - N, by omega, by omega⟩,
            fun ⟨i, hi, hij⟩ => by omega⟩,
      Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by
      simp [Function.Embedding.coeFn_mk, a']
  rw [h_sum_eq m, h_sum_eq n]
  exact hK_bound (n + N) (m + N) a' (by omega)

/-- Pull back a basic sequence through a norm-preserving linear map.
    If every element of `b` in `Y` lies in `J '' S` for some set `S ⊆ X`
    and norm-preserving `J`, then `S` contains a basic sequence with
    the same basis constant bound. -/
lemma pullback
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (b : BasicSequence 𝕜 Y) {S : Set X} (J : X →L[𝕜] Y)
    (hJ_iso : ∀ y : X, ‖J y‖ = ‖y‖) (hb_mem : ∀ n, b n ∈ J '' S) :
    ∃ (b' : BasicSequence 𝕜 X), (∀ n, b' n ∈ S) ∧
      b'.basicSequenceConstant ≤ b.basicSequenceConstant := by
  choose seq hseq_S hseq_J using hb_mem
  have h_nz : ∀ n, seq n ≠ 0 := fun n h =>
    b.ne_zero n (by rw [← hseq_J n, h, map_zero])
  have h_grunblum : SatisfiesGrunblumCondition 𝕜 seq b.basicSequenceConstant :=
    fun n m a hmn => b.Grunblum_bound_transfer seq J hJ_iso hseq_J n m a hmn
  obtain ⟨b', hb'_eq, hb'_bound⟩ := isBasicSequence_of_Grunblum_with_bound h_grunblum h_nz
  exact ⟨b', fun n => (congrFun hb'_eq n).symm ▸ hseq_S n, hb'_bound⟩

/-- Pull back through a norm-preserving linear map (predicate version). -/
lemma IsBasicSequence.pullback
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {e : ℕ → Y} (he : IsBasicSequence 𝕜 e) {S : Set X} (J : X →L[𝕜] Y)
    (hJ_iso : ∀ y : X, ‖J y‖ = ‖y‖) (he_mem : ∀ n, e n ∈ J '' S) :
    ∃ (seq : ℕ → X), (∀ n, seq n ∈ S) ∧ IsBasicSequence 𝕜 seq := by
  obtain ⟨b, hb_eq⟩ := he
  obtain ⟨b', hb'_S, _⟩ := b.pullback J hJ_iso (fun n => hb_eq ▸ he_mem n)
  exact ⟨⇑b', hb'_S, ⟨b', rfl⟩⟩

end BasicSequence

/-- An **unconditional basic sequence** indexed by `β` in a normed space `X` over `𝕜` is a
    sequence that forms an unconditional Schauder basis for its span, with finite projection
    bound. -/
structure UnconditionalBasicSequence (β : Type*) (𝕜 : Type*) (X : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- The underlying sequence. -/
  toFun : β → X
  /-- The unconditional Schauder basis for the closed span of the sequence. -/
  basis : UnconditionalSchauderBasis β 𝕜 (Submodule.span 𝕜 (Set.range toFun))
  /-- The basis vectors coincide with the sequence elements. -/
  basis_eq : ∀ i, (basis i : X) = toFun i
  /-- The basis constant is finite. -/
  basisConstant_lt_top : basis.enormProjBound < ⊤

instance {β : Type*} : CoeFun (UnconditionalBasicSequence β 𝕜 X) (fun _ ↦ β → X) where
  coe b := b.toFun

/-- A sequence satisfies the **General Grünblum Condition** with constant `K`
    if partial sums over subsets are bounded by `K` times any larger
    sum. -/
def SatisfiesNikolskiiCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {β : Type*} (e : β → X) (K : ℝ) : Prop :=
    ∀ (A B : Finset β) (a : β → 𝕜), A ⊆ B → ‖∑ i ∈ A, a i • e i‖ ≤ K * ‖∑ i ∈ B, a i • e i‖

namespace UnconditionalBasicSequence

variable (ubs : UnconditionalBasicSequence ℕ 𝕜 X)

/-- Convert an ℕ-indexed unconditional basic sequence to a (conditional) basic sequence. -/
def toBasicSequence : BasicSequence 𝕜 X := {
  toFun := ubs.toFun,
  basis := ubs.basis.toSchauderBasis,
  basis_eq := fun i => ubs.basis_eq i,
  basisConstant_lt_top :=
    lt_of_le_of_lt ubs.basis.toSchauderBasis_enormProjBound_le ubs.basisConstant_lt_top
}

/-- The coercion of `toBasicSequence` equals the original coercion. -/
@[simp] lemma coe_toBasicSequence : ⇑(ubs.toBasicSequence) = ⇑ubs := rfl

variable {β : Type*}
variable (ubs : UnconditionalBasicSequence β 𝕜 X)

/-- The **Basis Constant** of a general basic sequence. -/
def unconditionalBasicSequenceConstant : ℝ := ubs.basis.enormProjBound.toReal

/-- A sequence `e : β → X` is an unconditional basic sequence if there exists a
    `UnconditionalBasicSequence` structure whose underlying sequence equals `e`
    and whose projection bound is finite. -/
def IsUnconditionalBasicSequence (β : Type*) (𝕜 : Type*) {X : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (e : β → X) : Prop :=
  ∃ b : UnconditionalBasicSequence β 𝕜 X, b.toFun = e

/-- An ℕ-indexed unconditional basic sequence is also a basic sequence. -/
theorem IsUnconditionalBasicSequence.toIsBasicSequence {e : ℕ → X}
    (h : IsUnconditionalBasicSequence ℕ 𝕜 e) : BasicSequence.IsBasicSequence 𝕜 e := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b.toBasicSequence, rfl⟩

/-- A general basic sequence with finite projection bound satisfies the
    generalized Grünblum condition. -/
theorem unconditional_satisfiesNikolskii :
    SatisfiesNikolskiiCondition 𝕜 ubs ubs.unconditionalBasicSequenceConstant := by
  have hK_lt_top : ubs.basis.enormProjBound ≠ ⊤ := ubs.basisConstant_lt_top.ne
  refine fun A B a hAB => ?_
  let Y := Submodule.span 𝕜 (Set.range ubs.toFun)
  have hsum_mem (S : Finset β) : ∑ i ∈ S, a i • ubs i ∈ Y :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have h_proj_bound : ‖ubs.basis.proj A‖ ≤ ubs.unconditionalBasicSequenceConstant := by
    have h := ubs.basis.norm_proj_le_enormProjBound A
    rw [enorm_eq_nnnorm] at h
    rw [← ENNReal.toReal_le_toReal ENNReal.coe_ne_top hK_lt_top] at h
    simp only [ENNReal.coe_toReal, coe_nnnorm] at h
    exact h
  let sum_B : Y := ⟨∑ i ∈ B, a i • ubs i, hsum_mem B⟩
  let sum_A : Y := ⟨∑ i ∈ A, a i • ubs i, hsum_mem A⟩
  have h_basis_eq : ∀ i, (ubs.basis i : X) = ubs i := ubs.basis_eq
  have h_sum_B_basis : sum_B = ∑ j ∈ B, a j • ubs.basis j := by
    apply Subtype.ext
    simp only [sum_B, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  have h_proj_eq : ubs.basis.proj A sum_B = sum_A := by
    rw [h_sum_B_basis]
    simp_rw [map_sum, map_smul, GeneralSchauderBasis.proj_apply_basis]
    classical
    have : B.filter (· ∈ A) = A := by
      ext i; simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hAB h, h⟩⟩
    simp_rw [smul_ite, smul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero, this]
    apply Subtype.ext; simp only [sum_A, Submodule.coe_sum, Submodule.coe_smul, h_basis_eq]
  calc ‖∑ i ∈ A, a i • ubs i‖
    _ = ‖sum_A‖ := (norm_coe sum_A).symm
    _ = ‖ubs.basis.proj A sum_B‖ := by rw [h_proj_eq]
    _ ≤ ‖ubs.basis.proj A‖ * ‖sum_B‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ubs.unconditionalBasicSequenceConstant * ‖∑ i ∈ B, a i • ubs i‖ :=
       (mul_le_mul_of_nonneg_right h_proj_bound (norm_nonneg _)).trans_eq
         (congr_arg _ (norm_coe sum_B))

variable {e : β → X} {K : ℝ}

/-- A nonzero sequence satisfying the Nikolskii condition is linearly independent. -/
lemma linearIndependent_of_Nikolskii (hN : SatisfiesNikolskiiCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intro s g hsg i hi
  have h1 : ‖∑ j ∈ {i}, g j • e j‖ ≤ K * ‖∑ j ∈ s, g j • e j‖ :=
    hN {i} s g (Finset.singleton_subset_iff.mpr hi)
  simp [hsg] at h1
  exact h1.resolve_right (h_nz i)

open scoped Classical in
theorem isUnconditionalBasicSequence_of_Nikolskii {e : β → X} {K : ℝ}
    (h : SatisfiesNikolskiiCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
    IsUnconditionalBasicSequence β 𝕜 e := by
  set K' := max K 0 with hK'_def
  have hK'_nonneg : 0 ≤ K' := le_max_right _ _
  have h' : SatisfiesNikolskiiCondition 𝕜 e K' := fun A B a hAB => by
    exact (h A B a hAB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h_indep := linearIndependent_of_Nikolskii h h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS : ∀ n, (b_S n : X) = e n := Module.Basis.span_apply h_indep
  let coord_linear (j : β) : S →ₗ[𝕜] 𝕜 := (Finsupp.lapply j).comp b_S.repr.toLinearMap
  have h_coord_bound (j : β) (y : S) : ‖coord_linear j y‖ ≤ (K' / ‖e j‖) * ‖y‖ := by
    simp only [coord_linear, LinearMap.comp_apply, Finsupp.lapply_apply]
    have h_norm_ej : 0 < ‖e j‖ := norm_pos_iff.mpr (h_nz j)
    rw [div_mul_eq_mul_div, le_div_iff₀ h_norm_ej]
    calc ‖b_S.repr y j‖ * ‖e j‖
        = ‖b_S.repr y j • e j‖ := by rw [norm_smul]
      _ = ‖∑ i ∈ {j}, b_S.repr y i • e i‖ := by simp
      _ ≤ K' * ‖∑ i ∈ {j} ∪ (b_S.repr y).support, b_S.repr y i • e i‖ :=
          h' {j} ({j} ∪ (b_S.repr y).support) (b_S.repr y) Finset.subset_union_left
      _ = K' * ‖(y : X)‖ := by
          congr 1
          have h_y_eq : (y : X) = ∑ i ∈ (b_S.repr y).support, b_S.repr y i • e i := by
            conv_lhs => rw [← b_S.linearCombination_repr y, Finsupp.linearCombination_apply,
              Finsupp.sum]
            simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
          rw [h_y_eq]; congr 1
          exact (Finset.sum_subset Finset.subset_union_right
            (fun i _ hi => by rw [Finsupp.notMem_support_iff.mp hi, zero_smul])).symm
      _ = K' * ‖y‖ := by rw [norm_coe]
  let coord (j : β) : StrongDual 𝕜 S :=
    LinearMap.mkContinuous (coord_linear j) (K' / ‖e j‖) (h_coord_bound j)
  have h_ortho (i j : β) : coord i (b_S j) = (Pi.single j 1 : β → 𝕜) i := by
    simp only [coord, LinearMap.mkContinuous_apply, coord_linear, LinearMap.comp_apply,
      Finsupp.lapply_apply, Pi.single_apply]
    have : (b_S.repr : S →ₗ[𝕜] (β →₀ 𝕜)) (b_S j) = Finsupp.single j 1 := b_S.repr_self j
    rw [this, Finsupp.single_apply]; simp [eq_comm]
  have h_coord_eq (i : β) (x : S) :
      coord i x = (b_S.repr x : β →₀ 𝕜) i := by
    simp only [coord, LinearMap.mkContinuous_apply, coord_linear, LinearMap.comp_apply,
      Finsupp.lapply_apply]; rfl
  have h_sum_eq (x : S) (A : Finset β) (hA : (b_S.repr x).support ⊆ A) :
      ∑ i ∈ A, coord i x • b_S i = x := by
    simp_rw [h_coord_eq]
    conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_subset hA (fun i _ hi => by
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul])).symm
  have h_expansion (x : S) :
      HasSum (fun i ↦ coord i x • b_S i) x (SummationFilter.unconditional β) := by
    rw [HasSum, SummationFilter.unconditional_filter]
    exact tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support) (h_sum_eq x)
  let ubs_basis : UnconditionalSchauderBasis β 𝕜 S := {
    basis := b_S, coord := coord, ortho := h_ortho, expansion := h_expansion
  }
  have h_y_as_sum (y : S) :
      (y : X) = ∑ i ∈ (b_S.repr y).support, (b_S.repr y : β →₀ 𝕜) i • e i := by
    conv_lhs => rw [← b_S.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
    simp_rw [Submodule.coe_sum, Submodule.coe_smul, hbS]
  have h_proj_bound (A : Finset β) (y : S) : ‖ubs_basis.proj A y‖ ≤ K' * ‖y‖ := by
    have h_proj_coe : (ubs_basis.proj A y : X) = ∑ i ∈ A, (b_S.repr y : β →₀ 𝕜) i • e i := by
      simp only [GeneralSchauderBasis.proj_apply, Submodule.coe_sum, Submodule.coe_smul]
      apply Finset.sum_congr rfl; intro i _
      rw [h_coord_eq, hbS]
    rw [← norm_coe, h_proj_coe]
    have h_union_eq : ∑ i ∈ A ∪ (b_S.repr y).support, (b_S.repr y) i • e i = (y : X) := by
      rw [h_y_as_sum y]
      exact (Finset.sum_subset Finset.subset_union_right (fun i _ hi =>
        by rw [Finsupp.notMem_support_iff.mp hi, zero_smul])).symm
    exact (h' A _ _ Finset.subset_union_left).trans_eq (by rw [h_union_eq, norm_coe])
  have h_lt_top : ubs_basis.enormProjBound < ⊤ :=
    (iSup_le fun A => by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_le_ofReal_iff hK'_nonneg, coe_nnnorm]
      exact ContinuousLinearMap.opNorm_le_bound _ hK'_nonneg (h_proj_bound A)).trans_lt
      ENNReal.ofReal_lt_top
  exact ⟨{ toFun := e, basis := ubs_basis, basis_eq := hbS,
           basisConstant_lt_top := h_lt_top }, rfl⟩

theorem SatisfiesNikolskiiCondition.toSatisfiesGrunblumCondition {e : ℕ → X} {K : ℝ}
    (h : SatisfiesNikolskiiCondition 𝕜 e K) :
    SatisfiesGrunblumCondition 𝕜 e K :=
  fun _ _ a hmn => h _ _ a (Finset.range_subset_range.mpr hmn)

end UnconditionalBasicSequence

end -- public section

/-! ### Hahn-Banach separation lemmas -/

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

namespace BasicSequence

/-- A continuous linear functional with a lower bound on a set closed under 𝕜-scaling and
  containing 0 must vanish on that set.
  If u < re(g y) for all y ∈ S, 0 ∈ S, and c • y ∈ S for all c : 𝕜, y ∈ S, then g = 0 on S. -/
lemma functional_vanishes_on_set_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {S : Set E} (h0 : (0 : E) ∈ S) (hS_smul : ∀ (c : 𝕜) (y : E), y ∈ S → c • y ∈ S)
    (g : E →L[𝕜] 𝕜) (u : ℝ) (hg_bound : ∀ y ∈ S, u < RCLike.re (g y)) :
    ∀ y ∈ S, g y = 0 := by
  intro y hy
  by_contra h_ne
  let gy : 𝕜 := g y
  have hnorm_pos : 0 < ‖gy‖ := norm_pos_iff.mpr h_ne
  have hnorm_ne : ‖gy‖ ≠ 0 := ne_of_gt hnorm_pos
  have hu_neg : u < 0 := by simpa using hg_bound 0 h0
  let c : 𝕜 := -star gy / ‖gy‖
  have hcy_mem : c • y ∈ S := hS_smul c y hy
  have h_gc : g (c • y) = c * gy := by simp [gy, smul_eq_mul]
  have h_re : RCLike.re (c * gy) = -‖gy‖ := by
    simp only [c, neg_div, neg_mul, div_mul_eq_mul_div]
    simp only [map_neg, neg_inj]
    have h_conj : star gy * gy = (‖gy‖ : 𝕜)^2 := by
      rw [RCLike.star_def, RCLike.conj_mul, sq]
    rw [h_conj, sq]
    have h_simpl : (‖gy‖ : 𝕜) * ‖gy‖ / (‖gy‖ : 𝕜) = ‖gy‖ := by field_simp
    rw [h_simpl, RCLike.ofReal_re]
  let t : ℝ := (|u| + 1) / ‖gy‖ + 1
  have ht_pos : 0 < t := by positivity
  have htcy_mem : (t : 𝕜) • (c • y) ∈ S := hS_smul (t : 𝕜) (c • y) hcy_mem
  have h_gtc : g ((t : 𝕜) • (c • y)) = (t : 𝕜) * (c * gy) := by
    simp only [map_smul, smul_eq_mul, h_gc]
  have h_re_t : RCLike.re ((t : 𝕜) * (c * gy)) = t * (-‖gy‖) := by
    rw [RCLike.re_ofReal_mul, h_re]
  have h_bound' := hg_bound ((t : 𝕜) • (c • y)) htcy_mem
  rw [h_gtc, h_re_t] at h_bound'
  have : t * (-‖gy‖) = -(|u| + 1 + ‖gy‖) := by
    simp only [t]; field_simp
  linarith [neg_abs_le u]

/-- Given a point outside a closed submodule over 𝕜, there exists a continuous linear functional
    that equals -1 on the point and vanishes on the submodule. This follows from geometric
    Hahn-Banach separation applied to normed spaces. -/
lemma exists_functional_neg_one_and_vanishes_on_closed_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM_closed : IsClosed (M : Set E))
    (u : E) (hu : u ∉ M) :
    ∃ f : E →L[𝕜] 𝕜, f u = -1 ∧ ∀ m ∈ (M : Set E), f m = 0 := by
  haveI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hM_convex : Convex ℝ (M : Set E) := Submodule.convex (M.restrictScalars ℝ)
  obtain ⟨g, s, hg_u, hg_M⟩ := @RCLike.geometric_hahn_banach_point_closed 𝕜 E _ _ _
    (M : Set E) u _ _ _ _ _ _ hM_convex hM_closed hu
  have h0_in_M : (0 : E) ∈ M := M.zero_mem
  have hs_neg : s < 0 := by simpa using hg_M 0 h0_in_M
  have hg_vanish : ∀ m ∈ (M : Set E), g m = 0 :=
    functional_vanishes_on_set_of_bound h0_in_M (fun c y hy => M.smul_mem c hy) g s hg_M
  have hg_u_ne : g u ≠ 0 := by
    intro h; simp [h] at hg_u; linarith
  use (-(g u)⁻¹) • g
  constructor
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul, inv_mul_cancel₀ hg_u_ne]
  · intro m hm
    simp only [ContinuousLinearMap.smul_apply, hg_vanish m hm, smul_zero]

end BasicSequence
