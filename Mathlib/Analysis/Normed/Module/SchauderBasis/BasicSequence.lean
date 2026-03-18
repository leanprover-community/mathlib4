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

## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
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
    (h : SatisfiesGrunblumCondition 𝕜 e K) (hKK' : K ≤ K') : SatisfiesGrunblumCondition 𝕜 e K' :=
  fun n m a hmn => (h n m a hmn).trans (mul_le_mul_of_nonneg_right hKK' (norm_nonneg _))

namespace BasicSequence

variable (bs : BasicSequence 𝕜 X)

/-- The **Basis Constant** of a basic sequence. -/
def basicSequenceConstant : ℝ := bs.basis.enormProjBound.toReal

/-- A basic sequence with finite projection bound satisfies the Grünblum condition. -/
theorem basicSequence_satisfiesGrunblum :
    SatisfiesGrunblumCondition 𝕜 bs bs.basicSequenceConstant := by
  intro n m a hmn
  have h_bound : ‖bs.basis.proj m‖ ≤ bs.basicSequenceConstant := by
    have h := bs.basis.enorm_proj_le_enormProjBound m
    rwa [enorm_eq_nnnorm, ← ENNReal.toReal_le_toReal ENNReal.coe_ne_top bs.basisConstant_lt_top.ne,
      ENNReal.coe_toReal, coe_nnnorm] at h
  calc ‖∑ i ∈ Finset.range m, a i • bs i‖
    _ = ‖∑ i ∈ Finset.range m, a i • bs.basis i‖ := by
      simp only [coe_norm, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, bs.basis_eq]
    _ = ‖bs.basis.proj m (∑ i ∈ Finset.range n, a i • bs.basis i)‖ := by
      rw [SchauderBasis.proj_sum_range bs.basis m n a hmn]
    _ ≤ ‖bs.basis.proj m‖ * ‖∑ i ∈ Finset.range n, a i • bs.basis i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ bs.basicSequenceConstant * ‖∑ i ∈ Finset.range n, a i • bs i‖ := by
      simp only [coe_norm, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, bs.basis_eq]
      exact mul_le_mul_of_nonneg_right h_bound (norm_nonneg (∑ i ∈ Finset.range n, a i • bs i))

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
lemma linearIndependent_of_Grunblum {e : ℕ → X} {K : ℝ} (h_nz : ∀ n, e n ≠ 0)
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  let c j := if j ∈ s then g j else 0
  let N := s.sup id + 1
  have hb (j : ℕ) (hj : j ∈ s) : j < N := Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
  have h_tot : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hb j hj)) (fun _ _ hx ↦ by simp [c, hx])]
    exact (Finset.sum_congr rfl (fun j hj ↦ by simp [c, hj])).trans hg
  have h_part (m : ℕ) (hm : m ≤ N) : ∑ j ∈ Finset.range m, c j • e j = 0 :=
    norm_le_zero_iff.mp <| by simpa [h_tot] using h_grunblum N m c hm
  have hc : c i • e i = 0 := by
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j),
        h_part (i + 1) (hb i hi), h_part i (hb i hi).le, sub_zero]
  simpa [c, hi, h_nz i] using hc

/-- A version of `isBasicSequence_of_Grunblum` that also provides an explicit bound
    on the basis constant. If a sequence satisfies the Grünblum condition with constant K,
    the resulting basic sequence has basis constant at most K. -/
theorem isBasicSequence_of_Grunblum_with_bound {e : ℕ → X} {K : ℝ}
    (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
    ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ b.basicSequenceConstant ≤ K := by
  have h_indep := linearIndependent_of_Grunblum h_nz h_grunblum
  have hK : 0 ≤ K := zero_le_one.trans (Grunblum_const_ge_1 h_grunblum h_nz)
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  let e_Y : ℕ → S := b_S
  have hbS : ∀ n, (b_S n : X) = e n :=
    fun n => congrArg Subtype.val (Module.Basis.span_apply h_indep n)
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
  have hP_apply : ∀ k (x : S), P k x = P_span k x := fun _ _ => rfl
  have h0 : P 0 = 0 := by
    ext1 x; simp only [hP_apply, ContinuousLinearMap.zero_apply,
      h_P_span_apply, Finset.range_zero, Finset.sum_empty]
  have hdim (n : ℕ) : Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n := by
    let W := Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ b_S i))
    have h_range : LinearMap.range (P n).toLinearMap = W := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        simp only [ContinuousLinearMap.coe_coe, hP_apply]
        rw [h_P_span_apply]
        refine Submodule.sum_mem _ (fun i hi ↦ ?_)
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
      · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; use b_S i
        simp only [ContinuousLinearMap.coe_coe, hP_apply]
        dsimp only [P_span]
        rw [b_S.constr_basis, if_pos i.isLt]
    rw [h_range, finrank_span_eq_card]
    · exact Fintype.card_fin n
    · exact b_S.linearIndependent.comp (fun i : Fin n => i.val) Fin.val_injective
  have hcomp (n m : ℕ) (y : S) : P n (P m y) = P (min n m) y := by
    simp only [hP_apply]
    conv_lhs => rw [h_P_span_apply m y, h_P_span_apply]
    rw [h_P_span_apply]
    simp only [map_sum, map_smul, Module.Basis.repr_self]
    simp_rw [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
             smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
             ite_smul, zero_smul, ← Finset.sum_filter]
    congr 1; ext j; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  letI : Norm (S →L[𝕜] S) := ContinuousLinearMap.hasOpNorm
  have h_bound_P : ∀ n, ‖P n‖ ≤ K := fun n ↦
    ContinuousLinearMap.opNorm_le_bound _ hK (h_P_span_bound n)
  have hlim (x : S) : Filter.Tendsto (fun n ↦ P n x) Filter.atTop (nhds x) := by
    rw [show (fun n ↦ P n x) = fun n ↦ P_span n x from funext (hP_apply · x)]
    refine tendsto_atTop_of_eventually_const
      (i₀ := (b_S.repr x).support.sup id + 1) fun n hn ↦ ?_
    rw [h_P_span_apply]
    conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply]
    exact (Finset.sum_subset (fun i hi => Finset.mem_range.mpr
      ((Finset.le_sup hi (f := id)).trans_lt (Nat.lt_succ_self _) |>.trans_le hn))
      (fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi])).symm
  have hbS_eq : ∀ n, b_S n = ⟨e n, subset_span (mem_range_self n)⟩ := fun n ↦
    Subtype.ext (hbS n)
  have he_in_range : ∀ n, ⟨e n, subset_span (mem_range_self n)⟩ ∈
      LinearMap.range (SchauderBasis.succSub P n).toLinearMap := fun n ↦ by
    rw [← hbS_eq, LinearMap.mem_range]
    use b_S n
    change P (n + 1) (b_S n) - P n (b_S n) = b_S n
    simp only [hP_apply, h_P_span_apply, Finset.sum_range_succ, add_sub_cancel_left]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]
  have he_ne : ∀ n, (⟨e n, subset_span (mem_range_self n)⟩ : S) ≠ 0 := fun n h ↦
    h_nz n (by simpa using congrArg Subtype.val h)
  let D : SchauderBasis.RankOneDecomposition 𝕜 S := {
    P := P
    e := e_Y
    proj_zero := h0
    finrank_range := hdim
    proj_comp := hcomp
    proj_tendsto := hlim
    e_mem_range := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_in_range n
    e_ne_zero := fun n ↦ by dsimp only [e_Y]; rw [hbS_eq]; exact he_ne n
  }
  let b_basis := D.basis
  have h_lt_top : b_basis.enormProjBound < ⊤ :=
    (iSup_le fun n => by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm]
      change ‖D.basis.proj n‖ ≤ K
      rw [SchauderBasis.RankOneDecomposition.basis_proj D]; exact h_bound_P n).trans_lt
      ENNReal.ofReal_lt_top
  let seq : BasicSequence 𝕜 X := {
    toFun := e
    basis := b_basis
    basis_eq := fun n => by
      rw [SchauderBasis.RankOneDecomposition.basis_coe D]; exact hbS n
    basisConstant_lt_top := h_lt_top
  }
  refine ⟨seq, rfl, ?_⟩
  dsimp only [basicSequenceConstant]
  have h_bound_ennreal : b_basis.enormProjBound ≤ ENNReal.ofReal K :=
    iSup_le fun n => by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK,
        coe_nnnorm, SchauderBasis.RankOneDecomposition.basis_proj D]
      exact h_bound_P n
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound_ennreal).trans_eq
    (ENNReal.toReal_ofReal hK)

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
    have h := ubs.basis.enorm_proj_le_enormProjBound A
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
    simp_rw [map_sum, map_smul, GeneralSchauderBasis.proj_apply_basis_mem]
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
    (h : SatisfiesNikolskiiCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) (hK : 0 ≤ K) :
    ∃ (b : UnconditionalBasicSequence β 𝕜 X),
      ⇑b = e ∧ b.unconditionalBasicSequenceConstant ≤ K := by
  set K' := max K 0 with hK'_def
  have hK'_eq : K' = K := max_eq_left hK
  have hK'_nonneg : 0 ≤ K' := le_max_right _ _
  have h' : SatisfiesNikolskiiCondition 𝕜 e K' := fun A B a hAB => by
    exact (h A B a hAB).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h_indep := linearIndependent_of_Nikolskii h h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS : ∀ n, (b_S n : X) = e n :=
    fun n => congrArg Subtype.val (Module.Basis.span_apply h_indep n)
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
  have hcoord_apply : ∀ i (x : S), coord i x = coord_linear i x := fun _ _ => rfl
  have h_ortho (i j : β) : coord i (b_S j) = (Pi.single j 1 : β → 𝕜) i := by
    simp only [hcoord_apply, coord_linear, LinearMap.comp_apply,
      Finsupp.lapply_apply, Pi.single_apply]
    have : (b_S.repr : S →ₗ[𝕜] (β →₀ 𝕜)) (b_S j) = Finsupp.single j 1 := b_S.repr_self j
    rw [this, Finsupp.single_apply]; simp [eq_comm]
  have h_coord_eq (i : β) (x : S) :
      coord i x = (b_S.repr x : β →₀ 𝕜) i := by
    simp only [hcoord_apply, coord_linear, LinearMap.comp_apply,
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
      change (coord i y) • (b_S i : X) = _
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
  let seq : UnconditionalBasicSequence β 𝕜 X :=
    { toFun := e, basis := ubs_basis, basis_eq := hbS, basisConstant_lt_top := h_lt_top }
  refine ⟨seq, rfl, ?_⟩
  dsimp only [unconditionalBasicSequenceConstant]
  have h_bound_ennreal : ubs_basis.enormProjBound ≤ ENNReal.ofReal K :=
    hK'_eq ▸ iSup_le fun A => by
      rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_le_ofReal_iff hK'_nonneg, coe_nnnorm]
      exact ContinuousLinearMap.opNorm_le_bound _ hK'_nonneg (h_proj_bound A)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound_ennreal).trans_eq
    (ENNReal.toReal_ofReal hK)

theorem SatisfiesNikolskiiCondition.toSatisfiesGrunblumCondition {e : ℕ → X} {K : ℝ}
    (h : SatisfiesNikolskiiCondition 𝕜 e K) :
    SatisfiesGrunblumCondition 𝕜 e K :=
  fun _ _ a hmn => h _ _ a (Finset.range_subset_range.mpr hmn)

end UnconditionalBasicSequence

end -- public section
