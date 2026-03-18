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
  have h_total : ∑ j ∈ Finset.range N, c j • e j = 0 := by
    rw [← Finset.sum_subset (fun j hj ↦ Finset.mem_range.mpr (hb j hj))
      (fun x _ hx ↦ by simp only [c, hx, ite_false, zero_smul])]
    exact (Finset.sum_congr rfl (fun j hj ↦ by simp [c, hj])).trans hg
  have h_part (m : ℕ) (hm : m ≤ N) : ∑ j ∈ Finset.range m, c j • e j = 0 :=
    norm_le_zero_iff.mp <| by simpa [h_total] using h_grunblum N m c hm
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
  have hbS : ∀ n, (b_S n : X) = e n :=
    fun n ↦ congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have coe_sum (A : Finset ℕ) (c : ℕ → 𝕜) :
      (↑(∑ i ∈ A, c i • b_S i) : X) = ∑ i ∈ A, c i • e i := by
    simp [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, hbS]
  have h_sum (x : S) {N : ℕ} (hN : (b_S.repr x).support.sup id < N) :
      ∑ i ∈ Finset.range N, b_S.repr x i • b_S i = x := by
    conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_subset
      (fun i hi ↦ Finset.mem_range.2 ((Finset.le_sup (f := id) hi).trans_lt hN))
      (fun i _ hi ↦ by simp [Finsupp.notMem_support_iff.mp hi])).symm
  have h_partial_bound (k : ℕ) (y : S) :
      ‖∑ i ∈ Finset.range k, b_S.repr y i • e i‖ ≤ K * ‖y‖ := by
    let N := max k ((b_S.repr y).support.sup id + 1)
    have hN : (b_S.repr y).support.sup id < N :=
      (Nat.lt_succ_self _).trans_le (le_max_right k _)
    conv_rhs => rw [← norm_coe (x := y), ← h_sum y hN, coe_sum]
    exact h_grunblum N k (b_S.repr y) (le_max_left _ _)
  let coord (j : ℕ) : StrongDual 𝕜 S := LinearMap.mkContinuous
    ((Finsupp.lapply j).comp b_S.repr.toLinearMap) ((2 * K) / ‖e j‖) <| fun y ↦ by
      rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (h_nz j))]
      change ‖b_S.repr y j‖ * ‖e j‖ ≤ 2 * K * ‖y‖
      have := (norm_sub_le (∑ i ∈ Finset.range (j + 1), b_S.repr y i • e i)
        (∑ i ∈ Finset.range j, b_S.repr y i • e i)).trans
        (add_le_add (h_partial_bound (j + 1) y) (h_partial_bound j y))
      rw [Finset.sum_range_succ_sub_sum, norm_smul] at this; linarith
  let cond_basis : SchauderBasis 𝕜 S := {
    basis := b_S
    coord := coord
    ortho := fun i j ↦ by
      simp only [coord, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, Finsupp.lapply_apply, b_S.repr_self,
        Finsupp.single_apply, Pi.single_apply]
      split_ifs <;> simp_all
    expansion := fun x ↦ by
      rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
      exact tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support.sup id + 1)
        fun n hn ↦ h_sum x (Nat.lt_of_succ_le hn)
  }
  have h_bound : cond_basis.enormProjBound ≤ ENNReal.ofReal K := iSup_le fun n ↦ by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun y ↦ ?_
    rw [← norm_coe, SchauderBasis.proj_apply, coe_sum]
    exact h_partial_bound n y
  refine ⟨⟨e, cond_basis, hbS, h_bound.trans_lt ENNReal.ofReal_lt_top⟩, rfl, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound).trans_eq (ENNReal.toReal_ofReal hK)

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

open scoped Classical in
/-- A general basic sequence with finite projection bound satisfies the
    generalized Grünblum condition. -/
theorem unconditional_satisfiesNikolskii :
    SatisfiesNikolskiiCondition 𝕜 ubs ubs.unconditionalBasicSequenceConstant := fun A B a hAB ↦ by
  have h_bound : ‖ubs.basis.proj A‖ ≤ ubs.unconditionalBasicSequenceConstant := by
    have h := ubs.basis.enorm_proj_le_enormProjBound A
    rwa [enorm_eq_nnnorm, ← ENNReal.toReal_le_toReal ENNReal.coe_ne_top ubs.basisConstant_lt_top.ne,
      ENNReal.coe_toReal, coe_nnnorm] at h
  have h_eq (S : Finset β) : ‖∑ i ∈ S, a i • ubs.basis i‖ = ‖∑ i ∈ S, a i • ubs i‖ := by
    simp [ubs.basis_eq]
  calc ‖∑ i ∈ A, a i • ubs i‖
    _ = ‖∑ i ∈ A, a i • ubs.basis i‖ := (h_eq A).symm
    _ = ‖ubs.basis.proj A (∑ i ∈ B, a i • ubs.basis i)‖ := by
      congr 1
      simp_rw [map_sum, map_smul, GeneralSchauderBasis.proj_apply_basis_mem, smul_ite, smul_zero]
      exact (Finset.sum_congr rfl fun _ h ↦ if_pos h).symm.trans
        (Finset.sum_subset (f := fun i ↦ if i ∈ A then a i • ubs.basis i else 0)
          hAB fun _ _ h ↦ if_neg h)
    _ ≤ ‖ubs.basis.proj A‖ * ‖∑ i ∈ B, a i • ubs.basis i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ubs.unconditionalBasicSequenceConstant * ‖∑ i ∈ B, a i • ubs i‖ := by
      rw [h_eq B]
      exact mul_le_mul_of_nonneg_right h_bound (norm_nonneg _)
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
  have h_indep := linearIndependent_of_Nikolskii h h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS : ∀ n, (b_S n : X) = e n :=
    fun n ↦ congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have coe_sum (A : Finset β) (c : β → 𝕜) :
      (↑(∑ i ∈ A, c i • b_S i) : X) = ∑ i ∈ A, c i • e i := by
    simp [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, hbS]
  have h_sum (x : S) {A : Finset β} (hA : (b_S.repr x).support ⊆ A) :
      ∑ i ∈ A, b_S.repr x i • b_S i = x := by
    conv_rhs => rw [← b_S.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_subset hA fun i _ hi ↦ by simp [Finsupp.notMem_support_iff.mp hi]).symm
  have norm_sum_eq (y : S) {A : Finset β} (hA : (b_S.repr y).support ⊆ A) :
      ‖∑ i ∈ A, b_S.repr y i • e i‖ = ‖y‖ := by
    rw [← coe_sum, congrArg Subtype.val (h_sum y hA), norm_coe]
  let coord (j : β) : StrongDual 𝕜 S := LinearMap.mkContinuous
    ((Finsupp.lapply j).comp b_S.repr.toLinearMap) (K / ‖e j‖) <| fun y ↦ by
      rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (h_nz j))]
      change ‖b_S.repr y j‖ * ‖e j‖ ≤ K * ‖y‖
      calc ‖b_S.repr y j‖ * ‖e j‖
          = ‖∑ i ∈ {j}, b_S.repr y i • e i‖ := by simp [norm_smul]
          _ ≤ K * ‖∑ i ∈ {j} ∪ (b_S.repr y).support, b_S.repr y i • e i‖ :=
              h {j} _ _ Finset.subset_union_left
          _ = K * ‖y‖ := by congr 1; exact norm_sum_eq y Finset.subset_union_right
  let ubs_basis : UnconditionalSchauderBasis β 𝕜 S := {
    basis := b_S
    coord := coord
    ortho := fun i j ↦ by
      simp only [coord, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, Finsupp.lapply_apply, b_S.repr_self,
        Finsupp.single_apply, Pi.single_apply, eq_comm]
    expansion := fun x ↦ by
      rw [HasSum, SummationFilter.unconditional_filter]
      change Filter.Tendsto (fun A ↦ ∑ i ∈ A, b_S.repr x i • b_S i) atTop (𝓝 x)
      exact tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support)
        (fun A hA ↦ h_sum x hA)
  }
  have h_bound : ubs_basis.enormProjBound ≤ ENNReal.ofReal K := iSup_le fun A ↦ by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun y ↦ ?_
    have h_proj : (ubs_basis.proj A y : X) = ∑ i ∈ A, b_S.repr y i • e i := by
      have : ubs_basis.proj A y = ∑ i ∈ A, b_S.repr y i • b_S i := by
        simp only [GeneralSchauderBasis.proj_apply]; congr 1
      rw [this]; exact coe_sum _ _
    rw [← norm_coe, h_proj]
    calc ‖∑ i ∈ A, b_S.repr y i • e i‖
        ≤ K * ‖∑ i ∈ A ∪ (b_S.repr y).support, (b_S.repr y) i • e i‖ :=
          h A _ _ Finset.subset_union_left
        _ = K * ‖y‖ := by congr 1; exact norm_sum_eq y Finset.subset_union_right
  refine ⟨⟨e, ubs_basis, hbS, h_bound.trans_lt ENNReal.ofReal_lt_top⟩, rfl, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound).trans_eq (ENNReal.toReal_ofReal hK)

theorem SatisfiesNikolskiiCondition.toSatisfiesGrunblumCondition {e : ℕ → X} {K : ℝ}
    (h : SatisfiesNikolskiiCondition 𝕜 e K) :
    SatisfiesGrunblumCondition 𝕜 e K :=
  fun _ _ a hmn => h _ _ a (Finset.range_subset_range.mpr hmn)

end UnconditionalBasicSequence

end -- public section
