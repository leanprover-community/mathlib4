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

The key criterion for recognizing basic sequences is the **Grünblum condition**: a sequence `e` is
basic if and only if all partial sums `∑ i < m, a i · e i` are bounded by a constant `K` times the
full sum `∑ i < n, a i · e i` whenever `m ≤ n`. The analogous condition for unconditional basic
sequences, where subsets replace initial segments, is called the **Nikolskii condition**.

## Main Definitions

* `BasicSequence`: A bundled ℕ-indexed sequence that forms a Schauder basis for its span.
* `UnconditionalBasicSequence`: A bundled sequence forming an unconditional Schauder basis.
* `SatisfiesGrunblumCondition`: The Grünblum condition with a constant.
* `SatisfiesNikolskiiCondition`: The Nikolskii condition with a constant.

## Main Results

* `SatisfiesGrunblumCondition.basicSequence`: A nonzero sequence satisfying the Grünblum condition
  is a basic sequence, with an explicit bound on the basis constant.
* `SatisfiesNikolskiiCondition.unconditionalBasicSequence`: The analogous result for unconditional
  basic sequences under the Nikolskii condition.

## Implementation Notes

In the literature, a basic sequence is defined as a sequence that forms a Schauder basis for the
closure of its linear span. In this file, the `SchauderBasis` in `BasicSequence` and
`UnconditionalBasicSequence` lives on the algebraic span `Submodule.span 𝕜 (Set.range e)` rather
than its topological closure, and we additionally bundle a finite projection bound
(`SchauderBasis.enormProjBound < ⊤`). These two conditions are equivalent: a Schauder basis with
finite projection bound on the algebraic span extends to a Schauder basis for the topological
closure of the span. Our formulation is easier to verify:
the projection bound only needs to be checked on elements of the algebraic span, which are finite
linear combinations, so the Grünblum and Nikolskii conditions apply directly without density or
extension arguments. Working with the topological closure would also require cumbersome coercions
between elements of the closed subspace and the ambient space throughout the proofs.

## References

* [Albiac, Fernando. and Kalton, Nigel J., Topics in Banach Space Theory][Albiac_Kalton_2016].
-/

@[expose] public section

noncomputable section

open Submodule Set WeakDual Metric Filter Topology Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A **basic sequence** in a normed space `X` over `𝕜` is an `ℕ`-indexed sequence that forms a
    Schauder basis for its linear span, with finite projection bound. -/
structure BasicSequence (𝕜 : Type*) (X : Type*) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- The underlying sequence. -/
  e : ℕ → X
  /-- The Schauder basis for the span of the sequence. -/
  basis : SchauderBasis 𝕜 (Submodule.span 𝕜 (Set.range e))
  /-- The basis vectors coincide with the sequence elements. -/
  basis_eq : ∀ i, (basis i : X) = e i
  /-- The basis constant is finite. -/
  basisConstant_lt_top : basis.enormProjBound < ⊤

instance : CoeFun (BasicSequence 𝕜 X) (fun _ ↦ ℕ → X) where
  coe b := b.e

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
theorem satisfiesGrunblumCondition : SatisfiesGrunblumCondition 𝕜 bs bs.basicSequenceConstant := by
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

end BasicSequence

namespace SatisfiesGrunblumCondition

variable {e : ℕ → X} {K : ℝ}

/-- The Grünblum constant must be at least `1` for any nonzero sequence. -/
theorem one_le (h : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) : 1 ≤ K := by
  have := h 1 1 (fun _ => 1) le_rfl
  simp only [Finset.range_one, one_smul, sum_singleton] at this
  exact le_of_mul_le_mul_right ((one_mul _).le.trans this) (norm_pos_iff.mpr (h_nz 0))

/-- A nonzero sequence satisfying the Grünblum condition is linearly independent. -/
lemma linearIndependent (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K) (h_nz : ∀ n, e n ≠ 0) :
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
    norm_le_zero_iff.mp (by simpa [h_zero] using h_grunblum N m c hm)
  have hc : c i • e i = 0 := by
    rw [← Finset.sum_range_succ_sub_sum (fun j ↦ c j • e j),
        h_part (i + 1) (hltN i hi), h_part i (hltN i hi).le, sub_zero]
  simpa [c, hi, h_nz i] using hc

private lemma sum_repr_eq_of_support_subset {ι : Type*} {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    (b : Module.Basis ι 𝕜 M) (x : M) {A : Finset ι} (hA : (b.repr x).support ⊆ A) :
    ∑ i ∈ A, b.repr x i • b i = x := by
  conv_rhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_subset hA fun i _ hi ↦ by simp [Finsupp.notMem_support_iff.mp hi]).symm

/-- A nonzero sequence satisfying the Grünblum condition with constant `K` is a basic sequence,
    with basis constant at most `K`. -/
theorem basicSequence (h_grunblum : SatisfiesGrunblumCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : ∃ (b : BasicSequence 𝕜 X), ⇑b = e ∧ b.basicSequenceConstant ≤ K := by
  have h_indep := h_grunblum.linearIndependent h_nz
  have hK : 0 ≤ K := zero_le_one.trans (h_grunblum.one_le h_nz)
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS (n : ℕ) : (b_S n : X) = e n := congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have h_sum (x : S) {N : ℕ} (hN : (b_S.repr x).support.sup id < N) :
      ∑ i ∈ Finset.range N, b_S.repr x i • b_S i = x :=
    sum_repr_eq_of_support_subset b_S x
      fun i hi ↦ Finset.mem_range.2 ((Finset.le_sup (f := id) hi).trans_lt hN)
  have coe_sum (A : Finset ℕ) (c : ℕ → 𝕜) : (↑(∑ i ∈ A, c i • b_S i) : X) = ∑ i ∈ A, c i • e i := by
    simp [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, hbS]
  let P_span (k : ℕ) : S →ₗ[𝕜] S :=
    ∑ i ∈ Finset.range k, ((Finsupp.lapply i).comp b_S.repr.toLinearMap).smulRight (b_S i)
  have h_P_bound (k : ℕ) (x : S) : ‖P_span k x‖ ≤ K * ‖x‖ := by
    let a := b_S.repr x
    let N := max k (a.support.sup id + 1)
    have hN := (Nat.lt_succ_self _).trans_le (le_max_right k (a.support.sup id + 1))
    calc ‖P_span k x‖
      _ = ‖∑ i ∈ Finset.range k, a i • e i‖ := by rw [← norm_coe]; simp [P_span, coe_sum, a]
      _ ≤ K * ‖∑ i ∈ Finset.range N, a i • e i‖ := h_grunblum N k a (le_max_left _ _)
      _ = K * ‖x‖ := by rw [← norm_coe, ← coe_sum, congrArg Subtype.val (h_sum x hN)]
  let P (k : ℕ) : S →L[𝕜] S := (P_span k).mkContinuous K (h_P_bound k)
  have hP (k : ℕ) (x : S) : P k x = ∑ i ∈ Finset.range k, b_S.repr x i • b_S i := by
    change P_span k x = _
    simp [P_span]
  have h_proj_basis (i n : ℕ) (hi : i < n) : P n (b_S i) = b_S i := by
    rw [hP, h_sum _ (by simp [b_S.repr_self, Finsupp.support_single_ne_zero, hi])]
  let D : SchauderBasis.RankOneDecomposition 𝕜 S := {
    P, e := b_S,
    proj_zero := by
      ext x
      change (P 0 x : X) = (0 : S)
      simp [hP]
    finrank_range := fun n ↦ by
      have h_range : (P n).toLinearMap.range =
          Submodule.span 𝕜 (Set.range (fun i : Fin n ↦ b_S i)) := by
        apply le_antisymm
        · rintro _ ⟨x, rfl⟩
          rw [ContinuousLinearMap.coe_coe, hP]
          exact Submodule.sum_mem _ fun i hi ↦
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
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
      congr 1; ext _; simp
    proj_tendsto := fun x ↦ by
      change Filter.Tendsto (fun n ↦ P n x) Filter.atTop (nhds x)
      simp_rw [show ∀ n, P n x = ∑ i ∈ Finset.range n, b_S.repr x i • b_S i from
        fun n ↦ by rw [hP]]
      exact tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support.sup id + 1)
        fun n hn ↦ h_sum x ((Nat.lt_succ_self _).trans_le hn)
    e_mem_range := fun n ↦ ⟨b_S n, by
      change P (n + 1) (b_S n) - P n (b_S n) = b_S n
      simp [hP, Finset.sum_range_succ]⟩
    e_ne_zero := fun n h ↦ h_nz n (by simpa [hbS] using congrArg Subtype.val h) }
  have h_bound : D.basis.enormProjBound ≤ ENNReal.ofReal K := iSup_le fun n ↦ by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK,
      coe_nnnorm, SchauderBasis.RankOneDecomposition.basis_proj D]
    exact ContinuousLinearMap.opNorm_le_bound _ hK (h_P_bound n)
  refine ⟨⟨e, D.basis, fun n ↦ ?_, h_bound.trans_lt ENNReal.ofReal_lt_top⟩, rfl, ?_⟩
  · rw [SchauderBasis.RankOneDecomposition.basis_coe D]; exact hbS n
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound).trans_eq (ENNReal.toReal_ofReal hK)

end SatisfiesGrunblumCondition

/-- An **unconditional basic sequence** indexed by `β` in a normed space `X` over `𝕜` is a
    sequence that forms an unconditional Schauder basis for its span, with finite projection
    bound. -/
structure UnconditionalBasicSequence (β : Type*) (𝕜 : Type*) (X : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  /-- The underlying sequence. -/
  e : β → X
  /-- The unconditional Schauder basis for the span of the sequence. -/
  basis : UnconditionalSchauderBasis β 𝕜 (Submodule.span 𝕜 (Set.range e))
  /-- The basis vectors coincide with the sequence elements. -/
  basis_eq : ∀ i, (basis i : X) = e i
  /-- The basis constant is finite. -/
  basisConstant_lt_top : basis.enormProjBound < ⊤

instance {β : Type*} : CoeFun (UnconditionalBasicSequence β 𝕜 X) (fun _ ↦ β → X) where
  coe b := b.e

/-- A sequence satisfies the **Nikolskii Condition** with constant `K`
    if partial sums over subsets are bounded by `K` times any larger sum. -/
def SatisfiesNikolskiiCondition (𝕜 : Type*) {X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {β : Type*} (e : β → X) (K : ℝ) : Prop :=
    ∀ (A B : Finset β) (a : β → 𝕜), A ⊆ B → ‖∑ i ∈ A, a i • e i‖ ≤ K * ‖∑ i ∈ B, a i • e i‖

namespace UnconditionalBasicSequence

variable (ubs : UnconditionalBasicSequence ℕ 𝕜 X)

/-- Convert an `ℕ`-indexed unconditional basic sequence to a (conditional) basic sequence. -/
def toBasicSequence : BasicSequence 𝕜 X := {
  e := ubs.e,
  basis := ubs.basis.toSchauderBasis,
  basis_eq := fun i => ubs.basis_eq i,
  basisConstant_lt_top :=
    lt_of_le_of_lt ubs.basis.toSchauderBasis_enormProjBound_le ubs.basisConstant_lt_top
}

/-- The coercion of `toBasicSequence` equals the original coercion. -/
@[simp]
lemma coe_toBasicSequence : ⇑(ubs.toBasicSequence) = ⇑ubs := rfl

variable {β : Type*}
variable (ubs : UnconditionalBasicSequence β 𝕜 X)

/-- The **Basis Constant** of an unconditional basic sequence. -/
def unconditionalBasicSequenceConstant : ℝ := ubs.basis.enormProjBound.toReal

open scoped Classical in
/-- An unconditional basic sequence satisfies the Nikolskii condition. -/
theorem satisfiesNikolskiiCondition :
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
      rw [ubs.basis.proj_sum_subset A B a hAB]
    _ ≤ ‖ubs.basis.proj A‖ * ‖∑ i ∈ B, a i • ubs.basis i‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ubs.unconditionalBasicSequenceConstant * ‖∑ i ∈ B, a i • ubs i‖ := by
      rw [h_eq B]; exact mul_le_mul_of_nonneg_right h_bound (norm_nonneg _)

end UnconditionalBasicSequence

namespace SatisfiesNikolskiiCondition

variable {β : Type*} {e : β → X} {K : ℝ}

/-- The Nikolskii constant must be at least `1` for any nonzero sequence. -/
theorem one_le [Nonempty β] (h : SatisfiesNikolskiiCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : 1 ≤ K := by
  have := h {Classical.arbitrary β} {Classical.arbitrary β} (fun _ => 1) Finset.Subset.rfl
  simp only [sum_singleton, one_smul] at this
  exact le_of_mul_le_mul_right ((one_mul _).le.trans this) (norm_pos_iff.mpr (h_nz _))

/-- A nonzero sequence satisfying the Nikolskii condition is linearly independent. -/
lemma linearIndependent (hN : SatisfiesNikolskiiCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intro s g hsg i hi
  simpa [hsg, h_nz i] using hN {i} s g (Finset.singleton_subset_iff.mpr hi)

open scoped Classical in
/-- A nonzero sequence satisfying the Nikolskii condition is an unconditional basic sequence,
    with basis constant at most `K`. -/
theorem unconditionalBasicSequence [Nonempty β] (h : SatisfiesNikolskiiCondition 𝕜 e K)
    (h_nz : ∀ n, e n ≠ 0) : ∃ (b : UnconditionalBasicSequence β 𝕜 X), ⇑b = e ∧
    b.unconditionalBasicSequenceConstant ≤ K := by
  have hK : 0 ≤ K := zero_le_one.trans (h.one_le h_nz)
  have h_indep := h.linearIndependent h_nz
  let S := Submodule.span 𝕜 (Set.range e)
  let b_S := Module.Basis.span h_indep
  have hbS (n : β) : (b_S n : X) = e n := congrArg Subtype.val (Module.Basis.span_apply h_indep n)
  have coe_sum (A : Finset β) (c : β → 𝕜) : (↑(∑ i ∈ A, c i • b_S i) : X) = ∑ i ∈ A, c i • e i := by
    simp [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, hbS]
  have h_sum (x : S) {A : Finset β} (hA : (b_S.repr x).support ⊆ A) :
      ∑ i ∈ A, b_S.repr x i • b_S i = x :=
    SatisfiesGrunblumCondition.sum_repr_eq_of_support_subset b_S x hA
  have norm_sum_eq (y : S) {A : Finset β} (hA : (b_S.repr y).support ⊆ A) :
      ‖∑ i ∈ A, b_S.repr y i • e i‖ = ‖y‖ := by
    rw [← coe_sum, congrArg Subtype.val (h_sum y hA), norm_coe]
  let coord (j : β) : StrongDual 𝕜 S := LinearMap.mkContinuous
    ((Finsupp.lapply j).comp b_S.repr.toLinearMap)
    (K / ‖e j‖)
    fun y ↦ by
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
      exact tendsto_atTop_of_eventually_const (i₀ := (b_S.repr x).support) (fun A hA ↦ h_sum x hA)
  }
  have h_bound : ubs_basis.enormProjBound ≤ ENNReal.ofReal K := iSup_le fun A ↦ by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hK, coe_nnnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ hK fun y ↦ ?_
    have h_proj : (ubs_basis.proj A y : X) = ∑ i ∈ A, b_S.repr y i • e i := by
      have : ubs_basis.proj A y = ∑ i ∈ A, b_S.repr y i • b_S i := by
        simp only [GeneralSchauderBasis.proj_apply]
        congr 1
      rw [this, coe_sum]
    rw [← norm_coe, h_proj]
    calc ‖∑ i ∈ A, b_S.repr y i • e i‖
        ≤ K * ‖∑ i ∈ A ∪ (b_S.repr y).support, (b_S.repr y) i • e i‖ :=
          h A _ _ Finset.subset_union_left
        _ = K * ‖y‖ := by congr 1; exact norm_sum_eq y Finset.subset_union_right
  refine ⟨⟨e, ubs_basis, hbS, h_bound.trans_lt ENNReal.ofReal_lt_top⟩, rfl, ?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h_bound).trans_eq (ENNReal.toReal_ofReal hK)

end SatisfiesNikolskiiCondition

end
