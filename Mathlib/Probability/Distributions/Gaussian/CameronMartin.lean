/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Topology.Algebra.Module.ClosedSubmodule


/-!
# Cameron-Martin space

TODO: this is not up to date with the latest use of the rkhs for the def

A Gaussian measure `μ` on a Banach space `E` is characterized by a separable Hilbert space,
called the Cameron-Martin space of `μ`.
That space is a subspace of `E`, but with a different norm.

In this file, we define a type `cameronMartin μ` and build a bijective continuous linear map from
that type to the subset of `E` of points `y` such that the quantity
`⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y` is finite.

Since `μ` has finite second moment, for every function `L : StrongDual ℝ E`, the function
`L ↦ L (x - μ[id])` can be seen as a function in L2.
The subspace of L2 we obtain that way inherits the scalar product of L2, which is equal to the
covariance `covarianceBilin μ L L'`.
We define `cameronMartin μ` as the completion of that subspace. It is a separable Hilbert space.

This is the RKHS construction of the Cameron-Martin space. Another construction would be to
consider the subspace of `E` consisting of all points `y` such that the quantity
`⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y` is finite, and to endow it with
the norm `‖y‖ = ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y`.
Here we don't define the Cameron-Martin space as a subspace because it would inherit
the norm from `E`, which is not the norm we want to put on it. And we don't want to have two norms
on the same type.

## Main definitions

* `cameronMartin μ`: Cameron-Martin space of the measure `μ`.
* `cmOfDual μ L`: inclusion of the dual space `StrongDual ℝ E` into the Cameron-Martin space.
* `cmCoe`: the continuous linear map from the Cameron-Martin space
  to the initial space `E`. It is injective and its range is the subspace of `E` of points
  `y` such that `⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y` is finite.
* `cmOfBounded`: the inverse of `cmCoe`, which takes a point `y : E` with bounded
  Cameron-Martin norm and returns a point of `cameronMartin μ`.

## Main statements

* `range_cmCoe`: the range of `cmCoe` is the set `{y : E | ∃ M, ∀ L, Var[L; μ] ≤ 1 → L y ≤ M}`.
* `cmCoe_cmOfBounded` and `cmOfBounded_cmCoe`: the two maps `cmCoe` and `cmOfBounded` are inverses
  of each other.

* `norm_cameronMartin_eq_ciSup`: for `x` in the Cameron-Martin space,
  `‖x‖ = ⨆ (L) (_ : Var[L; μ] ≤ 1), L (cmCoe x)`.
* `norm_cmOfBounded`: for `y` in `E` with bounded Cameron-Martin norm,
  `‖cmOfBounded μ y‖ = ⨆ (L) (_ : Var[L; μ] ≤ 1), L y`.

## Implementation details

We build the Cameron-Martin space for any finite measure with a finite second moment, not only for
Gaussian measures. We do so only because we can write the definition with that weaker hypothesis:
we are not aware of any use of the Cameron-Martin space for non-Gaussian measures.

## References

* [F. Bar, *Quuxes*][bibkey]

-/

open MeasureTheory NormedSpace UniformSpace
open scoped ENNReal InnerProductSpace

lemma InnerProductSpace.norm_le_dual_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ y : E, ⟪x, y⟫_ℝ ≤ M * ‖y‖) :
    ‖x‖ ≤ M := by
  refine NormedSpace.norm_le_dual_bound ℝ _ hMp fun f ↦ ?_
  let y := (InnerProductSpace.toDual ℝ E).symm f
  obtain hy : f x = ⟪x, y⟫_ℝ := by
    unfold y
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  rw [hy]
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · specialize hM (-y)
    simp only [inner_neg_right, norm_neg] at hM
    rw [← neg_le]
    convert hM
    simp [y]
  · convert hM y
    simp [y]

lemma InnerProductSpace.norm_le_dual_bound_of_norm_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ y : E, ‖y‖ ≤ 1 → ⟪x, y⟫_ℝ ≤ M) :
    ‖x‖ ≤ M := by
  refine InnerProductSpace.norm_le_dual_bound x hMp fun y ↦ ?_
  by_cases h_zero : ‖y‖ = 0
  · simp only [h_zero, mul_zero]
    rw [inner_eq_zero_of_right _ h_zero]
  specialize hM (‖y‖⁻¹ • y) ?_
  · simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm]
    exact inv_mul_le_one
  · simp only [inner_smul_right] at hM
    rwa [inv_mul_le_iff₀ (by positivity), mul_comm] at hM

lemma InnerProductSpace.norm_eq_ciSup_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (x : E) :
    ‖x‖ = ⨆ (y : E) (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ := by
  have h_ciSup_le y : ⨆ (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ ≤ ‖x‖ := by
    by_cases hy : ‖y‖ ≤ 1
    · simp only [hy, ciSup_unique]
      calc ⟪x, y⟫_ℝ
      _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * 1 := by gcongr
      _ = ‖x‖ := by rw [mul_one]
    · simp [hy]
  have h_bdd : BddAbove (Set.range fun y ↦ ⨆ (_ : ‖y‖ ≤ 1), ⟪x, y⟫_ℝ) := by
    refine ⟨‖x‖, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro y
    exact h_ciSup_le y
  refine le_antisymm ?_ (ciSup_le h_ciSup_le)
  · refine InnerProductSpace.norm_le_dual_bound_of_norm_le_one x ?_ fun y hy ↦ ?_
    · exact le_ciSup_of_le h_bdd 0 (by simp)
    · exact le_ciSup_of_le h_bdd y (by simp [hy])

namespace UniformSpace.Completion

variable {R E F : Type*} [Semiring R]
    [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E]
    [Module R E] [UniformContinuousConstSMul R E]
    [UniformSpace F] [AddCommGroup F] [IsUniformAddGroup F]
    [Module R F] [UniformContinuousConstSMul R F] [T2Space F] [CompleteSpace F]

variable (R) in
/-- Extension of a continuous linear map `E →L[R] F` into a complete space to the completion of `E`,
giving a continuous linear map `Completion E →L[R] F`. -/
noncomputable
def continuousLinearMapExtension (f : E →L[R] F) : Completion E →L[R] F where
  toFun x := Completion.extension f x
  map_add' x₁ x₂ := by
    refine Completion.induction_on₂ x₁ x₂ ?_ fun x₁' x₂' ↦ ?_
    · have : Continuous (Completion.extension f) := continuous_extension
      exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [extension_coe, extension_coe, ← map_add, ← extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction x using Completion.induction_on with
    | hp =>
      have h_cont : Continuous (Completion.extension f) := continuous_extension
      refine isClosed_eq ?_ (by fun_prop)
      -- fun_prop fails here (it also fails in the `have` below)
      have : Continuous fun (a : Completion E) ↦ r • a := continuous_const_smul _
      exact h_cont.comp this
    | ih x =>
      rw [extension_coe, ← map_smul, ← extension_coe (f := f)]
      · congr
        norm_cast
      all_goals exact ContinuousLinearMap.uniformContinuous _

lemma continuousLinearMapExtension_apply (f : E →L[R] F) (x : Completion E) :
    Completion.continuousLinearMapExtension R f x = Completion.extension f x := by
  simp [continuousLinearMapExtension]

@[simp]
lemma continuousLinearMapExtension_coe (f : E →L[R] F) (x : E) :
    Completion.continuousLinearMapExtension R f x = f x := by
  simp [continuousLinearMapExtension, extension_coe f.uniformContinuous]

end UniformSpace.Completion

lemma norm_eval_le_norm_mul_ciSup {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [Module ℝ G] [NormSMulClass ℝ G]
    (f : StrongDual ℝ E →ₗ[ℝ] G) {y : E} (hy : ∃ M, ∀ L, ‖f L‖ ≤ 1 → L y ≤ M) (L : StrongDual ℝ E) :
    ‖L y‖ ≤ ‖f L‖ * ⨆ (L') (_ : ‖f L'‖ ≤ 1), L' y := by
  have h_bdd : BddAbove (Set.range fun L' ↦ ⨆ (_ : ‖f L'‖ ≤ 1), L' y) := by
    obtain ⟨M, hM⟩ := hy
    refine ⟨M, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro L
    by_cases hL : ‖f L‖ ≤ 1
    · simpa [hL] using hM L hL
    · simp only [hL, Real.iSup_of_isEmpty]
      simpa using hM 0 (by simp)
  have h L (hL : ‖f L‖ = 1) : ‖L y‖ ≤ ‖f L‖ * ⨆ L', ⨆ (_ : ‖f L'‖ ≤ 1), L' y := by
    rw [hL, one_mul]
    rcases le_total 0 (L y) with hLy | hLy
    · exact le_ciSup_of_le h_bdd L (by simp [hL, abs_of_nonneg hLy])
    · exact le_ciSup_of_le h_bdd (-L) (by simp [hL, abs_of_nonpos hLy])
  have hL_zero_of_L2 (hL : f L = 0) : L y = 0 := by
    have h_smul (r : ℝ) : f (r • L) = 0 := by simp [hL]
    contrapose! hy with hL_zero
    refine fun M ↦ ⟨((M + 1) / L y) • L, by simp [h_smul], ?_⟩
    simp [div_mul_cancel₀ _ hL_zero]
  by_cases hL_zero : L y = 0
  · simp only [hL_zero, norm_zero]
    refine mul_nonneg (by positivity) ?_
    exact le_ciSup_of_le h_bdd 0 (by simp)
  specialize h (‖f L‖⁻¹ • L) ?_
  · simp only [map_smul, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀]
    simp only [ne_eq, norm_eq_zero]
    contrapose! hL_zero
    exact hL_zero_of_L2 hL_zero
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    norm_norm, map_smul, norm_smul] at h
  rwa [mul_assoc, mul_le_mul_iff_of_pos_left] at h
  simp only [inv_pos, norm_pos_iff, ne_eq]
  contrapose! hL_zero
  exact hL_zero_of_L2 hL_zero

def abstractCompletionClosure {α : Type*} [UniformSpace α] [T0Space α] [CompleteSpace α]
    (s : Set α) :
    AbstractCompletion s where
  space := closure s
  coe x := ⟨x, subset_closure x.2⟩
  uniformStruct := inferInstance
  complete := isClosed_closure.isComplete.completeSpace_coe
  separation := inferInstance
  isUniformInducing := by
    constructor
    simp only [uniformity_subtype, Filter.comap_comap]
    congr
  dense := by
    rw [DenseRange, Subtype.dense_iff]
    refine closure_mono fun x hx ↦ ?_
    simp [hx, subset_closure hx]

@[simp]
lemma Submodule.mem_topologicalClosure_iff {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) (x : M) :
    x ∈ s.topologicalClosure ↔ x ∈ closure s := by
  simp only [Submodule.topologicalClosure, AddSubmonoid.topologicalClosure,
    Submodule.coe_toAddSubmonoid, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk]

lemma Submodule.mem_closure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) (L : s) :
    (L : M) ∈ s.topologicalClosure := by
  rw [Submodule.mem_topologicalClosure_iff]
  exact subset_closure L.2

instance {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] (s : Submodule R M) :
    ContinuousAdd s := AddSubmonoid.continuousAdd s.toAddSubmonoid

instance {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] (s : ClosedSubmodule R M) :
    ContinuousAdd s := AddSubmonoid.continuousAdd s.toAddSubmonoid

instance {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousConstSMul R M] (s : Submodule R M) :
    ContinuousConstSMul R s where
  continuous_const_smul r :=
    ((continuous_const_smul r).comp continuous_subtype_val).subtype_mk _

instance {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [UniformSpace M] [UniformContinuousConstSMul R M] (s : Submodule R M) :
    UniformContinuousConstSMul R s where
  uniformContinuous_const_smul r :=
    ((uniformContinuous_const_smul r).comp uniformContinuous_subtype_val).subtype_mk _

@[coe] def coeClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} :
    s → s.topologicalClosure := fun L ↦ ⟨L, Submodule.mem_closure s L⟩

instance {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} :
    Coe s s.topologicalClosure :=
  ⟨coeClosure⟩

@[simp, norm_cast]
lemma coeClosure_add {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} (x y : s) :
    ((x + y : s) : s.topologicalClosure)
      = (x : s.topologicalClosure) + (y : s.topologicalClosure) := by
  simp [coeClosure]

@[simp, norm_cast]
lemma coeClosure_sub {M R : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} (x y : s) :
    ((x - y : s) : s.topologicalClosure)
      = (x : s.topologicalClosure) - (y : s.topologicalClosure) := by
  simp only [coeClosure, AddSubgroupClass.coe_sub]
  norm_cast

@[simp, norm_cast]
lemma coeClosure_smul {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] {s : Submodule R M} (r : R) (x : s) :
    ((r • x : s) : s.topologicalClosure) = r • (x : s.topologicalClosure) := by
  simp [coeClosure]

@[fun_prop, continuity]
lemma continuous_coeClosure {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    Continuous (coeClosure : s → s.topologicalClosure) := by
  unfold coeClosure
  fun_prop

def toClosureCLM {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousConstSMul R M] (s : Submodule R M) :
    s →L[R] s.topologicalClosure where
  toFun := coeClosure
  map_add' := coeClosure_add
  map_smul' := coeClosure_smul

section Extension

variable {M R F : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
    [CompleteSpace M] [UniformContinuousConstSMul R M]
    [UniformSpace F] [AddCommGroup F] [Module R F] [T2Space F] [CompleteSpace F]
    {s : Submodule R M}

noncomputable
def closureExtension (s : Submodule R M) (f : s → F) : s.topologicalClosure → F :=
  AbstractCompletion.extend (abstractCompletionClosure s.carrier) f

omit [AddCommGroup F] [Module R F] [CompleteSpace F] in
@[simp]
lemma closureExtension_coe {f : s → F} (hf : UniformContinuous f) (a : s) :
  closureExtension s f a = f a := (abstractCompletionClosure s.carrier).extend_coe hf a

omit [AddCommGroup F] [Module R F] [T2Space F] in
@[fun_prop, continuity]
lemma continuous_closureExtension (s : Submodule R M) (f : s → F) :
    Continuous (closureExtension s f) := AbstractCompletion.continuous_extend _

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

theorem AbstractCompletion.denseRange_coe₂ {α β : Type*} [UniformSpace α] [UniformSpace β]
    (pkgα : AbstractCompletion α) (pkgβ : AbstractCompletion β) :
    DenseRange fun x : α × β => (pkgα.coe x.1, pkgβ.coe x.2) :=
  pkgα.dense.prodMap pkgβ.dense

@[elab_as_elim]
theorem AbstractCompletion.induction_on₂ {α β : Type*} [UniformSpace α] [UniformSpace β]
    (pkgα : AbstractCompletion α) (pkgβ : AbstractCompletion β)
    {p : pkgα.space → pkgβ.space → Prop} (a : pkgα.space) (b : pkgβ.space)
    (hp : IsClosed { x : pkgα.space × pkgβ.space | p x.1 x.2 })
    (ih : ∀ (a : α) (b : β), p (pkgα.coe a) (pkgβ.coe b)) :
    p a b :=
  have : ∀ x : pkgα.space × pkgβ.space, p x.1 x.2 :=
    isClosed_property (denseRange_coe₂ pkgα pkgβ) hp fun ⟨a, b⟩ => ih a b
  this (a, b)

@[elab_as_elim]
theorem induction_topologicalClosure {p : s.topologicalClosure → Prop} (a : s.topologicalClosure)
    (hp : IsClosed { a | p a }) (ih : ∀ a : s, p a) :
    p a :=
  AbstractCompletion.induction_on (abstractCompletionClosure s.carrier) a hp ih

@[elab_as_elim]
lemma induction_topologicalClosure₂
    {p : s.topologicalClosure → s.topologicalClosure → Prop} (a b : s.topologicalClosure)
    (hp : IsClosed { x : s.topologicalClosure × s.topologicalClosure | p x.1 x.2 })
    (ih : ∀ (a b : s), p a b) :
    p a b :=
  AbstractCompletion.induction_on₂ (abstractCompletionClosure s.carrier)
    (abstractCompletionClosure s.carrier) a b hp ih

omit [AddCommGroup F] [Module R F] [CompleteSpace F] in
lemma funext_topologicalClosure {f g : s.topologicalClosure → F} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a : s, f a = g a) : f = g :=
  funext fun a => induction_topologicalClosure a (isClosed_eq hf hg) h

variable [IsUniformAddGroup F] [UniformContinuousConstSMul R F]

noncomputable
def closureExtensionCLM (s : Submodule R M) (f : s →L[R] F) : s.topologicalClosure →L[R] F where
  toFun := closureExtension s f
  map_add' x₁ x₂ := by
    refine induction_topologicalClosure₂ x₁ x₂ ?_ fun x₁' x₂' ↦ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [closureExtension_coe, closureExtension_coe, ← map_add, ← closureExtension_coe (f := f)]
      · congr
      all_goals exact ContinuousLinearMap.uniformContinuous _
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction x using induction_topologicalClosure with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      rw [closureExtension_coe, ← map_smul, ← closureExtension_coe (f := f)]
      · rfl
      all_goals exact ContinuousLinearMap.uniformContinuous _

lemma closureExtensionCLM_apply (s : Submodule R M) (f : s →L[R] F)
    (x : s.topologicalClosure) :
    closureExtensionCLM s f x = closureExtension s f x := by
  simp [closureExtensionCLM]

@[simp]
lemma closureExtensionCLM_coe (s : Submodule R M) (f : s →L[R] F) (x : s) :
    closureExtensionCLM s f x = f x := by
  simp [closureExtensionCLM, closureExtension_coe f.uniformContinuous]

end Extension

noncomputable
def completionClosureEquiv {M R : Type*} [Ring R] [NormedAddCommGroup M] [CompleteSpace M]
    [Module R M] [UniformContinuousConstSMul R M] (s : Submodule R M) :
    Completion s ≃ᵤ s.topologicalClosure :=
  AbstractCompletion.compareEquiv (UniformSpace.Completion.cPkg (α := s))
    (abstractCompletionClosure s.carrier)

@[simp]
lemma completionClosureEquiv_coe {M R : Type*} [Ring R] [NormedAddCommGroup M] [CompleteSpace M]
    [Module R M] [UniformContinuousConstSMul R M] {s : Submodule R M} (L : s) :
    completionClosureEquiv s L = L := by
  simp [completionClosureEquiv, AbstractCompletion.compareEquiv]
  exact AbstractCompletion.compare_coe _ _ _

noncomputable
def completionClosureLinearIsometry {M R : Type*} [Ring R] [NormedAddCommGroup M] [Module R M]
    [CompleteSpace M] [UniformContinuousConstSMul R M] (s : Submodule R M) :
    Completion s ≃ₗᵢ[R] s.topologicalClosure where
  toEquiv := completionClosureEquiv s
  map_add' x y := by
    refine Completion.induction_on₂ x y ?_ fun x' y' ↦ ?_
    · have : Continuous (completionClosureEquiv s) := UniformEquiv.continuous _
      exact isClosed_eq (by fun_prop) (by fun_prop)
    · rw [← Completion.coe_add]
      simp
  map_smul' r x := by
    simp only [RingHom.id_apply]
    induction x using Completion.induction_on with
    | hp =>
      have : Continuous (completionClosureEquiv s) := UniformEquiv.continuous _
      exact isClosed_eq (this.comp (continuous_const_smul _)) (by fun_prop)
    | ih x =>
      rw [← Completion.coe_smul]
      simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, completionClosureEquiv_coe]
      norm_cast
  norm_map' x := by
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm]
    induction x using Completion.induction_on with
    | hp =>
      have : Continuous (completionClosureEquiv s) := UniformEquiv.continuous _
      exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih a =>
      simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, completionClosureEquiv_coe,
        Completion.norm_coe, AddSubgroupClass.coe_norm]
      norm_cast

@[simp]
lemma completionClosureLinearIsometry_coe {M R : Type*} [Ring R] [NormedAddCommGroup M]
    [CompleteSpace M] [Module R M] [UniformContinuousConstSMul R M] {s : Submodule R M} (L : s) :
    completionClosureLinearIsometry s L = L := by
  simp [completionClosureLinearIsometry]

namespace ProbabilityTheory

/-- A finite measure has two moments if `∫ x, x ^ 2 ∂μ < ∞`, that is if `MemLp id 2 μ`. -/
class HasTwoMoments {E : Type*} {_ : MeasurableSpace E} [ENorm E] [TopologicalSpace E]
    (μ : Measure E) extends IsFiniteMeasure μ where
  memLp_two : MemLp id 2 μ

lemma memLp_two_id {E : Type*} {_ : MeasurableSpace E} [ENorm E] [TopologicalSpace E]
    {μ : Measure E} [HasTwoMoments μ] : MemLp id 2 μ := HasTwoMoments.memLp_two

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E]
  {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {y : E}

instance [SecondCountableTopology E] [IsGaussian μ] : HasTwoMoments μ where
  memLp_two := IsGaussian.memLp_id μ 2 (by simp)

lemma _root_.ContinuousLinearMap.memLp_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {_ : MeasurableSpace E}
    {μ : Measure E} [HasTwoMoments μ] (L : StrongDual ℝ E) :
    MemLp L 2 μ := L.comp_memLp' memLp_two_id

section centeredToLp

/-- The Bochner integral as a continuous linear map from the StrongDual to `ℝ`.
This is well defined if the measure has a first moment. If not, it is uniformly zero (since
`Dual.toLp` is zero in that case). -/
noncomputable
def integralDualCLM (μ : Measure E) : StrongDual ℝ E →L[ℝ] ℝ :=
  L1.integralCLM.comp (StrongDual.toLp μ 1)

/-- The function `L ↦ L (x - μ[id])` as a continuous linear map from the StrongDual to `Lp ℝ p μ`.
This definition takes meaningful values only if the measure has a moment of order `p`
(`MemLp id p μ`). -/
noncomputable
def StrongDual.centeredToLp (μ : Measure E) [IsFiniteMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    StrongDual ℝ E →L[ℝ] Lp ℝ p μ :=
  StrongDual.toLp μ p - (Lp.constL p μ ℝ).comp (integralDualCLM μ)

lemma centeredToLp_apply [IsFiniteMeasure μ] (hμp : MemLp id p μ) (L : StrongDual ℝ E) :
    StrongDual.centeredToLp μ p L =ᵐ[μ] fun x ↦ L (x - ∫ z, z ∂μ) := by
  have hμ1 : MemLp id 1 μ := MemLp.mono_exponent hμp (Fact.out (p := 1 ≤ p))
  by_cases hμ_zero : μ = 0
  · simp only [hμ_zero, ae_zero, integral_zero_measure, sub_zero]
    exact trivial
  replace hμ_zero : NeZero μ := ⟨hμ_zero⟩
  simp only [StrongDual.centeredToLp, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    AddSubgroupClass.coe_sub, map_sub]
  filter_upwards [StrongDual.toLp_apply_ae hμp L,
    Lp.coeFn_sub (StrongDual.toLp μ p L) ((Lp.constL p μ ℝ).comp (integralDualCLM μ) L)]
    with x hx₁ hx₂
  simp only [AddSubgroupClass.coe_sub, Pi.sub_apply] at hx₂
  rw [← hx₁, hx₂]
  congr
  simp only [integralDualCLM, ContinuousLinearMap.coe_comp', Function.comp_apply,
    Lp.constL_apply, Lp.const_val, AEEqFun.coeFn_const_eq]
  have h_int_eq := L.integral_comp_comm (hμ1.integrable le_rfl)
  simp only [id_eq] at h_int_eq
  rw [← L1.integral_eq, L1.integral_eq_integral, ← h_int_eq]
  refine integral_congr_ae ?_
  exact StrongDual.toLp_apply_ae hμ1 L

lemma centeredToLp_two_inner [HasTwoMoments μ] (L₁ L₂ : StrongDual ℝ E) :
    ⟪StrongDual.centeredToLp μ 2 L₁, StrongDual.centeredToLp μ 2 L₂⟫_ℝ
      = covarianceBilin μ L₁ L₂ := by
  rw [real_inner_comm, L2.inner_def, covarianceBilin_apply' memLp_two_id]
  refine integral_congr_ae ?_
  filter_upwards [centeredToLp_apply memLp_two_id L₁, centeredToLp_apply memLp_two_id L₂]
    with x hx₁ hx₂
  simp [hx₁, hx₂]

lemma norm_centeredToLp_two [HasTwoMoments μ] (L : StrongDual ℝ E) :
    ‖StrongDual.centeredToLp μ 2 L‖ = √Var[L; μ] := by
  rw [norm_eq_sqrt_real_inner, centeredToLp_two_inner,
    covarianceBilin_self_eq_variance memLp_two_id]

lemma sq_norm_centeredToLp_two [HasTwoMoments μ] (L : StrongDual ℝ E) :
    ‖StrongDual.centeredToLp μ 2 L‖ ^ 2 = Var[L; μ] := by
  rw [← real_inner_self_eq_norm_sq, centeredToLp_two_inner,
    covarianceBilin_self_eq_variance memLp_two_id]

end centeredToLp

section CameronMartinSpace

/-- The Cameron-Martin space of a Gaussian measure.
This is a separable Hilbert space. -/
noncomputable
def cameronMartin (μ : Measure E) [HasTwoMoments μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (LinearMap.range (StrongDual.centeredToLp μ 2)).topologicalClosure

variable [HasTwoMoments μ]

noncomputable
instance : Coe (LinearMap.range (StrongDual.centeredToLp μ 2)) (cameronMartin μ) := ⟨coeClosure⟩

noncomputable
instance instCoeFun : CoeFun (cameronMartin μ) (fun _ ↦ E → ℝ) := ⟨fun f ↦ (f : E → ℝ)⟩

noncomputable instance : NormedAddCommGroup (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

noncomputable instance : InnerProductSpace ℝ (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

noncomputable instance : CompleteSpace (cameronMartin μ) := by
  unfold cameronMartin
  infer_instance

instance [SecondCountableTopology E] (μ : Measure E) [HasTwoMoments μ] :
    SecondCountableTopology (cameronMartin μ) := by
  have : Fact (2 ≠ ∞) := ⟨by simp⟩
  exact TopologicalSpace.Subtype.secondCountableTopology _

/-- Inclusion from the StrongDual into the Cameron-Martin space, as a linear map. -/
noncomputable
def cmOfDual (μ : Measure E) [HasTwoMoments μ] : StrongDual ℝ E →ₗ[ℝ] cameronMartin μ :=
  (toClosureCLM _).toLinearMap.comp ((StrongDual.centeredToLp μ 2).toLinearMap.rangeRestrict)

noncomputable
instance : Coe (StrongDual ℝ E) (cameronMartin μ) := ⟨cmOfDual μ⟩

omit [CompleteSpace E] in
lemma cmOfDual_apply (L : StrongDual ℝ E) :
    cmOfDual μ L = (⟨StrongDual.centeredToLp μ 2 L, LinearMap.mem_range.mpr ⟨L, rfl⟩⟩ :
        LinearMap.range (StrongDual.centeredToLp μ 2)) := rfl

lemma cmOfDual_inner (L₁ L₂ : StrongDual ℝ E) :
    ⟪cmOfDual μ L₁, cmOfDual μ L₂⟫_ℝ = covarianceBilin μ L₁ L₂ := by
  simp only [cmOfDual_apply]
  exact centeredToLp_two_inner L₁ L₂

lemma norm_cmOfDual (L : StrongDual ℝ E) : ‖cmOfDual μ L‖ = √Var[L; μ] := by
  rw [norm_eq_sqrt_real_inner, cmOfDual_inner, covarianceBilin_self_eq_variance memLp_two_id]

lemma sq_norm_cmOfDual (L : StrongDual ℝ E) : ‖cmOfDual μ L‖ ^ 2 = Var[L; μ] := by
  rw [← real_inner_self_eq_norm_sq, cmOfDual_inner, covarianceBilin_self_eq_variance memLp_two_id]

end CameronMartinSpace

section cmOfBounded

/-! We build a map from the elements of `E` with finite Cameron-Martin norm to
the Cameron-Martin space. -/

variable [HasTwoMoments μ]

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- For an L2 function `x` in the image of `Dual ℝ E` by `Dual.centeredToLp μ 2`, we can evaluate
`x` at `y : E` by taking `L y` for an arbitrary `L : StrongDual ℝ E` that is sent to `x`.
This is an auxiliary definition for `CameronMartin.eval`. -/
noncomputable
def evalL2 (μ : Measure E) [HasTwoMoments μ] (y : E)
    (x : LinearMap.range (StrongDual.centeredToLp μ 2)) : ℝ :=
  (LinearMap.mem_range.mp x.2).choose y

lemma norm_eval_le_norm_centeredToLp_mul (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    ‖L y‖ ≤ ‖StrongDual.centeredToLp μ 2 L‖
      * ⨆ (L' : StrongDual ℝ E) (_ : Var[L'; μ] ≤ 1), L' y := by
  simp_rw [← sq_norm_centeredToLp_two,
    sq_le_one_iff_abs_le_one, abs_norm] at hy ⊢
  exact norm_eval_le_norm_mul_ciSup (StrongDual.centeredToLp μ 2).toLinearMap hy L

lemma norm_evalL2_le (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp μ 2)) :
    ‖evalL2 μ y x‖ ≤ ‖x‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y := by
  simp only [AddSubgroupClass.coe_norm]
  conv_rhs => rw [← (LinearMap.mem_range.mp x.2).choose_spec]
  exact norm_eval_le_norm_centeredToLp_mul hy (LinearMap.mem_range.mp x.2).choose

lemma eval_eq_of_centeredToLp_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L L' : StrongDual ℝ E) (hL : StrongDual.centeredToLp μ 2 L = StrongDual.centeredToLp μ 2 L') :
    L y = L' y := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← norm_eq_zero]
  suffices ‖⇑(L - L') y‖ = 0 by simpa
  refine le_antisymm ?_ (by positivity)
  refine (norm_eval_le_norm_centeredToLp_mul hy _ (μ := μ)).trans ?_
  simp [hL]

lemma evalL2_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (x : LinearMap.range (StrongDual.centeredToLp μ 2))
    {L : StrongDual ℝ E} (hL : StrongDual.centeredToLp μ 2 L = x) :
    evalL2 μ y x = L y := by
  rw [evalL2]
  refine eval_eq_of_centeredToLp_eq hy (LinearMap.mem_range.mp x.2).choose L ?_
  rw [hL, (LinearMap.mem_range.mp x.2).choose_spec]

lemma evalL2_centeredToLp_eq (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    evalL2 μ y ⟨StrongDual.centeredToLp μ 2 L, LinearMap.mem_range.mpr ⟨L, rfl⟩⟩ = L y :=
  evalL2_eq hy _ (by simp)

end CameronMartinAux

open CameronMartinAux

/-- Evaluation map on the Cameron-Martin space. `CameronMartin.eval μ y hy x` is the evaluation of
`x` at `y`, where `x` is an element of the Cameron-Martin space of the Gaussian measure `μ`.
This map is defined for `y` with bounded Cameron-Martin norm, i.e., such that there exists `M` with
`∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M`.
It satisfies `cmEval μ y hy (ofDual μ L) = L y`. -/
noncomputable
def cmEval (μ : Measure E) [HasTwoMoments μ] (y : E)
    (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    StrongDual ℝ (cameronMartin μ) :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp μ 2)) <|
  LinearMap.mkContinuous
    { toFun x := evalL2 μ y x
      map_add' x₁ x₂ := by
        obtain ⟨L₁, hL₁⟩ := LinearMap.mem_range.mp x₁.2
        obtain ⟨L₂, hL₂⟩ := LinearMap.mem_range.mp x₂.2
        rw [evalL2_eq hy x₁ hL₁, evalL2_eq hy x₂ hL₂, evalL2_eq hy (x₁ + x₂) (L := L₁ + L₂)]
        · simp
        · simp [hL₁, hL₂]
      map_smul' r x := by
        obtain ⟨L, hL⟩ := LinearMap.mem_range.mp x.2
        rw [evalL2_eq hy x hL, evalL2_eq hy (r • x) (L := r • L)]
        · simp
        · simp [hL] }
    (⨆ (L' : StrongDual ℝ E) (_ : Var[L'; μ] ≤ 1), L' y) fun x ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, AddSubgroupClass.coe_norm]
    rw [mul_comm]
    exact norm_evalL2_le hy x

lemma cmEval_cmOfDual (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)
    (L : StrongDual ℝ E) :
    cmEval μ y hy (cmOfDual μ L) = L y := by
  rw [cmOfDual_apply, cmEval]
  unfold cameronMartin
  simp only [closureExtensionCLM_coe, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [evalL2_centeredToLp_eq hy]

/-- Map from the space on which a Gaussian measure `μ` is defined to the Cameron-Martin space
of `μ`. This takes a meaningful value only if the argument has bounded Cameron-Martin norm,
and takes the default value zero otherwise. -/
noncomputable
def cmOfBounded (μ : Measure E) [HasTwoMoments μ] (y : E)
    [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)] :
    cameronMartin μ :=
  if hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M
    then (InnerProductSpace.toDual ℝ (cameronMartin μ)).symm (cmEval μ y hy)
    else 0

variable [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

lemma cmOfBounded_def (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    cmOfBounded μ y = (InnerProductSpace.toDual ℝ (cameronMartin μ)).symm (cmEval μ y hy) := by
  simp [cmOfBounded, hy]

lemma cmEval_apply (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) (x : cameronMartin μ) :
    cmEval μ y hy x = ⟪x, cmOfBounded μ y⟫_ℝ := by
  rw [cmOfBounded_def hy, real_inner_comm, InnerProductSpace.toDual_symm_apply]

end cmOfBounded

section CmCoe

/-! We build an injective continuous linear map from the Cameron-Martin space to the elements
of `E` with finite Cameron-Martin norm. This is an inverse of `CameronMartin.cmOfBounded`. -/

variable [SecondCountableTopology E] [HasTwoMoments μ]

namespace CameronMartinAux -- namespace for auxiliary definitions and lemmas

/-- From `x` in the image of `Dual ℝ E` by `Dual.centeredToLp μ 2`, we define a point of `E` by
`∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ` for an arbitrary `L : StrongDual ℝ E` with
`Dual.centeredToLp μ 2 L = x`.
This is an auxiliary definition for `CameronMartin.cmCoe`. -/
noncomputable
def toInit (μ : Measure E) [IsFiniteMeasure μ]
    (x : LinearMap.range (StrongDual.centeredToLp μ 2)) : E :=
  ∫ y, (LinearMap.mem_range.mp x.2).choose (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ

omit [SecondCountableTopology E] in
lemma toInit_eq (x : LinearMap.range (StrongDual.centeredToLp μ 2)) {L : StrongDual ℝ E}
    (hL : StrongDual.centeredToLp μ 2 L = x) :
    toInit μ x = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ :=
  calc toInit μ x
  _ = ∫ y, x.1 y • (y - ∫ z, z ∂μ) ∂μ := by
    rw [toInit]
    conv_rhs => rw [← (LinearMap.mem_range.mp x.2).choose_spec]
    refine integral_congr_ae ?_
    filter_upwards [centeredToLp_apply memLp_two_id (LinearMap.mem_range.mp x.2).choose] with y hy
    rw [hy]
  _ = ∫ y, StrongDual.centeredToLp μ 2 L y • (y - ∫ z, z ∂μ) ∂μ := by rw [hL]
  _ = ∫ y, L (y - ∫ z, z ∂μ) • (y - ∫ z, z ∂μ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [centeredToLp_apply memLp_two_id L] with y hy using by rw [hy]

lemma apply_toInit (x : LinearMap.range (StrongDual.centeredToLp μ 2)) (L : StrongDual ℝ E) :
    L (toInit μ x)
      = ∫ y, (LinearMap.mem_range.mp x.2).choose (y - ∫ z, z ∂μ) * L (y - ∫ z, z ∂μ) ∂μ := by
  rw [toInit, ← L.integral_comp_comm]
  · simp
  rw [← integrable_norm_iff (by fun_prop)]
  simp only [map_sub, norm_smul]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · rw [memLp_norm_iff (by fun_prop)]
    exact (ContinuousLinearMap.memLp_two _).sub (memLp_const _)
  · rw [memLp_norm_iff (by fun_prop)]
    exact MemLp.sub memLp_two_id (memLp_const _)

lemma apply_toInit_eq_inner (x : LinearMap.range (StrongDual.centeredToLp μ 2))
    (L : StrongDual ℝ E) :
    L (toInit μ x) = ⟪StrongDual.centeredToLp μ 2 L, x⟫_ℝ := by
  rw [← (LinearMap.mem_range.mp x.2).choose_spec, L2.inner_def, apply_toInit]
  simp only [RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [centeredToLp_apply memLp_two_id L,
    centeredToLp_apply memLp_two_id (LinearMap.mem_range.mp x.2).choose]
    with y hy₁ hy₂
  rw [hy₁, hy₂]

lemma norm_toInit_le (x : LinearMap.range (StrongDual.centeredToLp μ 2)) :
    ‖toInit μ x‖ ≤ ‖StrongDual.centeredToLp μ 2‖ * ‖x‖ := by
  refine norm_le_dual_bound ℝ _ (by positivity) fun L ↦ ?_
  calc ‖L (toInit μ x)‖
  _ = ‖⟪StrongDual.centeredToLp μ 2 L, x⟫_ℝ‖ := by rw [apply_toInit_eq_inner]
  _ ≤ ‖StrongDual.centeredToLp μ 2 L‖ * ‖x‖ :=
    norm_inner_le_norm ((StrongDual.centeredToLp μ 2) L) x
  _ ≤ ‖StrongDual.centeredToLp μ 2‖ * ‖L‖ * ‖x‖ := by
    gcongr
    exact (StrongDual.centeredToLp μ 2).le_opNorm L
  _ = ‖StrongDual.centeredToLp μ 2‖ * ‖x‖ * ‖L‖ := by ring

end CameronMartinAux

open CameronMartinAux

/-- Continuous linear map from the Cameron-Martin space of a Gaussian measure to the space on
which that measure is defined. This map is injective: see `cmCoe_injective`.
Therefore, we can see the Cameron-Martin space as a subspace of the initial space, with a different
norm. -/
noncomputable
def cmCoe {μ : Measure E} [HasTwoMoments μ] : cameronMartin μ →L[ℝ] E :=
  closureExtensionCLM (LinearMap.range (StrongDual.centeredToLp μ 2)) <|
  LinearMap.mkContinuous
    { toFun x := toInit μ x
      map_add' x y := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_add, apply_toInit_eq_inner, Submodule.coe_add, inner_add_right]
      map_smul' r x := by
        refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
        simp_rw [map_smul, apply_toInit_eq_inner, Submodule.coe_smul, inner_smul_right]
        simp }
    ‖StrongDual.centeredToLp μ 2‖ norm_toInit_le

lemma apply_cmCoe_eq_inner (x : cameronMartin μ) (L : StrongDual ℝ E) :
    L (cmCoe x) = ⟪cmOfDual μ L, x⟫_ℝ := by
  rw [cmOfDual_apply]
  unfold cameronMartin
  simp only [cmCoe, closureExtensionCLM_apply]
  revert x
  rw [← funext_iff]
  refine funext_topologicalClosure (by fun_prop) (by fun_prop) fun x ↦ ?_
  rw [closureExtension_coe]
  swap; · exact ContinuousLinearMap.uniformContinuous _
  simp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [apply_toInit_eq_inner]
  rfl

lemma eq_zero_of_cmCoe_eq_zero {x : cameronMartin μ}
    (h : cmCoe x = 0) :
    x = 0 := by
  suffices ∀ y : cameronMartin μ, ⟪y, x⟫_ℝ = 0 by
    rw [← inner_self_eq_zero (𝕜 := ℝ) (x := x)]
    exact this x
  rw [← funext_iff]
  refine funext_topologicalClosure (by fun_prop) (by fun_prop) fun L ↦ ?_
  obtain ⟨L', hL'⟩ := LinearMap.mem_range.mp L.2
  have : cmOfDual μ L' = L := by rw [cmOfDual_apply]; congr
  rw [← this, ← apply_cmCoe_eq_inner, h]
  simp

lemma cmCoe_injective : Function.Injective (cmCoe (μ := μ)) := by
  intro x y h
  rw [← sub_eq_zero, ← map_sub] at h
  rw [← sub_eq_zero, eq_zero_of_cmCoe_eq_zero h]

/-- Any point of the Cameron-Martin space has finite Cameron-Martin norm
`⨆ L (_ : Var[L; μ] ≤ 1), L x` (when seen as a point of the initial space). -/
lemma apply_cmCoe_le_norm (x : cameronMartin μ)
    {L : StrongDual ℝ E} (hL : Var[L; μ] ≤ 1) :
    L (cmCoe x) ≤ ‖x‖ := by
  calc L (cmCoe x)
  _ = ⟪cmOfDual μ L, x⟫_ℝ := apply_cmCoe_eq_inner x L
  _ ≤ ‖cmOfDual μ L‖ * ‖x‖ := real_inner_le_norm (cmOfDual μ L) x
  _ = √Var[L; μ] * ‖x‖ := by rw [norm_cmOfDual]
  _ ≤ 1 * ‖x‖ := by gcongr; exact Real.sqrt_le_one.mpr hL
  _ = ‖x‖ := by rw [one_mul]

end CmCoe

variable [SecondCountableTopology E] [HasTwoMoments μ]
  [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]

@[simp]
lemma cmCoe_cmOfBounded (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    cmCoe (cmOfBounded μ y) = y := by
  refine (eq_iff_forall_dual_eq (𝕜 := ℝ)).mpr fun L ↦ ?_
  rw [← cmEval_cmOfDual hy, apply_cmCoe_eq_inner, cmEval_apply]

@[simp]
lemma cmOfBounded_cmCoe (x : cameronMartin μ)
    [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L (cmCoe x) ≤ M)] :
    cmOfBounded μ (cmCoe x) = x := by
  refine cmCoe_injective ?_
  rw [cmCoe_cmOfBounded ⟨‖x‖, fun _ hL ↦ apply_cmCoe_le_norm x hL⟩]

lemma range_cmCoe :
    Set.range (cmCoe (μ := μ))
      = {y : E | ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨‖x‖, fun L hL ↦ apply_cmCoe_le_norm x hL⟩
  · rintro hy
    classical
    refine ⟨cmOfBounded μ y, ?_⟩
    rw [cmCoe_cmOfBounded hy]

lemma cmOfDual_inner_le_of_norm_cmOfDual_le (x : cameronMartin μ) {L : StrongDual ℝ E}
    (hL : ‖cmOfDual μ L‖ ≤ 1) :
    ⟪cmOfDual μ L, x⟫_ℝ ≤ ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  refine le_ciSup_of_le ?_ L ?_
  · refine ⟨‖x‖, ?_⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro L
    by_cases hL : Var[L; μ] ≤ 1
    · simpa [hL] using apply_cmCoe_le_norm x hL
    · simp [hL]
  have hL' : Var[L; μ] ≤ 1 := by rwa [norm_cmOfDual, Real.sqrt_le_one] at hL
  simp only [hL', ciSup_unique]
  rw [← apply_cmCoe_eq_inner]

lemma cmOfDual_inner_le_mul (x : cameronMartin μ) (L : StrongDual ℝ E) :
    ⟪cmOfDual μ L, x⟫_ℝ
      ≤ ‖cmOfDual μ L‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  by_cases h_zero : ‖cmOfDual μ L‖ = 0
  · simp only [h_zero, zero_mul]
    rw [inner_eq_zero_of_left _ h_zero]
  have h := cmOfDual_inner_le_of_norm_cmOfDual_le x (L := ‖cmOfDual μ L‖⁻¹ • L) ?_
  · simp only [map_smul, inner_smul_left, map_inv₀, conj_trivial] at h
    rwa [inv_mul_le_iff₀ (by positivity)] at h
  · simp only [map_smul, norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one

lemma inner_cameronMartin_le_mul_ciSup (x y : cameronMartin μ) :
    ⟪y, x⟫_ℝ ≤ ‖y‖ * ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  induction y using induction_topologicalClosure with
  | hp =>
    exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a =>
    obtain ⟨L, hL⟩ := LinearMap.mem_range.mp a.2
    have : (a : cameronMartin μ) = cmOfDual μ L := by
      simp_rw [cmOfDual_apply, hL]
    rw [this]
    exact cmOfDual_inner_le_mul x L

lemma norm_cameronMartin_eq_ciSup (x : cameronMartin μ) :
    ‖x‖ = ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L (cmCoe x) := by
  refine le_antisymm ?_ ?_
  · refine InnerProductSpace.norm_le_dual_bound x ?_ fun y ↦ ?_
    · by_cases h_bdd :
        BddAbove (Set.range fun L : StrongDual ℝ E ↦ ⨆ (_ : Var[L; μ] ≤ 1), L (cmCoe x))
      · exact le_ciSup_of_le h_bdd 0 (by simp)
      · simp [h_bdd]
    rw [real_inner_comm, mul_comm]
    exact inner_cameronMartin_le_mul_ciSup x y
  · refine ciSup_le fun L ↦ ?_
    by_cases hL : Var[L; μ] ≤ 1
    · simpa [hL] using apply_cmCoe_le_norm x hL
    · simp [hL]

lemma norm_cmOfBounded {y : E} [Decidable (∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M)]
    (hy : ∃ M, ∀ L : StrongDual ℝ E, Var[L; μ] ≤ 1 → L y ≤ M) :
    ‖cmOfBounded μ y‖ = ⨆ (L : StrongDual ℝ E) (_ : Var[L; μ] ≤ 1), L y := by
  rw [norm_cameronMartin_eq_ciSup]
  simp [cmCoe_cmOfBounded hy]

end ProbabilityTheory
