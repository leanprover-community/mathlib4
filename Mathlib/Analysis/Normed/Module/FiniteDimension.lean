/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Normed.Group.Lemmas
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.Topology.Algebra.AffineSubspace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Finite-dimensional normed spaces over complete fields

Over a complete nontrivially normed field, in finite dimension, all norms are equivalent and all
linear maps are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `FiniteDimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `Submodule.closed_of_finiteDimensional` : a finite-dimensional subspace over a complete field is
  closed
* `FiniteDimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `FiniteDimensional.complete` on `ℝ` or
  `ℂ`.
* `FiniteDimensional.of_isCompact_closedBall`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'` to `E` are continuous thanks to
`LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence.
-/

@[expose] public section

universe u v w x

noncomputable section

open Asymptotics Filter Module Metric Module NNReal Set TopologicalSpace Topology

namespace LinearIsometry

open LinearMap

variable {F E₁ : Type*} [SeminormedAddCommGroup F] [NormedAddCommGroup E₁]
variable {R₁ : Type*} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁]
  [FiniteDimensional R₁ F]

/-- A linear isometry between finite-dimensional spaces of equal dimension can be upgraded
to a linear isometry equivalence. -/
def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    E₁ ≃ₗᵢ[R₁] F where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.injective h
  norm_map' := li.norm_map'

@[simp]
theorem coe_toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ → F) = li :=
  rfl

@[simp]
theorem toLinearIsometryEquiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
    (x : E₁) : (li.toLinearIsometryEquiv h) x = li x :=
  rfl

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type*} {V₁ V₂ : Type*} {P₁ P₂ : Type*} [NormedField 𝕜] [NormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

/-- An affine isometry between finite-dimensional spaces of equal dimension can be upgraded
to an affine isometry equivalence. -/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.linearIsometry.toLinearIsometryEquiv h)
    (Inhabited.default (α := P₁)) fun p => by simp

@[simp]
theorem coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ → P₂) = li :=
  rfl

@[simp]
theorem toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x :=
  rfl

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type*} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF]
  [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]

theorem AffineMap.continuous_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional

theorem AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finiteDimensional

/-- Reinterpret an affine equivalence as a homeomorphism. -/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF where
  toEquiv := f.toEquiv
  continuous_toFun := f.continuous_of_finiteDimensional
  continuous_invFun :=
    haveI : FiniteDimensional 𝕜 F := f.linear.finiteDimensional
    f.symm.continuous_of_finiteDimensional

@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl

@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl

/-- An affine map from a finite-dimensional space is automatically Lipschitz. -/
theorem AffineMap.lipschitzWith_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  let fL : E →L[𝕜] F := f.linear.toContinuousLinearMap
  refine ⟨‖fL‖₊, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  rw [NormedAddTorsor.dist_eq_norm', NormedAddTorsor.dist_eq_norm', ← f.linearMap_vsub]
  exact fL.le_opNorm _

end Affine

theorem ContinuousLinearMap.continuous_det : Continuous fun f : E →L[𝕜] E => f.det := by
  change Continuous fun f : E →L[𝕜] E => LinearMap.det (f : E →ₗ[𝕜] E)
  -- TODO: this could be easier with `det_cases`
  by_cases h : ∃ s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    haveI : FiniteDimensional 𝕜 E := b.finiteDimensional_of_finite
    classical
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine Continuous.matrix_det ?_
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · rw [LinearMap.det]
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitzExtensionConstant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1

theorem lipschitzExtensionConstant_pos (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] : 0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]
  exact zero_lt_one.trans_le (le_max_right _ _)

/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitzExtensionConstant E' * K`. -/
theorem LipschitzOnWith.extend_finite_dimension {α : Type*} [PseudoMetricSpace α] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {s : Set α} {f : α → E'}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s := by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ E'
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.toContinuousLinearMap‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.toContinuousLinearMap‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitzOnWith hf
  obtain ⟨g, hg, gs⟩ :
    ∃ g : α → ι → ℝ, LipschitzWith (‖A.toContinuousLinearMap‖₊ * K) g ∧ EqOn (A ∘ f) g s :=
    L.extend_pi
  refine ⟨A.symm ∘ g, ?_, ?_⟩
  · have LAsymm : LipschitzWith ‖A.symm.toContinuousLinearMap‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant, ← mul_assoc]
    exact mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]

theorem LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F)
    (hf : LinearMap.ker f = ⊥) : ∃ K > 0, AntilipschitzWith K f := by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] LinearMap.range f := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩

open Function in
/-- A `LinearMap` on a finite-dimensional space over a complete field
  is injective iff it is anti-Lipschitz. -/
theorem LinearMap.injective_iff_antilipschitz [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F) :
    Injective f ↔ ∃ K > 0, AntilipschitzWith K f := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact f.exists_antilipschitzWith
  · rintro ⟨K, -, H⟩
    exact H.injective

/-- An injective affine map from a finite-dimensional space is automatically anti-Lipschitz. -/
theorem AffineMap.antilipschitzWith_of_finiteDimensional {PE PF : Type*} [MetricSpace PE]
    [NormedAddTorsor E PE] [MetricSpace PF] [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]
    {f : PE →ᵃ[𝕜] PF} (hf : Function.Injective f) :
    ∃ K : ℝ≥0, AntilipschitzWith K f := by
  obtain ⟨K, -, hK⟩ := f.linear.injective_iff_antilipschitz.mp (f.linear_injective_iff.mpr hf)
  refine ⟨K, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  rw [dist_eq_norm_vsub E, dist_eq_norm_vsub F, ← f.linearMap_vsub]
  exact ZeroHomClass.bound_of_antilipschitz f.linear hK (x -ᵥ y)

open Function in
/-- The set of injective continuous linear maps `E → F` is open,
  if `E` is finite-dimensional over a complete field. -/
theorem ContinuousLinearMap.isOpen_injective [FiniteDimensional 𝕜 E] :
    IsOpen { L : E →L[𝕜] F | Injective L } := by
  rw [isOpen_iff_eventually]
  rintro φ₀ hφ₀
  rcases φ₀.injective_iff_antilipschitz.mp hφ₀ with ⟨K, K_pos, H⟩
  have : ∀ᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ := eventually_nnnorm_sub_lt _ <| inv_pos_of_pos K_pos
  filter_upwards [this] with φ hφ
  apply φ.injective_iff_antilipschitz.mpr
  exact ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ),
    H.add_sub_lipschitzWith (φ - φ₀).lipschitz hφ⟩

protected theorem LinearIndependent.eventually {ι} [Finite ι] {f : ι → E}
    (hf : LinearIndependent 𝕜 f) : ∀ᶠ g in 𝓝 f, LinearIndependent 𝕜 g := by
  cases nonempty_fintype ι
  classical
  simp only [Fintype.linearIndependent_iff'] at hf ⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : Tendsto (fun g : ι → E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finset_sum _ fun i _ =>
      Tendsto.norm <| ((continuous_apply i).tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => ?_
  replace hg : ∑ i, ‖g i - f i‖₊ < K⁻¹ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact hg
  rw [LinearMap.ker_eq_bot]
  refine (hK.add_sub_lipschitzWith (LipschitzWith.of_dist_le_mul fun v u => ?_) hg).injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_smul, mul_comm]
  gcongr
  exact norm_le_pi_norm (v - u) i

theorem isOpen_setOf_linearIndependent {ι : Type*} [Finite ι] :
    IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  isOpen_iff_mem_nhds.2 fun _ => LinearIndependent.eventually

theorem isOpen_setOf_nat_le_rank (n : ℕ) :
    IsOpen { f : E →L[𝕜] F | ↑n ≤ (f : E →ₗ[𝕜] F).rank } := by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, setOf_exists, ← exists_prop]
  refine isOpen_biUnion fun t _ => ?_
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).continuous
  exact isOpen_setOf_linearIndependent.preimage this

theorem isOpen_setOf_affineIndependent {ι : Type*} [Finite ι] :
    IsOpen {p : ι → E | AffineIndependent 𝕜 p} := by
  classical
  rcases isEmpty_or_nonempty ι with h | ⟨⟨i₀⟩⟩
  · exact isOpen_discrete _
  · simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
    let ι' := { x // x ≠ i₀ }
    cases nonempty_fintype ι
    haveI : Fintype ι' := Subtype.fintype _
    convert_to
      IsOpen ((fun (p : ι → E) (i : ι') ↦ p i -ᵥ p i₀) ⁻¹' {p : ι' → E | LinearIndependent 𝕜 p})
    exact isOpen_setOf_linearIndependent.preimage (by fun_prop)

namespace Module.Basis

theorem opNNNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0)
    (hu : ∀ i, ‖u (v i)‖₊ ≤ M) : ‖u‖₊ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊ * M :=
  u.opNNNorm_le_bound _ fun e => by
    set φ := v.equivFunL.toContinuousLinearMap
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equivFun e i • v i)‖₊ := by rw [v.sum_equivFun]
      _ = ‖∑ i, v.equivFun e i • (u <| v i)‖₊ := by simp only [equivFun_apply, map_sum, map_smul]
      _ ≤ ∑ i, ‖v.equivFun e i • (u <| v i)‖₊ := nnnorm_sum_le _ _
      _ = ∑ i, ‖v.equivFun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ ≤ ∑ i, ‖v.equivFun e i‖₊ * M := by gcongr; apply hu
      _ = (∑ i, ‖v.equivFun e i‖₊) * M := by rw [Finset.sum_mul]
      _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M := by
        gcongr
        calc
          ∑ i, ‖v.equivFun e i‖₊ ≤ Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_right (φ.le_opNNNorm e) _
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]

theorem opNorm_le {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (v i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖ * M := by
  simpa using NNReal.coe_le_coe.mpr (v.opNNNorm_le ⟨M, hM⟩ hu)

/-- A weaker version of `Basis.opNNNorm_le` that abstracts away the value of `C`. -/
theorem exists_opNNNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ≥0), ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ i, ‖u (v i)‖₊ ≤ M) → ‖u‖₊ ≤ C * M := by
  cases nonempty_fintype ι
  exact
    ⟨max (Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊) 1,
      zero_lt_one.trans_le (le_max_right _ _), fun {u} M hu =>
      (v.opNNNorm_le M hu).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le M)⟩

/-- A weaker version of `Basis.opNorm_le` that abstracts away the value of `C`. -/
theorem exists_opNorm_le {ι : Type*} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖u (v i)‖ ≤ M) → ‖u‖ ≤ C * M := by
  obtain ⟨C, hC, h⟩ := v.exists_opNNNorm_le (F := F)
  refine ⟨C, hC, ?_⟩
  intro u M hM H
  simpa using h ⟨M, hM⟩ H

end Module.Basis

instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] :
    SecondCountableTopology (E →L[𝕜] F) := by
  set d := Module.finrank 𝕜 E
  suffices
    ∀ ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → Fin d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε from
    Metric.secondCountable_of_countable_discretization fun ε ε_pos =>
      ⟨Fin d → ℕ, by infer_instance, this ε ε_pos⟩
  intro ε ε_pos
  obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F
  let v := Module.finBasis 𝕜 E
  obtain
    ⟨C : ℝ, C_pos : 0 < C, hC :
      ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖φ (v i)‖ ≤ M) → ‖φ‖ ≤ C * M⟩ :=
    v.exists_opNorm_le (E := E) (F := F)
  have h_2C : 0 < 2 * C := mul_pos zero_lt_two C_pos
  have hε2C : 0 < ε / (2 * C) := div_pos ε_pos h_2C
  have : ∀ φ : E →L[𝕜] F, ∃ n : Fin d → ℕ, ‖φ - (v.constrL <| u ∘ n)‖ ≤ ε / 2 := by
    intro φ
    have : ∀ i, ∃ n, ‖φ (v i) - u n‖ ≤ ε / (2 * C) := by
      simp only [norm_sub_rev]
      intro i
      have : φ (v i) ∈ closure (range u) := hu _
      obtain ⟨n, hn⟩ : ∃ n, ‖u n - φ (v i)‖ < ε / (2 * C) := by
        rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this
        specialize this (ε / (2 * C)) hε2C
        simpa [dist_eq_norm]
      exact ⟨n, le_of_lt hn⟩
    choose n hn using this
    use n
    replace hn : ∀ i : Fin d, ‖(φ - (v.constrL <| u ∘ n)) (v i)‖ ≤ ε / (2 * C) := by simp [hn]
    have : C * (ε / (2 * C)) = ε / 2 := by
      rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc,
        mul_div_cancel₀ _ (ne_of_gt h_2C)]
    specialize hC (le_of_lt hε2C) hn
    rwa [this] at hC
  choose n hn using this
  set Φ := fun φ : E →L[𝕜] F => v.constrL <| u ∘ n φ
  change ∀ z, dist z (Φ z) ≤ ε / 2 at hn
  use n
  intro x y hxy
  calc
    dist x y ≤ dist x (Φ x) + dist (Φ x) y := dist_triangle _ _ _
    _ = dist x (Φ x) + dist y (Φ y) := by simp [Φ, hxy, dist_comm]
    _ ≤ ε := by linarith [hn x, hn y]

theorem AffineSubspace.closed_of_finiteDimensional {P : Type*} [MetricSpace P]
    [NormedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) :=
  s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional

section Riesz

/-- In an infinite-dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y ∈ s, 1 ≤ ‖y - x‖ := by
  let F := Submodule.span 𝕜 (s : Set E)
  have hF : F.FG := ⟨s, rfl⟩
  haveI : FiniteDimensional 𝕜 F := .of_fg hF
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by
      ext x
      simp [h]
    rw [← this] at hF
    exact .of_fg_top hF
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ‖y - x‖ := by
    intro y hy
    rw [← norm_neg]
    simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩

/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖f m - f n‖ := by
  have : Std.Symm fun x y : E => 1 ≤ ‖x - y‖ := by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ ≤ R) fun (x : E) (y : E) => 1 ≤ ‖x - y‖
  rintro s -
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s

theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖f m - f n‖ := by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩

variable (𝕜)

/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
theorem FiniteDimensional.of_isCompact_closedBall₀ {r : ℝ} (rpos : 0 < r)
    (h : IsCompact (Metric.closedBall (0 : E) r)) : FiniteDimensional 𝕜 E := by
  by_contra hfin
  obtain ⟨R, f, Rgt, fle, lef⟩ :
    ∃ (R : ℝ) (f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ Pairwise fun m n => 1 ≤ ‖f m - f n‖ :=
    exists_seq_norm_le_one_le_norm_sub hfin
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt)
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < r / R := NormedField.exists_norm_lt _ rRpos
  let g := fun n : ℕ => c • f n
  have A : ∀ n, g n ∈ Metric.closedBall (0 : E) r := by
    intro n
    simp only [g, norm_smul, dist_zero_right, Metric.mem_closedBall]
    calc
      ‖c‖ * ‖f n‖ ≤ r / R * R := by
        gcongr
        · exact hc.2.le
        · apply fle
      _ = r := by simp [(zero_lt_one.trans Rgt).ne']
  obtain ⟨x : E, _ : x ∈ Metric.closedBall (0 : E) r, φ : ℕ → ℕ, φmono : StrictMono φ,
    φlim : Tendsto (g ∘ φ) atTop (𝓝 x)⟩ := h.tendsto_subseq A
  have B : CauchySeq (g ∘ φ) := φlim.cauchySeq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ‖c‖ :=
    Metric.cauchySeq_iff'.1 B ‖c‖ hc.1
  apply lt_irrefl ‖c‖
  calc
    ‖c‖ ≤ dist (g (φ (N + 1))) (g (φ N)) := by
      conv_lhs => rw [← mul_one ‖c‖]
      simp only [g, dist_eq_norm, ← smul_sub, norm_smul]
      gcongr
      apply lef (ne_of_gt _)
      exact φmono (Nat.lt_succ_self N)
    _ < ‖c‖ := hN (N + 1) (Nat.le_succ N)

/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
theorem FiniteDimensional.of_isCompact_closedBall {r : ℝ} (rpos : 0 < r) {c : E}
    (h : IsCompact (Metric.closedBall c r)) : FiniteDimensional 𝕜 E :=
  .of_isCompact_closedBall₀ 𝕜 rpos <| by simpa using h.vadd (-c)

/-- **Riesz's theorem**: a locally compact normed vector space is finite-dimensional. -/
theorem FiniteDimensional.of_locallyCompactSpace [LocallyCompactSpace E] :
    FiniteDimensional 𝕜 E :=
  let ⟨_r, rpos, hr⟩ := exists_isCompact_closedBall (0 : E)
  .of_isCompact_closedBall₀ 𝕜 rpos hr

/-- If a function has compact support, then either the function is trivial
or the space is finite-dimensional. -/
theorem HasCompactSupport.eq_zero_or_finiteDimensional {X : Type*} [TopologicalSpace X] [Zero X]
    [T1Space X] {f : E → X} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ FiniteDimensional 𝕜 E :=
  (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h ↦
    -- TODO: Lean doesn't find the instance without this `have`
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

/-- If a function has compact multiplicative support, then either the function is trivial
or the space is finite-dimensional. -/
@[to_additive existing]
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*} [TopologicalSpace X] [One X]
    [T1Space X] {f : E → X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E :=
  have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional (X := Additive X) 𝕜 hf h'f

/-- A locally compact normed vector space is proper. -/
lemma ProperSpace.of_locallyCompactSpace (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] :
    ProperSpace E := by
  rcases exists_isCompact_closedBall (0 : E) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : ∀ n, IsCompact (closedBall (0 : E) (‖c‖ ^ n * r)) := fun n ↦ by
    have : c ^ n ≠ 0 := pow_ne_zero _ <| fun h ↦ by simp [h, zero_le_one.not_gt] at hc
    simpa [_root_.smul_closedBall' this] using hr.smul (c ^ n)
  have hTop : Tendsto (fun n ↦ ‖c‖ ^ n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)

variable (E)
lemma ProperSpace.of_locallyCompact_module [Nontrivial E] [LocallyCompactSpace E] :
    ProperSpace 𝕜 :=
  have : LocallyCompactSpace 𝕜 := by
    obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := exists_ne 0
    let L : 𝕜 → E := fun t ↦ t • v
    have : IsClosedEmbedding L := isClosedEmbedding_smul_left hv
    apply IsClosedEmbedding.locallyCompactSpace this
  .of_locallyCompactSpace 𝕜

end Riesz

open ContinuousLinearMap

/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
def ContinuousLinearEquiv.piRing (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  { LinearMap.toContinuousLinearMap.symm.trans (LinearEquiv.piRing 𝕜 E ι 𝕜) with
    continuous_toFun := by
      refine continuous_pi fun i => ?_
      exact (ContinuousLinearMap.apply 𝕜 E (Pi.single i 1)).continuous
    continuous_invFun := by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      -- Note: added explicit type and removed `change` that tried to achieve the same
      refine AddMonoidHomClass.continuous_of_bound
        (LinearMap.toContinuousLinearMap.toLinearMap.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
        (Fintype.card ι : ℝ) fun g => ?_
      rw [← nsmul_eq_mul]
      refine opNorm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => ?_
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_toContinuousLinearMap', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_
      rw [norm_smul, mul_comm]
      gcongr <;> apply norm_le_pi_norm }

/-- A family of continuous linear maps is continuous on `s` if all its applications are. -/
theorem continuousOn_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {s : Set X} : ContinuousOn f s ↔ ∀ y, ContinuousOn (fun x => f x y) s := by
  refine ⟨fun h y => (ContinuousLinearMap.apply 𝕜 F y).continuous.comp_continuousOn h, fun h => ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ : E ≃L[𝕜] Fin d → 𝕜 := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] Fin d → F :=
    (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← f.id_comp, ← e₂.symm_comp_self]
  exact e₂.symm.continuous.comp_continuousOn (continuousOn_pi.mpr fun i => h _)

theorem continuous_clm_apply {X : Type*} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} : Continuous f ↔ ∀ y, Continuous (f · y) := by
  simp_rw [← continuousOn_univ, continuousOn_clm_apply]

end CompleteField

section LocallyCompactField

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (E : Type v) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [LocallyCompactSpace 𝕜]

/-- Any finite-dimensional vector space over a locally compact field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E := by
  have : ProperSpace 𝕜 := .of_locallyCompactSpace 𝕜
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.properSpace e.symm.continuous e.symm.surjective

end LocallyCompactField

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ProperSpace E :=
  FiniteDimensional.proper ℝ E

/-- A submodule of a locally compact space over a complete field is also locally compact (and even
proper). -/
instance {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E] (S : Submodule 𝕜 E) :
    ProperSpace S := by
  nontriviality E
  have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  exact FiniteDimensional.proper 𝕜 S

/-- If `E` is a finite-dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`Metric.infDist x sᶜ` from `x`. See also
`IsCompact.exists_mem_frontier_infDist_compl_eq_dist`. -/
theorem exists_mem_frontier_infDist_compl_eq_dist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x : E} {s : Set E} (hx : x ∈ s) (hs : s ≠ univ) :
    ∃ y ∈ frontier s, Metric.infDist x sᶜ = dist x y := by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
  refine ⟨y, ⟨Metric.closedBall_infDist_compl_subset_closure hx <|
    Metric.mem_closedBall.2 <| ge_of_eq ?_, hys⟩, hyd⟩
  rwa [dist_comm]

/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `Metric.infDist x Kᶜ` from `x`. See also
`exists_mem_frontier_infDist_compl_eq_dist`. -/
nonrec theorem IsCompact.exists_mem_frontier_infDist_compl_eq_dist {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K)
    (hx : x ∈ K) :
    ∃ y ∈ frontier K, Metric.infDist x Kᶜ = dist x y := by
  obtain hx' | hx' : x ∈ interior K ∪ frontier K := by
    rw [← closure_eq_interior_union_frontier]
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, Metric.nhds_basis_closedBall.mem_iff] at hx'
    rcases hx' with ⟨r, hr₀, hrK⟩
    have : FiniteDimensional ℝ E :=
      .of_isCompact_closedBall ℝ hr₀
        (hK.of_isClosed_subset Metric.isClosed_closedBall hrK)
    exact exists_mem_frontier_infDist_compl_eq_dist hx hK.ne_univ
  · refine ⟨x, hx', ?_⟩
    rw [frontier_eq_closure_inter_closure] at hx'
    rw [Metric.infDist_zero_of_mem_closure hx'.2, dist_self]

/-- In a finite-dimensional vector space over `ℝ`, the series `∑ x, ‖f x‖` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite-dimensional spaces. -/
theorem summable_norm_iff {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : α → E} : (Summable fun x => ‖f x‖) ↔ Summable f := by
  refine ⟨Summable.of_norm, fun hf ↦ ?_⟩
  -- First we use a finite basis to reduce the problem to the case `E = Fin N → ℝ`
  suffices ∀ {N : ℕ} {g : α → Fin N → ℝ}, Summable g → Summable fun x => ‖g x‖ by
    obtain v := Module.finBasis ℝ E
    set e := v.equivFunL
    have H : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine .of_norm_bounded (H.mul_left ↑‖(e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E)‖₊) fun i ↦ ?_
    simpa using (e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_opNorm (e <| f i)
  clear! E
  -- Now we deal with `g : α → Fin N → ℝ`
  intro N g hg
  have : ∀ i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine .of_norm_bounded (summable_sum fun i (_ : i ∈ Finset.univ) => this i) fun x => ?_
  rw [norm_norm, pi_norm_le_iff_of_nonneg]
  · refine fun i => Finset.single_le_sum (f := fun i => ‖g x i‖) (fun i _ => ?_) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

alias ⟨_, Summable.norm⟩ := summable_norm_iff

theorem summable_of_sum_range_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {c : ℝ} {f : ℕ → E} (h : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ c) :
    Summable f :=
  summable_norm_iff.mp <| summable_of_sum_range_le (fun _ ↦ norm_nonneg _) h

theorem summable_of_isBigO' {ι E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_isBigO hg.norm h.norm_right

lemma Asymptotics.IsBigO.comp_summable {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [CompleteSpace F]
    {f : E → F} (hf : f =O[𝓝 0] id) {g : ι → E} (hg : Summable g) : Summable (f ∘ g) :=
  .of_norm <| hf.comp_summable_norm hg.norm

theorem summable_of_isBigO_nat' {E F : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO_nat hg.norm h.norm_right


open Nat Asymptotics in
/-- This is a version of `summable_norm_mul_geometric_of_norm_lt_one` for more general codomains. We
keep the original one due to import restrictions. -/
theorem summable_norm_mul_geometric_of_norm_lt_one' {F : Type*} [NormedRing F]
    [NormOneClass F] [NormMulClass F] {k : ℕ} {r : F} (hr : ‖r‖ < 1) {u : ℕ → F}
    (hu : u =O[atTop] fun n ↦ ((n ^ k : ℕ) : F)) : Summable fun n : ℕ ↦ ‖u n * r ^ n‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h).norm
  calc
  fun n ↦ ‖(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ ‖u n‖ * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : ℝ)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp
  _ =O[atTop] fun n ↦ ‖((n : F) ^ k)‖ * ‖r‖ ^ n := by
      simpa [Nat.cast_pow] using
      (isBigO_norm_left.mpr (isBigO_norm_right.mpr hu)).mul (isBigO_refl (fun n ↦ (‖r‖ ^ n)) atTop)
  _ =O[atTop] fun n ↦ ‖r' ^ n‖ := by
      convert isBigO_norm_right.mpr (isBigO_norm_left.mpr
        (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO)
      simp only [norm_pow, norm_mul]

theorem summable_of_isEquivalent {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) :
    Summable f :=
  summable_of_isBigO' hg h.isBigO

theorem summable_of_isEquivalent_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (hg : Summable g) (h : f ~[atTop] g) :
    Summable f :=
  summable_of_isBigO_nat' hg h.isBigO

theorem Asymptotics.IsTheta.summable_iff {ι E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F} (h : f =Θ[cofinite] g) :
    Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isBigO' hf h.isBigO_symm, fun hg => summable_of_isBigO' hg h.isBigO⟩

theorem Asymptotics.IsTheta.summable_iff_nat {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F} (h : f =Θ[atTop] g) :
    Summable f ↔ Summable g :=
  IsTheta.summable_iff <| by simpa [← Nat.cofinite_eq_atTop] using h

theorem Asymptotics.IsEquivalent.summable_iff {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (h : f ~[cofinite] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff := Asymptotics.IsEquivalent.summable_iff

theorem Asymptotics.IsEquivalent.summable_iff_nat {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (h : f ~[atTop] g) :
    Summable f ↔ Summable g :=
  h.isTheta.summable_iff_nat

@[deprecated (since := "2026-02-07")]
alias IsEquivalent.summable_iff_nat := Asymptotics.IsEquivalent.summable_iff_nat

namespace Module.Basis

variable {ι R M : Type*} [Finite ι]
  [NontriviallyNormedField R] [CompleteSpace R]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]
  [Module R M] [ContinuousSMul R M] (B : Module.Basis ι R M)

-- Note that Finsupp has no topology so we need the coercion, see
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/TVS.20and.20NormedSpace.20on.20Finsupp.2C.20DFinsupp.2C.20DirectSum.2C.20.2E.2E/near/512890984
theorem continuous_coe_repr : Continuous (fun m : M => ⇑(B.repr m)) :=
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.equivFun.toLinearMap

-- Note: this could be generalized if we had some typeclass to indicate "each of the projections
-- into the basis is continuous".
theorem continuous_toMatrix : Continuous fun (v : ι → M) => B.toMatrix v :=
  let _ := Fintype.ofFinite ι
  have := Finite.of_basis B
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap

end Module.Basis
