/-
Copyright (c) 2026 E. S. Markov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E. S. Markov
-/
module

public import Mathlib.Analysis.Normed.Module.Proximinal

/-!
# Birkhoff–James Orthogonality, Linear Metric Selectors, and Lipschitz Stability

This file develops the geometric theory of continuous linear selections for multivalued metric
projections in normed spaces via Birkhoff–James orthogonality.

## Main definitions

* `BirkhoffOrthogonal`: Birkhoff–James orthogonality `x ⊥_B y`, meaning `‖x‖ ≤ ‖x + c • y‖` for
  all scalars `c`.
* `Submodule.BirkhoffOrthogonalTo`: orthogonality of an element `x` to a submodule `V`.
* `Submodule.LinearSelector`: a continuous linear operator `s : X →L[𝕜] X` mapping into `V` such
  that `s x ∈ V.metricProjection x` for every `x : X`.
* `Submodule.mutualInclination`: the mutual inclination (opening) coefficient `δ(V, U)` between
  two submodules.

## Main results

* `Submodule.birkhoffOrthogonalTo_iff_mem_metricProjectionZeroLayer`: equivalence between `u ⊥_B V`
  and `u ∈ P_V⁻¹(0)`.
* `Submodule.LinearSelector.isCompl_ker` & `Submodule.exists_linearSelector_of_isCompl`: Deutsch's
  structural splitting theorem characterizing the existence of a continuous linear selector via
  a closed complement `U ⊆ P_V⁻¹(0)`.
* `Submodule.LinearSelector.eq_of_subsingleton`: uniqueness of the linear selector for Chebyshev
  subspaces.
* `Submodule.LinearSelector.comp_of_commute`: stability of commuting linear selectors under
  subspace intersections.
* `Submodule.LinearSelector.opNorm_eq_inv_mutualInclination`: exact characterization of the
  global Lipschitz constant `L = ‖s‖ = 1 / δ(V, ker s)`.

## References

* E. S. Markov, *On Linear Metric Projections in Non-Reflexive Banach Spaces: Proximinal Lattices,
  Multivalued Boundaries and Linear Selections*, Zenodo (2026),
  [DOI: 10.5281/zenodo.24318041](https://doi.org).
* F. Deutsch, *Linear selections for the metric projection*, J. Functional Analysis 49 (1982),
  269–292.
-/

@[expose] public section

open Set Topology

section BirkhoffOrthogonality

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Birkhoff–James orthogonality `x ⊥_B y` in a normed space: `‖x‖ ≤ ‖x + c • y‖` for all
scalars `c : 𝕜`. -/
def BirkhoffOrthogonal (x y : X) : Prop :=
  ∀ c : 𝕜, ‖x‖ ≤ ‖x + c • y‖

/-- Birkhoff–James orthogonality of a vector `x : X` to a submodule `V`. -/
def Submodule.BirkhoffOrthogonalTo (V : Submodule 𝕜 X) (x : X) : Prop :=
  ∀ v ∈ V, @BirkhoffOrthogonal 𝕜 _ X _ _ x v

/-- An element `u : X` is Birkhoff–James orthogonal to a submodule `V` if and only if `u` lies in
the null layer `P_V⁻¹(0)` of the metric projection. -/
theorem Submodule.birkhoffOrthogonalTo_iff_mem_metricProjectionZeroLayer
    (V : Submodule 𝕜 X) (u : X) :
    V.BirkhoffOrthogonalTo u ↔ u ∈ V.metricProjectionZeroLayer := by
  refine ⟨fun h_orth => ⟨V.zero_mem, fun w hw => ?_⟩, fun h_zero v hv c => ?_⟩
  · rw [sub_zero]
    have h1 := h_orth (-w) (V.neg_mem hw) (1 : 𝕜)
    rwa [one_smul, ← sub_eq_add_neg] at h1
  · have h1 := h_zero.2 (-c • v) (V.smul_mem (-c) hv)
    rwa [sub_zero, neg_smul, sub_neg_eq_add] at h1

end BirkhoffOrthogonality

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A continuous linear selector for the multivalued metric projection onto a submodule `V`. -/
structure LinearSelector (V : Submodule 𝕜 X) where
  /-- The underlying continuous linear operator on `X`. -/
  toFun : X →L[𝕜] X
  /-- The range of the selector is contained in `V`. -/
  mem_subspace : ∀ x : X, toFun x ∈ V
  /-- For every `x : X`, `toFun x` is an element of best approximation in `V`. -/
  is_selection : ∀ x : X, toFun x ∈ V.metricProjection x

namespace LinearSelector

/-- A linear selector acts as the identity on elements of `V`. -/
lemma apply_eq_self {V : Submodule 𝕜 X} (s : LinearSelector V) {v : X} (hv : v ∈ V) :
    s.toFun v = v := by
  have h_sel := (s.is_selection v).2 v hv
  rw [sub_self, norm_zero] at h_sel
  have h_zero : ‖v - s.toFun v‖ = 0 := le_antisymm h_sel (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp h_zero)).symm

/-- Every linear selector is an idempotent projection operator. -/
lemma idempotent {V : Submodule 𝕜 X} (s : LinearSelector V) (x : X) :
    s.toFun (s.toFun x) = s.toFun x :=
  s.apply_eq_self (s.mem_subspace x)

/-- Deutsch's theorem (necessity): if `s` is a continuous linear selector onto `V`, then its
kernel `U = ker s` is a closed complement of `V` contained in the null layer `P_V⁻¹(0)`. -/
theorem isCompl_ker {V : Submodule 𝕜 X} (s : LinearSelector V) :
    let U : Submodule 𝕜 X := LinearMap.ker (s.toFun : X →ₗ[𝕜] X)
    IsClosed (U : Set X) ∧ IsCompl V U ∧ (U : Set X) ⊆ V.metricProjectionZeroLayer := by
  intro U
  refine ⟨isClosed_eq s.toFun.continuous continuous_const, ?_, ?_⟩
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    refine ⟨?_, ?_⟩
    · rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
      change x ∈ V ∧ s.toFun x = 0 at hx
      rw [← s.apply_eq_self hx.1, hx.2]
    · rw [Submodule.eq_top_iff']
      intro x
      rw [← add_sub_cancel (s.toFun x) x]
      apply Submodule.add_mem_sup (s.mem_subspace x)
      rw [LinearMap.mem_ker]
      change s.toFun (x - s.toFun x) = 0
      rw [map_sub, s.idempotent, sub_self]
  · intro u hu
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hu
    change s.toFun u = 0 at hu
    have h_sel := s.is_selection u
    rwa [hu] at h_sel

/-- Uniqueness of the linear selector when `V` is a Chebyshev subspace. -/
theorem eq_of_subsingleton {V : Submodule 𝕜 X}
    (h_cheb : ∀ x : X, (V.metricProjection x).Subsingleton)
    (s₁ s₂ : LinearSelector V) : s₁.toFun = s₂.toFun :=
  DFunLike.ext _ _ fun x => h_cheb x (s₁.is_selection x) (s₂.is_selection x)

end LinearSelector
namespace LinearSelector

/-- Composition of two commuting continuous linear selectors yields a continuous linear selector
onto the intersection `V₁ ⊓ V₂` whenever `ker s₁ ⊔ ker s₂ ⊆ P_{V₁ ⊓ V₂}⁻¹(0)`. -/
theorem comp_of_commute {V₁ V₂ : Submodule 𝕜 X}
    (s₁ : LinearSelector V₁) (s₂ : LinearSelector V₂)
    (h_comm : s₁.toFun.comp s₂.toFun = s₂.toFun.comp s₁.toFun)
    (h_ker_sub : ((LinearMap.ker (s₁.toFun : X →ₗ[𝕜] X) ⊔
      LinearMap.ker (s₂.toFun : X →ₗ[𝕜] X) : Submodule 𝕜 X) : Set X) ⊆
      (V₁ ⊓ V₂).metricProjectionZeroLayer) :
    ∃ s₀ : LinearSelector (V₁ ⊓ V₂), s₀.toFun = s₁.toFun.comp s₂.toFun := by
  let V₀ := V₁ ⊓ V₂
  let s₀_op : X →L[𝕜] X := s₁.toFun.comp s₂.toFun
  have h_comm_pt : ∀ x : X, s₁.toFun (s₂.toFun x) = s₂.toFun (s₁.toFun x) :=
    fun x => DFunLike.congr_fun h_comm x
  have h_range : ∀ x : X, s₀_op x ∈ V₀ := by
    intro x
    refine ⟨s₁.mem_subspace _, ?_⟩
    change s₁.toFun (s₂.toFun x) ∈ V₂
    rw [h_comm_pt]
    exact s₂.mem_subspace _
  have h_ker_eq : LinearMap.ker (s₀_op : X →ₗ[𝕜] X) =
      LinearMap.ker (s₁.toFun : X →ₗ[𝕜] X) ⊔ LinearMap.ker (s₂.toFun : X →ₗ[𝕜] X) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      change s₁.toFun (s₂.toFun x) = 0 at hx
      have h_decomp : x = (s₂.toFun x - s₁.toFun (s₂.toFun x)) + (x - s₂.toFun x) := by
        rw [add_comm, sub_add_sub_cancel, hx, sub_zero]
      rw [h_decomp]
      apply Submodule.add_mem_sup
      · rw [LinearMap.mem_ker]
        change s₁.toFun (s₂.toFun x - s₁.toFun (s₂.toFun x)) = 0
        rw [map_sub, s₁.idempotent, sub_self]
      · rw [LinearMap.mem_ker]
        change s₂.toFun (x - s₂.toFun x) = 0
        rw [map_sub, s₂.idempotent, sub_self]
    · apply sup_le
      · intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        change s₁.toFun x = 0 at hx
        change s₁.toFun (s₂.toFun x) = 0
        rw [h_comm_pt, hx, map_zero]
      · intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        change s₂.toFun x = 0 at hx
        change s₁.toFun (s₂.toFun x) = 0
        rw [hx, map_zero]
  refine ⟨⟨s₀_op, h_range, fun x => ⟨h_range x, fun w hw => ?_⟩⟩, rfl⟩
  have hu_ker : x - s₀_op x ∈
      LinearMap.ker (s₁.toFun : X →ₗ[𝕜] X) ⊔ LinearMap.ker (s₂.toFun : X →ₗ[𝕜] X) := by
    rw [← h_ker_eq, LinearMap.mem_ker]
    change s₁.toFun (s₂.toFun (x - s₁.toFun (s₂.toFun x))) = 0
    rw [map_sub, map_sub]
    have h_idem : s₁.toFun (s₂.toFun (s₁.toFun (s₂.toFun x))) = s₁.toFun (s₂.toFun x) := by
      calc s₁.toFun (s₂.toFun (s₁.toFun (s₂.toFun x)))
        _ = s₁.toFun (s₁.toFun (s₂.toFun (s₂.toFun x))) := by rw [← h_comm_pt (s₂.toFun x)]
        _ = s₁.toFun (s₂.toFun (s₂.toFun x)) := by rw [s₁.idempotent]
        _ = s₁.toFun (s₂.toFun x) := by rw [s₂.idempotent]
    rw [h_idem, sub_self]
  have hu_zero := (h_ker_sub hu_ker).2 (w - s₀_op x) (V₀.sub_mem hw (h_range x))
  rw [sub_zero] at hu_zero
  have h_shift : x - w = (x - s₀_op x) - (w - s₀_op x) := (sub_sub_sub_cancel_right x w (s₀_op x)).symm
  rw [h_shift]
  exact hu_zero

/-- Global Lipschitz stability of a linear selector in terms of the complementary projection
`Q = I - s`. -/
theorem lipschitz_bound {V : Submodule 𝕜 X} (s : LinearSelector V) (x y : X) :
    ‖s.toFun x - s.toFun y‖ ≤
      ‖ContinuousLinearMap.id 𝕜 X - (ContinuousLinearMap.id 𝕜 X - s.toFun)‖ * ‖x - y‖ := by
  rw [sub_sub_cancel, ← map_sub]
  exact s.toFun.le_opNorm (x - y)

end LinearSelector

/-- Deutsch's theorem (sufficiency): a continuous linear projection `s_proj` onto `V` along a
complement `U ⊆ P_V⁻¹(0)` defines a continuous linear selector for `V`. -/
theorem exists_linearSelector_of_isCompl {V U : Submodule 𝕜 X}
    (h_compl : IsCompl V U) (h_zero : (U : Set X) ⊆ V.metricProjectionZeroLayer)
    (s_proj : X →L[𝕜] X)
    (h_proj_V : ∀ v ∈ V, s_proj v = v)
    (h_proj_U : ∀ u ∈ U, s_proj u = 0)
    (h_range : ∀ x : X, s_proj x ∈ V) :
    ∃ s : LinearSelector V, s.toFun = s_proj := by
  refine ⟨⟨s_proj, h_range, fun x => ⟨h_range x, fun w hw => ?_⟩⟩, rfl⟩
  have hx_mem : x ∈ V ⊔ U := by rw [h_compl.sup_eq_top]; trivial
  rcases Submodule.mem_sup.mp hx_mem with ⟨v, hv, u, hu, rfl⟩
  have hsv : s_proj (v + u) = v := by
    rw [map_add, h_proj_V v hv, h_proj_U u hu, add_zero]
  rw [hsv]
  have hu_best := (h_zero hu).2 (w - v) (V.sub_mem hw hv)
  rw [sub_zero] at hu_best
  have h_shift1 : v + u - v = u := add_sub_cancel_left v u
  have h_shift2 : v + u - w = u - (w - v) := by abel
  rw [h_shift1, h_shift2]
  exact hu_best

/-- The mutual inclination (opening) coefficient `δ(V, U)` between two submodules `V` and `U`. -/
noncomputable def mutualInclination (V U : Submodule 𝕜 X) : ℝ :=
  sInf {r : ℝ | ∃ v ∈ V, ‖v‖ = 1 ∧ ∃ u ∈ U, r = ‖v + u‖}

/-- Exact operator norm (global Lipschitz constant) of a linear selector in terms of the
mutual inclination `δ(V, ker s)`. -/
theorem LinearSelector.opNorm_eq_inv_mutualInclination {V : Submodule 𝕜 X} (s : LinearSelector V)
    (hV_nontriv : ∃ v ∈ V, v ≠ 0)
    (h_pos : 0 < mutualInclination V (LinearMap.ker (s.toFun : X →ₗ[𝕜] X))) :
    ‖s.toFun‖ = 1 / mutualInclination V (LinearMap.ker (s.toFun : X →ₗ[𝕜] X)) := by
  set U := LinearMap.ker (s.toFun : X →ₗ[𝕜] X)
  set S := {r : ℝ | ∃ v ∈ V, ‖v‖ = 1 ∧ ∃ u ∈ U, r = ‖v + u‖}
  have h_bdd : BddBelow S := ⟨0, by rintro r ⟨v, _, _, u, _, rfl⟩; exact norm_nonneg _⟩
  have h_le : ‖s.toFun‖ ≤ 1 / mutualInclination V U := by
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one h_pos.le)
    intro x
    by_cases hv : s.toFun x = 0
    · rw [hv, norm_zero]
      exact mul_nonneg (div_nonneg zero_le_one h_pos.le) (norm_nonneg x)
    · set v := s.toFun x
      set u := x - v
      have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hv_unit : ‖(‖v‖ : 𝕜)⁻¹ • v‖ = 1 := by
        rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hv_norm_pos.ne']
      have hv_mem : (‖v‖ : 𝕜)⁻¹ • v ∈ V := V.smul_mem _ (s.mem_subspace x)
      have hu_mem : (‖v‖ : 𝕜)⁻¹ • u ∈ U := by
        rw [LinearMap.mem_ker]
        change s.toFun ((‖v‖ : 𝕜)⁻¹ • (x - s.toFun x)) = 0
        rw [map_smul, map_sub, s.idempotent, sub_self, smul_zero]
      have h_delta_le : mutualInclination V U ≤ ‖(‖v‖ : 𝕜)⁻¹ • v + (‖v‖ : 𝕜)⁻¹ • u‖ :=
        csInf_le h_bdd ⟨(‖v‖ : 𝕜)⁻¹ • v, hv_mem, hv_unit, (‖v‖ : 𝕜)⁻¹ • u, hu_mem, rfl⟩
      have h_factor : ‖(‖v‖ : 𝕜)⁻¹ • v + (‖v‖ : 𝕜)⁻¹ • u‖ = ‖v‖⁻¹ * ‖x‖ := by
        rw [← smul_add, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, add_sub_cancel]
      rw [h_factor] at h_delta_le
      have h1 : mutualInclination V U * ‖v‖ ≤ ‖x‖ := by
        have := mul_le_mul_of_nonneg_right h_delta_le hv_norm_pos.le
        rwa [mul_comm (‖v‖⁻¹) ‖x‖, mul_assoc, inv_mul_cancel₀ hv_norm_pos.ne', mul_one] at this
      rw [one_div, inv_mul_eq_div, le_div_iff₀' h_pos]
      exact h1
  apply le_antisymm h_le
  have h_nonempty : S.Nonempty := by
    rcases hV_nontriv with ⟨v₀, hv₀, hv₀_ne⟩
    have hv₀_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀_ne
    refine ⟨‖(‖v₀‖ : 𝕜)⁻¹ • v₀ + 0‖, (‖v₀‖ : 𝕜)⁻¹ • v₀, V.smul_mem _ hv₀, ?_,
      0, Submodule.zero_mem _, rfl⟩
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ hv₀_pos.ne']
  have hs_pos : 0 < ‖s.toFun‖ := by
    rcases hV_nontriv with ⟨v₀, hv₀, hv₀_ne⟩
    have h1 : ‖v₀‖ ≤ ‖s.toFun‖ * ‖v₀‖ := by
      simpa only [s.apply_eq_self hv₀] using s.toFun.le_opNorm v₀
    have hv₀_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀_ne
    nlinarith
  rw [one_div, inv_le_comm₀ h_pos hs_pos]
  apply le_csInf h_nonempty
  rintro r ⟨v, hv, hv_norm, u, hu, rfl⟩
  rw [LinearMap.mem_ker] at hu
  change s.toFun u = 0 at hu
  have h_svu : s.toFun (v + u) = v := by
    rw [map_add, s.apply_eq_self hv, hu, add_zero]
  have h_bound : 1 ≤ ‖s.toFun‖ * ‖v + u‖ := by
    calc (1 : ℝ) = ‖v‖ := hv_norm.symm
      _ = ‖s.toFun (v + u)‖ := by rw [h_svu]
      _ ≤ ‖s.toFun‖ * ‖v + u‖ := s.toFun.le_opNorm (v + u)
  rw [mul_comm] at h_bound
  rwa [inv_le_iff_one_le_mul₀ hs_pos]

end Submodule
