/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

open Function Metric Set Filter Finset Topology NNReal

open LinearMap (range ker)

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E →SL[σ] F)

namespace ContinuousLinearMap

/-- A (possibly nonlinear) right inverse to a continuous linear map, which doesn't have to be
linear itself but which satisfies a bound `‖inverse x‖ ≤ C * ‖x‖`. A surjective continuous linear
map doesn't always have a continuous linear right inverse, but it always has a nonlinear inverse
in this sense, by Banach's open mapping theorem. -/
structure NonlinearRightInverse where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : F → E
  /-- The bound `C` so that `‖inverse x‖ ≤ C * ‖x‖` for all `x`. -/
  nnnorm : ℝ≥0
  bound' : ∀ y, ‖toFun y‖ ≤ nnnorm * ‖y‖
  right_inv' : ∀ y, f (toFun y) = y

instance : CoeFun (NonlinearRightInverse f) fun _ => F → E :=
  ⟨fun fsymm => fsymm.toFun⟩

@[simp]
theorem NonlinearRightInverse.right_inv {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    f (fsymm y) = y :=
  fsymm.right_inv' y

theorem NonlinearRightInverse.bound {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    ‖fsymm y‖ ≤ fsymm.nnnorm * ‖y‖ :=
  fsymm.bound' y

end ContinuousLinearMap

variable {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ']

/-- Given a continuous linear equivalence, the inverse is in particular an instance of
`ContinuousLinearMap.NonlinearRightInverse` (which turns out to be linear). -/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse
    [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F) where
  toFun := f.invFun
  nnnorm := ‖(f.symm : F →SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F →SL[σ'] E) _
  right_inv' := f.apply_symm_apply

noncomputable instance [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F)) :=
  ⟨f.toNonlinearRightInverse⟩

/-! ### Proof of the Banach open mapping theorem -/


variable [CompleteSpace F]

namespace ContinuousLinearMap

include σ' in
/-- First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ‖y‖`.
For further use, we will only need such an element whose image
is within distance `‖y‖/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le (surj : Surjective f) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have A : ⋃ n : ℕ, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  have : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n)) :=
    nonempty_interior_of_iUnion_of_closed (fun n => isClosed_closure) A
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at this
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hc' : 1 < ‖σ c‖ := by simp only [RingHomIsometric.norm_map, hc]
    rcases rescale_to_shell hc' (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ ≤ 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ ≤ δ + δ := by rw [dist_eq_norm'] at h₁ h₂; gcongr
        _ = 2 * δ := (two_mul _).symm
    have J : ‖f (σ' d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ :=
      calc
        ‖f (σ' d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rwa [f.map_smulₛₗ _, inv_mul_cancel₀, one_smul, map_inv₀, map_inv₀,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = ‖d‖⁻¹ * ‖d‖ * ‖y‖ / 2 := by
          simp only [δ]
          ring
        _ = ‖y‖ / 2 := by
          simp [norm_eq_zero, hd]
        _ = 1 / 2 * ‖y‖ := by ring
    rw [← dist_eq_norm] at J
    have K : ‖σ' d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖σ' d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, RingHomIsometric.norm_map, norm_inv]
        _ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          gcongr
          · simpa using dinv
          · exact le_trans (norm_sub_le _ _) (by gcongr)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨σ' d⁻¹ • x, J, K⟩

variable [CompleteSpace E]

section
include σ'

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le (surj : Surjective f) :
    ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) C0
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/
protected theorem isOpenMap (surj : Surjective f) : IsOpenMap f := by
  intro s hs
  rcases exists_preimage_norm_le f surj with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x + w) = z := by rw [f.map_add, wim, fxy, add_sub_cancel]
  rw [← this]
  have : x + w ∈ ball x ε :=
    calc
      dist (x + w) x = ‖w‖ := by
        simp
      _ ≤ C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ (ne_of_gt Cpos)
  exact Set.mem_image_of_mem _ (hε this)

theorem isQuotientMap (surj : Surjective f) : IsQuotientMap f :=
  (f.isOpenMap surj).isQuotientMap f.continuous surj

end

theorem _root_.AffineMap.isOpenMap {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] {P Q : Type*} [MetricSpace P] [NormedAddTorsor E P] [MetricSpace Q]
    [NormedAddTorsor F Q] (f : P →ᵃ[𝕜] Q) (hf : Continuous f) (surj : Surjective f) :
    IsOpenMap f :=
  AffineMap.isOpenMap_linear_iff.mp <|
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)

/-! ### Applications of the Banach open mapping theorem -/

section
include σ'

theorem interior_preimage (hsurj : Surjective f) (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

theorem closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

theorem frontier_preimage (hsurj : Surjective f) (s : Set F) :
    frontier (f ⁻¹' s) = f ⁻¹' frontier s :=
  ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

theorem exists_nonlinearRightInverse_of_surjective (f : E →SL[σ] F)
    (hsurj : LinearMap.range f = ⊤) :
    ∃ fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm := by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

end

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
noncomputable irreducible_def nonlinearRightInverseOfSurjective (f : E →SL[σ] F)
  (hsurj : LinearMap.range f = ⊤) : NonlinearRightInverse f :=
  Classical.choose (exists_nonlinearRightInverse_of_surjective f hsurj)

theorem nonlinearRightInverseOfSurjective_nnnorm_pos (f : E →SL[σ] F)
    (hsurj : LinearMap.range f = ⊤) : 0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm := by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

end ContinuousLinearMap

namespace LinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/-- If a bounded linear map is a bijection, then its inverse is also a bounded linear map. -/
@[continuity]
theorem continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

/-- Associating to a linear equivalence between Banach spaces a continuous linear equivalence when
the direct map is continuous, thanks to the Banach open mapping theorem that ensures that the
inverse map is also continuous. -/
def toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : E ≃SL[σ] F :=
  { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h) = e :=
  rfl

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E] [RingHomInvPair σ' σ] {f : E →SL[σ] F}

/-- An injective continuous linear map with a closed range defines a continuous linear equivalence
between its domain and its range. -/
noncomputable def equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] LinearMap.range f :=
  have : CompleteSpace (LinearMap.range f) := hclo.completeSpace_coe
  LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj) <|
    (f.continuous.codRestrict fun x ↦ LinearMap.mem_range_self f x).congr fun _ ↦ rfl

@[simp]
theorem coe_linearMap_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    f.equivRange hinj hclo = f.rangeRestrict :=
  rfl

@[simp]
theorem coe_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo : E → LinearMap.range f) = f.rangeRestrict :=
  rfl

@[simp]
lemma equivRange_symm_toLinearEquiv (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo).toLinearEquiv.symm =
      (LinearEquiv.ofInjective f.toLinearMap hinj).symm := rfl

@[simp]
lemma equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f))
    (x : E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x := by
  suffices f ((f.equivRange hinj hclo).symm ⟨f x, by simp⟩) = f x from hinj this
  trans f ((f.equivRange hinj hclo).symm.toLinearEquiv ⟨f x, by simp⟩)
  · rfl -- is there an API lemma for this already?
  simp only [ContinuousLinearEquiv.toLinearEquiv_symm, equivRange_symm_toLinearEquiv]
  set x' : LinearMap.range f := ⟨f x, by simp⟩
  set f' : E →ₛₗ[σ] F := ↑f
  change f' ((LinearEquiv.ofInjective f' hinj).symm x') = _
  rw [LinearEquiv.ofInjective_symm_apply (f := f') (h := hinj) x']

section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

-- TODO: once mathlib has Fredholm operators, generalise the next two lemmas accordingly

/-- If `f : E →L[𝕜] F` is injective with closed range (and `E` and `F` are Banach spaces),
`f` is anti-Lipschitz. -/
lemma antilipschitz_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : ∃ K, AntilipschitzWith K f := by
  let S : (LinearMap.range f) →L[𝕜] E := (f.equivRange hf hf').symm
  use ⟨S.opNorm, S.opNorm_nonneg⟩
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro x
  calc ‖x‖
    _ = ‖S ⟨f x, by simp⟩‖ := by simp [S]
    _ ≤ S.opNorm * ‖f x‖ := le_opNorm S ⟨f x, by simp⟩

/-- An injective bounded linear operator between Banach spaces has closed range
iff it is anti-Lipschitz. -/
lemma isClosed_range_iff_antilipschitz_of_injective (f : E →L[𝕜] F)
    (hf : Injective f) : IsClosed (Set.range f) ↔ ∃ K, AntilipschitzWith K f := by
  refine ⟨fun h ↦ f.antilipschitz_of_injective_of_isClosed_range hf h, fun h ↦ ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

end

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable [CompleteSpace E] [RingHomInvPair σ' σ]

/-- Convert a bijective continuous linear map `f : E →SL[σ] F` from a Banach space to a normed space
to a continuous linear equivalence. -/
noncomputable def ofBijective (f : E →SL[σ] F) (hinj : ker f = ⊥) (hsurj : LinearMap.range f = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
    (by exact f.continuous)

@[simp]
theorem coeFn_ofBijective (f : E →SL[σ] F) (hinj : ker f = ⊥) (hsurj : LinearMap.range f = ⊤) :
    ⇑(ofBijective f hinj hsurj) = f :=
  rfl

theorem coe_ofBijective (f : E →SL[σ] F) (hinj : ker f = ⊥) (hsurj : LinearMap.range f = ⊤) :
    ↑(ofBijective f hinj hsurj) = f := by
  ext
  rfl

@[simp]
theorem ofBijective_symm_apply_apply (f : E →SL[σ] F) (hinj : ker f = ⊥)
    (hsurj : LinearMap.range f = ⊤) (x : E) : (ofBijective f hinj hsurj).symm (f x) = x :=
  (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]
theorem ofBijective_apply_symm_apply (f : E →SL[σ] F) (hinj : ker f = ⊥)
    (hsurj : LinearMap.range f = ⊤) (y : F) : f ((ofBijective f hinj hsurj).symm y) = y :=
  (ofBijective f hinj hsurj).apply_symm_apply y

lemma _root_.ContinuousLinearMap.isUnit_iff_bijective {f : E →L[𝕜] E} :
    IsUnit f ↔ Bijective f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ofUnit f |>.bijective
  · refine fun h ↦ ⟨toUnit <| .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMapClass.ker_eq_bot, h.1, h.2]

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- Intermediate definition used to show
`ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as a `ContinuousLinearEquiv`. -/
noncomputable def coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl (LinearMap.range f) G) [CompleteSpace G] (hker : ker f = ⊥) : (E × G) ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · rw [hker, Submodule.ker_subtypeL, Submodule.prod_bot]
      · rw [Submodule.range_subtypeL]
        exact h.disjoint)
    (by simp only [range_coprod, Submodule.range_subtypeL, h.sup_eq_top])

theorem range_eq_map_coprodSubtypeLEquivOfIsCompl {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E →L[𝕜] F) {G : Submodule 𝕜 F}
    (h : IsCompl (LinearMap.range f) G) [CompleteSpace G] (hker : ker f = ⊥) :
    LinearMap.range f =
      ((⊤ : Submodule 𝕜 E).prod (⊥ : Submodule 𝕜 G)).map
        (f.coprodSubtypeLEquivOfIsCompl h hker : E × G →ₗ[𝕜] F) := by
  rw [coprodSubtypeLEquivOfIsCompl, ContinuousLinearEquiv.coe_ofBijective,
    coe_coprod, LinearMap.coprod_map_prod, Submodule.map_bot, sup_bot_eq, Submodule.map_top]
  rfl

/- TODO: remove the assumption `f.ker = ⊥` in the next lemma, by using the map induced by `f` on
`E / f.ker`, once we have quotient normed spaces. -/
theorem closed_complemented_range_of_isCompl_of_ker_eq_bot {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (f : E →L[𝕜] F) (G : Submodule 𝕜 F)
    (h : IsCompl (LinearMap.range f) G) (hG : IsClosed (G : Set F)) (hker : ker f = ⊥) :
    IsClosed (LinearMap.range f : Set F) := by
  haveI : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

end ContinuousLinearMap

section ClosedGraphThm

variable [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (g : E →ₗ[𝕜] F)

/-- The **closed graph theorem** : a linear map between two Banach spaces whose graph is closed
is continuous. -/
theorem LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    Continuous g := by
  letI : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let φ₀ : E →ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E :=
    φ.symm.toContinuousLinearEquivOfContinuous continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/-- A useful form of the **closed graph theorem** : let `f` be a linear map between two Banach
spaces. To show that `f` is continuous, it suffices to show that for any convergent sequence
`uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`. -/
theorem LinearMap.continuous_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    Continuous g := by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

variable {g}

namespace ContinuousLinearMap

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using the **closed graph theorem**. -/
def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_isClosed_graph hg

@[simp]
theorem coeFn_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ⇑(ContinuousLinearMap.ofIsClosedGraph hg) = g :=
  rfl

theorem coe_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ↑(ContinuousLinearMap.ofIsClosedGraph hg) = g := by
  ext
  rfl

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using a variation on the
**closed graph theorem**. -/
def ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
theorem coeFn_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ⇑(ContinuousLinearMap.ofSeqClosedGraph hg) = g :=
  rfl

theorem coe_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ↑(ContinuousLinearMap.ofSeqClosedGraph hg) = g := by
  ext
  rfl

end ContinuousLinearMap

end ClosedGraphThm

section BijectivityCriteria

namespace ContinuousLinearMap

variable {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ']
variable {F : Type u_4} [NormedAddCommGroup F] [NormedSpace 𝕜' F]
variable [CompleteSpace E]

lemma closed_range_of_antilipschitz {f : E →SL[σ] F} {c : ℝ≥0} (hf : AntilipschitzWith c f) :
    (LinearMap.range f).topologicalClosure = LinearMap.range f :=
  SetLike.ext'_iff.mpr <| (hf.isClosed_range f.uniformContinuous).closure_eq

variable [CompleteSpace F]

lemma _root_.AntilipschitzWith.completeSpace_range_clm {f : E →SL[σ] F} {c : ℝ≥0}
    (hf : AntilipschitzWith c f) : CompleteSpace (LinearMap.range f) :=
  IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

variable [RingHomInvPair σ' σ] [RingHomIsometric σ] [RingHomIsometric σ']

open Function
lemma bijective_iff_dense_range_and_antilipschitz (f : E →SL[σ] F) :
    Bijective f ↔ (LinearMap.range f).topologicalClosure = ⊤ ∧ ∃ c, AntilipschitzWith c f := by
  refine ⟨fun h ↦ ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ ↦ ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using h.2.denseRange.closure_eq
  case anti =>
    refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_ |>.antilipschitz⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMapClass.ker_eq_bot, h.1, h.2]
  case surj => rwa [← LinearMap.range_eq_top, ← closed_range_of_antilipschitz hf]

end ContinuousLinearMap

end BijectivityCriteria
