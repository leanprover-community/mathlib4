/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The Second Partial Derivatives Test

We prove a version of the second partial derivative test from calculus for
analytic functions `f : V → ℝ`, where `V` is a finite-dimensional vector space.

## Main results

* `second_derivative_test`:
    Suppose `f` is a real-valued function on a
    finite-dimensional inner product space that
    has vanishing gradient at `x₀`, and has a power series on a ball of positive radius
    around `x₀`. If the second Frechét derivative is positive definite at `x₀` then
    `f` has  local minimum at `x₀`.

## Tags
partial derivative test, calculus
-/

/-- Update a vector of length 2 in coordinate 0. -/
@[simp]
lemma Function.update₀ {α : Type*} {a b c : α} : Function.update ![a,b] 0 c = ![c,b] := by
  ext i; fin_cases i <;> simp

/-- Update a vector of length 2 in coordinate 1. -/
@[simp]
lemma Function.update₁ {α : Type*} {a b c : α} : Function.update ![a,b] 1 c = ![a,c] := by
  ext i; fin_cases i <;> simp

open Nat ContinuousMultilinearMap Finset Function

/-- The Hessian companion as a bilinear map. -/
noncomputable def hessianBilinearCompanion {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ := by
  apply @LinearMap.mk₂ (
    f := fun a b => iteratedFDeriv ℝ 2 f x₀ ![a,b]
                  + iteratedFDeriv ℝ 2 f x₀ ![b,a])
  · intro b c a
    have h₀ := (iteratedFDeriv ℝ 2 f x₀).map_update_add' ![b, a] 0 b c
    have h₁ := (iteratedFDeriv ℝ 2 f x₀).map_update_add' ![a, b] 1 b c
    repeat (
    simp only [Fin.isValue, update₁, Nat.succ_eq_add_one, Nat.reduceAdd,
    MultilinearMap.toFun_eq_coe, coe_coe] at h₁;
    simp only [Fin.isValue, update₀, Nat.succ_eq_add_one, Nat.reduceAdd,
        MultilinearMap.toFun_eq_coe, coe_coe] at h₀)
    linarith
  · intro m x a
    have h₀ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![x,a] 0 m x
    have h₁ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![a,x] 1 m x
    repeat rw [update₀] at h₀; rw [update₁] at h₁
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
    coe_coe, smul_eq_mul] at h₀ h₁ ⊢
    linarith
  · intro i x y
    have had₀ := (iteratedFDeriv ℝ 2 f x₀).map_update_add' ![x,i] 0 x y
    have had₁ := (iteratedFDeriv ℝ 2 f x₀).map_update_add' ![i,i] 1 x y
    repeat rw [update₀] at had₀
    repeat rw [update₁] at had₁
    simp only [succ_eq_add_one, reduceAdd, MultilinearMap.toFun_eq_coe, coe_coe] at had₀ had₁ ⊢
    have := @(Mathlib.Tactic.Ring.add_pf_add_overlap had₀.symm had₁.symm).symm
    linarith
  · intro m a x
    have h₀ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![x,a] 0 m x
    have h₁ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![a,x] 1 m x
    repeat rw [update₀] at h₀; rw [update₁] at h₁
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
    coe_coe, smul_eq_mul] at h₀ h₁ ⊢
    linarith


/-- The second iterated Frechét derivative as a quadratic map. -/
noncomputable def iteratedFDerivQuadraticMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) : QuadraticMap ℝ V ℝ := {
  toFun := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
  exists_companion' := by
    use hessianBilinearCompanion f x₀
    intro x y
    have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
    have had₀ := had ![x, x + y] 0 x y
    have had₁ := had ![x,x] 1 x y
    have had₂ := had ![y,x] 1 x y
    repeat rw [update₀] at had₀; rw [update₁] at had₁ had₂
    simp [hessianBilinearCompanion] at had₀ had₁ had₂ ⊢
    linarith
  toFun_smul := fun u v => by
    have hsm₀ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![v, v] 0 u v
    have hsm₁ := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![u • v,v] 1 u v
    simp only [update₀, update₁, MultilinearMap.toFun_eq_coe, coe_coe, smul_eq_mul] at hsm₀ hsm₁
    rw [smul_eq_mul, mul_assoc, ← hsm₀, hsm₁]}


/-- A continuous multilinear map is bilinear. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMap
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => V) 𝕜) : V →L[𝕜] V →L[𝕜] 𝕜 := {
  toFun := fun x => {
    toFun := fun y => g.toFun ![x,y]
    map_add' := fun a b => by simpa [update₁] using g.map_update_add ![x,b] 1 a b
    map_smul' := fun m a => by simpa [update₁] using g.map_update_smul ![x,a] 1 m a
    cont := g.cont.comp' <| continuous_const.matrixVecCons
            <| continuous_id'.matrixVecCons continuous_const}
  map_add' := fun a b => by ext c; simpa [update₀] using g.map_update_add ![a,c] 0 a b
  map_smul' := fun c x => by ext y; simpa [update₀] using g.map_update_smul ![x,y] 0 c x
  cont := continuous_clm_apply.mpr fun x => g.cont.comp'
    <| continuous_id'.matrixVecCons continuous_const}

/-- A continuous multilinear map is bilinear. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMapGENERAL
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin 2 => V) 𝕜) : V →L[𝕜] V →L[𝕜] 𝕜 := {
  toFun := fun x => {
    toFun := fun y => g.toFun ![x,y]
    map_add' := fun a b => by simpa [update₁] using g.map_update_add ![x,b] 1 a b
    map_smul' := fun m a => by simpa [update₁] using g.map_update_smul ![x,a] 1 m a
    cont := g.cont.comp' <| continuous_const.matrixVecCons
            <| continuous_id'.matrixVecCons continuous_const}
  map_add' := fun a b => by ext c; simpa [update₀] using g.map_update_add ![a,c] 0 a b
  map_smul' := fun c x => by ext y; simpa [update₀] using g.map_update_smul ![x,y] 0 c x
  cont := continuous_clm_apply.mpr fun x => g.cont.comp'
    <| continuous_id'.matrixVecCons continuous_const}

/-- The iterated Frechet derivative is continuous. -/
theorem continuous_hessian' {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x₀ : V) : Continuous fun y => (iteratedFDeriv ℝ k f x₀) fun _ => y :=
  (iteratedFDeriv ℝ k f x₀).coe_continuous.comp' (continuous_pi fun _ => continuous_id')

/-- The Hessian is continuous. -/
theorem continuous_hessian {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x₀ : V} :
    Continuous fun y => (iteratedFDeriv ℝ 2 f x₀) ![y, y] := by
  convert continuous_hessian' (k := 2) f x₀ using 3
  ext i
  fin_cases i <;> simp

@[nontriviality]
lemma isCoercive.of_subsingleton {V : Type*} [Subsingleton V]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V →L[ℝ] V →L[ℝ] ℝ) : IsCoercive F := by
  use 1
  constructor
  · simp
  · intro u
    rw [Subsingleton.eq_zero u]
    simp


theorem iteratedFDeriv_two_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x₀ : V} (u : V) (r : ℝ) :
    (iteratedFDeriv ℝ 2 f x₀) ![u, u] * r = (iteratedFDeriv ℝ 2 f x₀) ![r • u, u] := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, mul_comm]
  simp only [Matrix.cons_val_zero, map_smul,
    smul_apply, smul_eq_mul, mul_eq_mul_left_iff]
  left
  congr

/-- Positive definiteness implies coercivity. -/
lemma coercive_of_posdef {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : V → ℝ} {x₀ : V}
    (hf' : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  nontriviality V
  have h₀ : ∃ x : ↑(Metric.sphere 0 1), ∀ (y : ↑(Metric.sphere 0 1)),
    (fun y ↦ (iteratedFDeriv ℝ 2 f x₀) ![y, y]) x.1 ≤ (fun y ↦ (iteratedFDeriv ℝ 2 f x₀) ![y, y])
      y.1 := by
    obtain ⟨x,hx⟩ := IsCompact.exists_isMinOn (f := (fun y => (iteratedFDeriv ℝ 2 f x₀) ![y, y]))
      (isCompact_sphere (0:V) 1) (NormedSpace.sphere_nonempty.mpr (by simp))
      (Continuous.continuousOn <| @continuous_hessian V _ _ f x₀)
    use ⟨x,hx.1⟩
    intro y
    simp only [mem_sphere_iff_norm, sub_zero, IsMinOn, IsMinFilter,
      Filter.eventually_principal] at hx
    apply hx.2
    simp
  simp only [Subtype.forall, mem_sphere_iff_norm, sub_zero, Subtype.exists, exists_prop] at h₀
  obtain ⟨m,hm⟩ := h₀
  use iteratedFDeriv ℝ 2 f x₀ ![m, m]
  rw [continuousBilinearMap_of_continuousMultilinearMap]
  constructor
  · exact hf' m (by intro hc;simp [hc] at hm)
  · intro u
    by_cases hu : u = 0
    · simp [hu, iteratedFDeriv_succ_apply_left]
    · have h₁ : ‖u‖ * ‖u‖⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel _ <| norm_ne_zero_iff.mpr hu
      repeat (
        refine le_of_mul_le_mul_right ?_ <|Right.inv_pos.mpr <| norm_pos_iff.mpr hu
        rw [mul_assoc, h₁]
        simp only [mul_one, MultilinearMap.toFun_eq_coe, coe_coe,
          ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk])
      have h₂ := update₁ ▸ update₁ ▸
        (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![‖u‖⁻¹ • u,u] 1 ‖u‖⁻¹ u
      simp only [MultilinearMap.toFun_eq_coe, coe_coe, smul_eq_mul] at h₂
      rw [iteratedFDeriv_two_mul, mul_comm, ← h₂]
      exact hm.2 (‖u‖⁻¹ • u) (by rw [norm_smul];field_simp)

theorem le_of_littleO {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ℝ} {x₀ x : V} {C : ℝ}
    (hx : C * (‖x - x₀‖ ^ 2) ≤ iteratedFDeriv ℝ 2 f x₀ fun _ ↦ x - x₀)
    (hx₀ : fderiv ℝ f x₀ x = fderiv ℝ f x₀ x₀)
    (h₁ : ‖f x - ∑ i ∈ range 3, 1 / ↑i ! * iteratedFDeriv ℝ i f x₀ fun _ ↦ x - x₀‖
      ≤ C / 2 * ‖x - x₀‖ ^ 2) :
  f x₀ ≤ f x := by
  have rev_ineq {a b c d : ℝ} (h : a + b ≤ c + d) (h' : d ≤ b) : a ≤ c := by
    linarith
  refine rev_ineq ?_ <| mul_le_mul_of_nonneg_right (by convert hx using 2) (show 0 ≤ 1/2 by simp)
  simp only [range_succ, range_zero, insert_empty_eq, one_div, mem_insert, OfNat.ofNat_ne_one,
    mem_singleton, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, sum_insert, factorial_two,
    cast_ofNat, one_ne_zero, factorial_one, cast_one, inv_one, iteratedFDeriv_one_apply, map_sub,
    one_mul, sum_singleton, factorial_zero, iteratedFDeriv_zero_apply, Real.norm_eq_abs] at h₁
  have := le_of_max_le_right (hx₀ ▸ h₁)
  linarith


/-- Second partial derivative test, "little oh" form. -/
theorem isLocalMin_of_posDef_of_littleo {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {f : V → ℝ} {x₀ : V}
    (h : (fun x => f x - ∑ i ∈ range 3, 1 / (i)! * iteratedFDeriv ℝ i f x₀ fun _ => x - x₀)
      =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2) (h₀ : gradient f x₀ = 0)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) : IsLocalMin f x₀ := by
  have ⟨C,hC⟩ := coercive_of_posdef hf
  simp only [Asymptotics.IsLittleO, Asymptotics.IsBigOWith] at h
  apply (h (half_pos hC.1)).mono
  intro x
  have hx := hC.2 (x - x₀)
  simp only [continuousBilinearMap_of_continuousMultilinearMap, MultilinearMap.toFun_eq_coe,
    coe_coe, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk] at hx
  rw [mul_assoc,show ![x - x₀, x - x₀] = fun _ => x - x₀ by
    ext i; fin_cases i <;> simp] at hx
  have hx₀ : inner ℝ (gradient f x₀) (x - x₀) = fderiv ℝ f x₀ (x - x₀) := by simp [gradient]
  simp only [h₀, inner_zero_left, map_sub] at hx₀
  simp only [norm_pow, norm_norm]
  rw [← pow_two] at hx
  exact le_of_littleO hx <| sub_eq_zero.mp hx₀.symm


theorem littleO_of_powerseries.inequality {z : ℝ} {r : ℝ} (hr : 0 < r)
    {a : ℝ} (ha : 0 < a) {C : ℝ} (hC : 0 < C) {D : ℝ}
    (hx : z ≤ D / (C * (a * r) ^ 3)) :
    C * (a * (z * r)) ^ 3 ≤ D * z ^ 2 := by
  rw [pow_succ, mul_pow, pow_two, pow_two] at hx ⊢
  have : z * (C * (a * a * (r * r) * (a * r))) ≤ D := (le_div_iff₀ (by positivity)).mp hx
  ring_nf at this ⊢
  suffices z ^ 2 * (z * C * a ^ 3 * r ^ 3) ≤ z ^ 2 * D by linarith
  gcongr

theorem littleO_of_powerseries.aux
    {V : Type*} [NormedAddCommGroup V]
    {x₀ : V}
    {r : NNReal} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {C : ℝ} (hC : 0 < C)
    {x : V} {D : ℝ}
    (hx : x ∈ Metric.ball x₀ (D / (C * (a * (2 / r)) ^ 3))) :
    C * (a * (‖x - x₀‖ / (r / 2))) ^ 3 ≤ D * ‖x - x₀‖ ^ 2 := by
  convert @inequality ‖x-x₀‖ (2/r) (by aesop) a ha C hC D
    (le_of_lt (by
      simp at hx
      convert hx using 1
      exact mem_sphere_iff_norm.mp rfl
      )) using 2
  ring_nf

theorem littleO_of_powerseries.calculation {V : Type*} [NormedAddCommGroup V]
    {f : V → ℝ} {x₀ : V}
    {r : NNReal} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {C : ℝ} (hC : 0 < C)
    (α : ℝ) {x : V}
    (h₃ : x - x₀ ∈ Metric.ball 0 (r / 2) →
        ‖f (x₀ + (x - x₀)) - α‖
        ≤ C * (a * (‖x - x₀‖ / (r / 2))) ^ 3)
    {D : ℝ}
    (hx : x ∈ Metric.ball x₀ (min (r / 2) (D / (C * (a * (2 / r)) ^ 3)))) :
    |f x - α| ≤ D * ‖x - x₀‖ ^ 2 := by
  simp only [Metric.mem_ball, lt_inf_iff, dist_zero_right, add_sub_cancel,
    Real.norm_eq_abs] at hx h₃ ⊢
  specialize h₃ (by convert hx.1 using 1;exact mem_sphere_iff_norm.mp rfl)
  apply h₃.trans <| aux hr ha hC (by convert hx.2 using 2)

/-- Having a power series implies quadratic approximation. -/
lemma littleO_of_powerseries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x₀ : V} {p : FormalMultilinearSeries ℝ V ℝ}
    {r : NNReal} (hr : 0 < r) (h : HasFPowerSeriesOnBall f p x₀ r) :
    (fun x => f x - p.partialSum 3 (x - x₀)) =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2 := by
  rw [Asymptotics.IsLittleO]
  intro D hD
  have : ENNReal.ofNNReal ((r / 2)) < r := by
    norm_num
    exact ENNReal.half_lt_self (fun hc => (lt_self_iff_false _).mp
      (ENNReal.coe_eq_zero.mp hc ▸ hr)) (by simp)
  obtain ⟨a,ha⟩ := HasFPowerSeriesOnBall.uniform_geometric_approx' h this
  rw [Asymptotics.IsBigOWith]
  apply eventually_nhds_iff.mpr
  simp only [Real.norm_eq_abs, norm_pow]
  obtain ⟨C,hC⟩ := ha.2
  use Metric.ball x₀ (min (r/2) (D / (C * (a * (2/r))^3)))
  constructor
  · intro y h
    rw [abs_norm]
    exact littleO_of_powerseries.calculation hr ha.1.1
      hC.1 (p.partialSum 3 (y - x₀)) (fun hy => hC.2 (y-x₀) hy 3) h
  · constructor
    · exact Metric.isOpen_ball
    · simp_all

@[nontriviality]
lemma isLocalMin.of_subsingleton {V : Type*} [TopologicalSpace V]
    [Subsingleton V] {f : V → ℝ} {x₀ : V} : IsLocalMin f x₀ := by
  simp [IsLocalMin, IsMinFilter]

/-- The second partial derivative test. -/
theorem second_derivative_test {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {f : V → ℝ} {x₀ : V} {p : FormalMultilinearSeries ℝ V ℝ}
    (h₀ : gradient f x₀ = 0) {r : NNReal} (hr : 0 < r) (h₁ : HasFPowerSeriesOnBall f p x₀ r)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) : IsLocalMin f x₀ := by
  nontriviality V
  have h₂ (x : V) (i : ℕ) : p i (fun _ => x - x₀)
      = 1 / (i)! * iteratedFDeriv ℝ i f x₀ fun _ => x - x₀ := by
    rw [← HasFPowerSeriesOnBall.factorial_smul h₁ (x - x₀) i]
    ring_nf
    field_simp
  have h₃ (x : V) : ∑ i ∈ range 3, p i (fun _ => x - x₀)
                  = ∑ i ∈ range 3, 1 / (i)! * iteratedFDeriv ℝ i f x₀ fun _ => x - x₀ := by
    congr
    ext
    rw [h₂]
  have h₄ (x : V) := congrArg (HSub.hSub (f x)) (h₃ x)
  exact isLocalMin_of_posDef_of_littleo (funext_iff.mpr h₄ ▸ littleO_of_powerseries hr h₁) h₀ hf
