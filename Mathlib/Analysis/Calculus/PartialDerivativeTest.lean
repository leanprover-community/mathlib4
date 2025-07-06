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

/-- Update a vector in coordinate 0. -/
lemma update₀ {α : Type*} (a b c : α)  :
  Function.update ![a,b] 0 c = ![c,b] := by
  ext i
  fin_cases i <;> simp

/-- Update a vector in coordinate 1. -/
lemma update₁ {α : Type*} (a b c : α) :
  Function.update ![a,b] 1 c = ![a,c] := by
  ext i
  fin_cases i <;> simp

/-- The Hessian companion as a linear map. -/
noncomputable def hessianLinearCompanion {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) :
    V → V →ₗ[ℝ] ℝ := fun a => {
    toFun := fun b => iteratedFDeriv ℝ 2 f x₀ ![a,b]
                    + iteratedFDeriv ℝ 2 f x₀ ![b,a]
    map_add' := fun b c => by
      have h_add := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      have h₀ := h_add ![b, a] 0 b c
      have h₁ := h_add ![a, b] 1 b c
      repeat (
        simp only [Fin.isValue, update₁, Nat.succ_eq_add_one, Nat.reduceAdd,
        MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe] at h₁;
        simp only [Fin.isValue, update₀, Nat.succ_eq_add_one, Nat.reduceAdd,
          MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe] at h₀)
      linarith
    map_smul' := by
      intro m x
      have h_smul := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have h₀ := h_smul ![x,a] 0 m x
      have h₁ := h_smul ![a,x] 1 m x
      repeat rw [update₀] at h₀; rw [update₁] at h₁
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
        ContinuousMultilinearMap.coe_coe, smul_eq_mul, RingHom.id_apply] at h₀ h₁ ⊢
      linarith
  }

/-- The Hessian companion as a bilinear map. -/
noncomputable def hessianBilinearCompanion {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) :
    LinearMap.BilinMap ℝ V ℝ := {
    toFun := hessianLinearCompanion f x₀
    map_add' := fun x y => by
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        ext i
        have had₀ := had ![x,i] 0 x y
        have had₁ := had ![i,i] 1 x y
        repeat rw [update₀] at had₀
        repeat rw [update₁] at had₁
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
          ContinuousMultilinearMap.coe_coe, hessianLinearCompanion, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.add_apply] at had₀ had₁ ⊢
        exact
          (Mathlib.Tactic.Ring.add_pf_add_overlap had₀.symm had₁.symm).symm

    map_smul' := fun m x => LinearMap.ext_iff.mpr <| fun x₁ => by
        have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
        have hsm₀ := hsm ![x,x₁] 0 m x
        have hsm₁ := hsm ![x₁,x] 1 m x
        have h := CancelDenoms.add_subst hsm₀.symm hsm₁.symm
        repeat rw [update₀, update₁] at h
        exact h.symm
}

/-- TODO: for a more familiar constructor when R is a ring, see QuadraticMap.ofPolar -/
noncomputable def iteratedFDerivQuadraticMap {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) :
  QuadraticMap ℝ V ℝ :=
  {
    toFun := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
    exists_companion' := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      use hessianBilinearCompanion f x₀
      intro x y
      have had₀ := had ![x, x + y] 0 x y
      have had₁ := had ![x,x] 1 x y
      have had₂ := had ![y,x] 1 x y
      repeat rw [update₀] at had₀; rw [update₁] at had₁ had₂
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
        ContinuousMultilinearMap.coe_coe, hessianBilinearCompanion, LinearMap.coe_mk, AddHom.coe_mk,
        hessianLinearCompanion] at had₀ had₁ had₂ ⊢
      linarith
    toFun_smul := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      intro u v
      have hsm₀ := hsm ![v, v] 0 u v
      have hsm₁ := hsm ![u • v,v] 1 u v
      repeat (
        simp only [Fin.isValue, update₀, Nat.succ_eq_add_one, Nat.reduceAdd,
        MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe, smul_eq_mul] at hsm₀
        simp only [Fin.isValue, update₁, Nat.succ_eq_add_one, Nat.reduceAdd,
          MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe, smul_eq_mul] at hsm₁)
      rw [smul_eq_mul, mul_assoc, ← hsm₀, hsm₁]
  }

/-- An everywhere positive function `f:ℝⁿ → ℝ` achieves its minimum on the sphere. -/
lemma sphere_min_of_pos_of_nonzero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] (f : V → ℝ)
    (hf : Continuous f) (hf' : ∀ x ≠ 0, f x > 0) :
    ∃ x : Metric.sphere 0 1, ∀ y : Metric.sphere 0 1, f x.1 ≤ f y.1 := by
  have h₀ : HasCompactSupport
    fun (x : ↑(Metric.sphere (0:V) 1)) ↦ f ↑x := by
    rw [hasCompactSupport_def]
    rw [Function.support]
    have : @setOf ↑(Metric.sphere (0:V) (1:ℝ)) (fun x ↦ f x.1 ≠ 0)
      = Set.univ := by
      apply subset_antisymm
      simp only [ne_eq, Set.subset_univ]
      intro a ha
      suffices f a > 0 by
        aesop
      apply hf'
      intro hc
      have : ‖a.1‖ = 1 := norm_eq_of_mem_sphere a
      rw [hc] at this
      simp at this
    rw [this]
    simp only [isClosed_univ, IsClosed.closure_eq]
    exact CompactSpace.isCompact_univ
  have ⟨m,hm⟩ := @Continuous.exists_forall_le_of_hasCompactSupport ℝ
    (Metric.sphere (0:V) 1) _
    _ _ _ (by
      have := (@NormedSpace.sphere_nonempty (V)
        _ _ _ 0 1).mpr (by simp)
      exact Set.Nonempty.to_subtype this) _
        (fun x => f x) (by
          refine Continuous.comp' hf ?_
          exact continuous_subtype_val) h₀
  use m

/-- A continuous multilinear map is bilinear. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMap
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ := {
    toFun := fun x => {
        toFun := fun y => g.toFun ![x,y]
        map_add' := by
            intro a b
            have := g.map_update_add ![x,b] 1 a b
            repeat rw [update₁] at this
            exact this
        map_smul' := by
            intro m a
            have := g.map_update_smul ![x,a] 1 m a
            repeat rw [update₁] at this
            exact this
        cont := Continuous.comp' g.cont <| Continuous.matrixVecCons continuous_const
                <| Continuous.matrixVecCons continuous_id' continuous_const
    }
    map_add' := by
        intro a b
        ext c
        have := g.map_update_add ![a,c] 0 a b
        repeat rw [update₀] at this
        exact this
    map_smul' := by
        intro c x
        ext y
        have := g.map_update_smul ![x,y] 0 c x
        repeat rw [update₀] at this
        exact this
    cont := continuous_clm_apply.mpr fun x => Continuous.comp' g.cont
        <| Continuous.matrixVecCons continuous_id' continuous_const
}

/-- The iterated Frechet derivative is continuous. -/
theorem continuous_hessian' {k : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) :
    Continuous fun y ↦ (iteratedFDeriv ℝ k f x₀) fun _ => y :=
  Continuous.comp' (iteratedFDeriv ℝ k f x₀).coe_continuous
    <| continuous_pi fun _ => continuous_id'

/-- The Hessian is continuous. -/
theorem continuous_hessian {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x₀ : V} :
    Continuous fun y ↦ (iteratedFDeriv ℝ 2 f x₀) ![y, y] := by
  convert continuous_hessian' (k := 2) f x₀ using 3
  ext i
  fin_cases i <;> simp

/-- Positive definiteness implies coercivity. -/
lemma coercive_of_posdef'  {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {f : V → ℝ} {x₀ : V}
    (hf' : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  by_cases H : Nontrivial V
  · have := sphere_min_of_pos_of_nonzero (iteratedFDerivQuadraticMap f x₀)
      continuous_hessian hf'
    rw [IsCoercive, continuousBilinearMap_of_continuousMultilinearMap]
    simp only [iteratedFDerivQuadraticMap, Subtype.forall, mem_sphere_iff_norm, sub_zero,
      Subtype.exists, exists_prop] at this
    obtain ⟨m,hm⟩ := this
    have := hm.2
    use (iteratedFDeriv ℝ 2 f x₀) ![m, m]
    have := hf' m (by intro hc;subst hc;simp at hm)
    rw [iteratedFDerivQuadraticMap] at this
    constructor
    · exact this
    · intro u
      by_cases hu : u = 0
      · subst hu
        simp only [norm_zero, mul_zero, MultilinearMap.toFun_eq_coe,
            ContinuousMultilinearMap.coe_coe,
            ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
        rw [iteratedFDeriv_succ_apply_left]
        simp
      · have h₁ : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
        have h₂ : 0 < ‖u‖⁻¹ := Right.inv_pos.mpr <| norm_pos_iff.mpr hu
        have h₃ : ‖u‖ * ‖u‖⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel ‖u‖ h₁
        repeat (
          refine le_of_mul_le_mul_right ?_ h₂
          rw [mul_assoc, h₃]
          simp only [mul_one, MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
            ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk])
        have : (iteratedFDeriv ℝ 2 f x₀) ![u, u] * ‖u‖⁻¹
          = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] := by
          rw [mul_comm, iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
          simp only [Fin.isValue, Matrix.cons_val_zero, Nat.reduceAdd, map_smul,
            ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero,
            norm_eq_zero]
          left
          congr
        rw [this]
        have h₄ : (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] * ‖u‖⁻¹
          = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, ‖u‖⁻¹ • u] := by
          rw [mul_comm]
          have := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![‖u‖⁻¹ • u,u] 1 ‖u‖⁻¹ u
          repeat rw [update₁] at this
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MultilinearMap.toFun_eq_coe,
            ContinuousMultilinearMap.coe_coe, smul_eq_mul] at this ⊢
          rw [this]
        rw [h₄]
        exact hm.2 (‖u‖⁻¹ • u) (by rw [norm_smul];field_simp)
  use 1
  constructor
  · simp
  · intro u
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp H
    rw [Subsingleton.eq_zero u]
    simp

/-- Higher Taylor coefficient. -/
noncomputable def higher_taylor_coeff {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) (k : ℕ) :=
    fun x =>
    (1 / Nat.factorial k : ℝ) * (iteratedFDeriv ℝ k f x₀ fun _ => x - x₀)

/-- Higher Taylor polynomial. -/
noncomputable def higher_taylor {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) (k : ℕ) :
    V → ℝ :=
  ∑ i ∈ Finset.range (k+1), higher_taylor_coeff f x₀ i

/-- Second partial derivative test in terms of `higher_taylor`. -/
theorem isLocalMin_of_PosDef_of_Littleo {V : Type*}
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [Nontrivial V]
    {f : V → ℝ} {x₀ : V}
    (h : (fun x => |f x - higher_taylor f x₀ 2 x|) =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2)
    (h₀ : gradient f x₀ = 0)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsLocalMin f x₀ := by
  have ⟨C,hC⟩ := coercive_of_posdef' hf
  simp only [Asymptotics.IsLittleO, Asymptotics.IsBigOWith] at h
  apply Filter.Eventually.mono <| h (half_pos hC.1)
  intro x
  have h₄ := hC.2 (x - x₀)
  simp only [continuousBilinearMap_of_continuousMultilinearMap, MultilinearMap.toFun_eq_coe,
    ContinuousMultilinearMap.coe_coe, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk] at h₄
  have h₃ : ∑ x_1 ∈ Finset.range 3, higher_taylor_coeff f x₀ x_1 x
   = higher_taylor_coeff f x₀ 0 x + higher_taylor_coeff f x₀ 1 x +
     higher_taylor_coeff f x₀ 2 x := by
    repeat rw [Finset.range_succ]
    simp only [Finset.range_zero, insert_empty_eq, Finset.mem_insert, OfNat.ofNat_ne_one,
      Finset.mem_singleton, OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Finset.sum_insert,
      one_ne_zero, Finset.sum_singleton]
    linarith
  simp only [higher_taylor, Nat.reduceAdd, Finset.sum_apply, Real.norm_eq_abs, abs_abs, norm_pow]
  rw [h₃]
  simp only [higher_taylor_coeff, Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero,
    not_false_eq_true, div_self, iteratedFDeriv_zero_apply, one_mul, Nat.factorial_one,
    iteratedFDeriv_one_apply, map_sub, Nat.factorial_two, Nat.cast_ofNat, one_div, abs_norm]
  intro h₁
  have h₂ : inner ℝ (gradient f x₀) (x - x₀) = (fderiv ℝ f x₀) (x - x₀) := by
    simp [gradient]
  rw [h₀] at h₂
  simp only [inner_zero_left, map_sub] at h₂
  rw [← h₂] at h₁
  simp only [add_zero] at h₁
  rw [mul_assoc,show ![x - x₀, x - x₀] = fun _ => x - x₀ by
    ext i; fin_cases i <;> simp] at h₄
  rw [(Lean.Grind.Semiring.pow_two ‖x - x₀‖).symm] at h₄
  have h₅ : - (f x - (f x₀ + 2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) fun x_1 => x - x₀))
    ≤ (C / 2) * ‖x - x₀‖ ^ 2 := le_of_max_le_right h₁
  ring_nf at h₅
  linarith

/-- `higher_taylor_coeff` expresses power series correctly. -/
lemma eliminate_higher_taylor_coeff {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ContinuousConstSMul ℝ V]
    {f : V → ℝ} (x₀ x : V) {r : NNReal}
    (p : FormalMultilinearSeries ℝ V ℝ)
    (h : HasFPowerSeriesOnBall f p x₀ r) (k : ℕ) :
    p k (fun _ => x - x₀) = higher_taylor_coeff f x₀ k x := by
  have h₀ := @HasFPowerSeriesOnBall.factorial_smul ℝ _
    V _ _ ℝ _ _ p f x₀ r h (x - x₀) _ k
  unfold higher_taylor_coeff
  rw [← h₀]
  norm_num
  rw [← smul_eq_mul, ← smul_eq_mul, ← smul_assoc]
  have : (Nat.factorial k : ℝ)⁻¹ • (Nat.factorial k : ℝ) = 1 := by
    ring_nf
    field_simp
  rw [this]
  simp

theorem littleO_of_powerseries.calculation {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {x₀ : V}
    {p : FormalMultilinearSeries ℝ V ℝ}
    {r : NNReal} (hr : 0 < r) {a : ℝ} (ha : 0 < a) {C : ℝ} (hC : 0 < C)
    (h₃ : ∀ (x : V), x - x₀ ∈ Metric.ball 0 ↑(r / 2) →
        ∀ (n_1 : ℕ), ‖f (x₀ + (x - x₀)) - p.partialSum n_1 (x - x₀)‖
        ≤ C * (a * (‖x - x₀‖ / ↑(r / 2))) ^ n_1)
    {D : ℝ} {x : V}
    (hx : x ∈ Metric.ball x₀ (min (↑r / 2) (D / (C * (a * (2 / ↑r)) ^ 3)))) :
    |f x - p.partialSum 3 (x - x₀)| ≤ D * ‖x - x₀‖ ^ 2 := by
  have h₂ := h₃ x (by
    have : x ∈ Metric.ball x₀ (↑(r / 2)) := by
        aesop
    simp only [Metric.ball, NNReal.coe_div, NNReal.coe_ofNat, Set.mem_setOf_eq, dist_zero_right,
      gt_iff_lt] at this ⊢
    convert this using 1
    exact mem_sphere_iff_norm.mp rfl
  ) 3
  simp only [add_sub_cancel, Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] at h₂
  apply h₂.trans
  simp only [Metric.mem_ball, lt_inf_iff] at hx
  by_cases H : ‖x-x₀‖ = 0
  · have : x - x₀ = 0 := norm_eq_zero.mp H
    have : x = x₀ := by grind only
    subst this
    simp
  suffices (C * (a * (‖x - x₀‖ / (↑r / 2))) ^ 3) * ‖x-x₀‖⁻¹
          ≤ (D * ‖x - x₀‖ ^ 2) * ‖x-x₀‖⁻¹ by
    apply le_of_mul_le_mul_right this
    aesop
  nth_rewrite 2 [mul_assoc]
  have : (‖x - x₀‖ ^ 2 * ‖x - x₀‖⁻¹) = ‖x - x₀‖ := by
    rw [pow_two]
    field_simp
  rw [this]
  suffices C * (a * (‖x - x₀‖ / (↑r / 2))) ^ 3 * ‖x - x₀‖⁻¹  * ‖x-x₀‖⁻¹
       ≤ D * ‖x - x₀‖  * ‖x-x₀‖⁻¹ by
    apply le_of_mul_le_mul_right this
    aesop
  nth_rewrite 3 [mul_assoc]
  have : (‖x - x₀‖ * ‖x - x₀‖⁻¹) = 1 := by field_simp
  rw [this]
  have :  C * (a * (‖x - x₀‖ / (↑r / 2))) ^ 3 * ‖x - x₀‖⁻¹ * ‖x - x₀‖⁻¹
       =  C * (a * (1 / (↑r / 2))) ^ 3 * ‖x - x₀‖  := by
    field_simp
    ring_nf
  rw [this]
  have := hx.2
  simp only [one_div, inv_div, mul_one, ge_iff_le] at this ⊢
  let Q := C * (a * (2 / ↑r)) ^ 3
  conv at this =>
    right
    right
    change Q
  have : Q * ‖x - x₀‖ ≤ Q * (D / Q) := by
    refine (mul_le_mul_iff_of_pos_left ?_).mpr <| le_of_lt (by
        convert this using 1
        exact mem_sphere_iff_norm.mp rfl
    )
    simp only [Q]
    aesop
  convert this using 2
  field_simp

/-- Having a power series implies quadratic approximation. -/
lemma littleO_of_powerseries {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ}
    {x₀ : V}
    {p : FormalMultilinearSeries ℝ V ℝ}
    {r : NNReal} (hr : 0 < r) (h₁ : HasFPowerSeriesOnBall f p x₀ r) :
        (fun x => |f x - p.partialSum 3 (x - x₀)|)
          =o[nhds x₀]
          fun x => ‖x - x₀‖ ^ 2 := by
  rw [Asymptotics.IsLittleO]
  intro D hD
  obtain ⟨a,ha⟩ := HasFPowerSeriesOnBall.uniform_geometric_approx' h₁ (by
      change ENNReal.ofNNReal ((r / 2)) < r
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
      refine ENNReal.half_lt_self ?_ ?_
      · simp only [ne_eq, ENNReal.coe_eq_zero]
        intro hc
        subst hc
        simp at hr
      · simp)
  obtain ⟨C,hC⟩ := ha.2
  have h₃ (x) := hC.2 (x - x₀)
  rw [Asymptotics.IsBigOWith]
  refine eventually_nhds_iff.mpr ?_
  simp only [Real.norm_eq_abs, abs_abs, norm_pow]
  use Metric.ball x₀ (min (r/2) (D / (C * (a * (2/r))^3)))
  constructor
  · convert @littleO_of_powerseries.calculation V _ _ f x₀ p r hr a ha.1.1 C hC.1 h₃ D using 3
    congr
    apply abs_norm
  · constructor
    · exact Metric.isOpen_ball
    · simp only [Metric.mem_ball, dist_self, lt_inf_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right,
      NNReal.coe_pos]
      constructor
      · tauto
      · simp_all

/-- Second partial derivative test. -/
theorem second_derivative_test {V : Type*}
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {f : V → ℝ}
    {x₀ : V}
    {p : FormalMultilinearSeries ℝ V ℝ}
    (h₀ : gradient f x₀ = 0) {r : NNReal} (hr : 0 < r)
    (h₁ : HasFPowerSeriesOnBall f p x₀ r)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) : IsLocalMin f x₀ := by
  by_cases H : Nontrivial V
  · have : (fun x ↦ |f x - ∑ x_1 ∈ Finset.range (2 + 1), (p x_1) fun x_2 ↦ x - x₀|)
       = (fun x ↦ |f x - ∑ x_1 ∈ Finset.range (2 + 1), higher_taylor_coeff f x₀ x_1 x|) := by
      ext
      congr
      ext
      rw [eliminate_higher_taylor_coeff x₀ _ p h₁]
    exact isLocalMin_of_PosDef_of_Littleo (this ▸ littleO_of_powerseries hr h₁) h₀ hf
  · have : Subsingleton V := not_nontrivial_iff_subsingleton.mp H
    simp [IsLocalMin, IsMinFilter]
