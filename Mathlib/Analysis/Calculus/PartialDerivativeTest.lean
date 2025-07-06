/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Second Partial Derivatives Test

We prove a version of the second partial derivative test from calculus for
analytic functions `f : ℝⁿ → ℝ`.

## Main results

* `second_derivative_test`:
    Suppose `f` is a real-valued function on `n`-dimensional Euclidean space that
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
noncomputable def hessianLinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := fun a => {
    toFun := fun b => iteratedFDeriv ℝ 2 f x₀ ![a,b]
                    + iteratedFDeriv ℝ 2 f x₀ ![b,a]
    map_add' := fun b c => by
      have h_add := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      have h₀ := h_add ![b, a] 0 b c
      have h₁ := h_add ![a, b] 1 b c
      repeat simp [update₁] at h₁; simp [update₀] at h₀
      linarith
    map_smul' := by
      intro m x
      have h_smul := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have h₀ := h_smul ![x,a] 0 m x
      have h₁ := h_smul ![a,x] 1 m x
      repeat rw [update₀] at h₀; rw [update₁] at h₁
      simp at h₀ h₁ ⊢
      linarith
  }

/-- The Hessian companion as a bilinear map. -/
noncomputable def hessianBilinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)): LinearMap.BilinMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ := {
    toFun := hessianLinearCompanion f x₀
    map_add' := fun x y => by
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        ext i
        have had₀ := had ![x,i] 0 x y
        have had₁ := had ![i,i] 1 x y
        repeat rw [update₀] at had₀
        repeat rw [update₁] at had₁
        simp [hessianLinearCompanion] at had₀ had₁ ⊢
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
noncomputable def iteratedFDerivQuadraticMap {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
  QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ :=
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
      simp [hessianLinearCompanion, hessianBilinearCompanion] at had₀ had₁ had₂ ⊢
      linarith
    toFun_smul := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      intro u v
      have hsm₀ := hsm ![v, v] 0 u v
      have hsm₁ := hsm ![u • v,v] 1 u v
      repeat simp [update₀] at hsm₀; simp [update₁] at hsm₁
      rw [smul_eq_mul, mul_assoc, ← hsm₀, hsm₁]
  }

/-- An everywhere positive function `f:ℝⁿ → ℝ` achieves its minimum on the sphere. -/
lemma sphere_min_of_pos_of_nonzero {n : ℕ} (f : EuclideanSpace ℝ (Fin n.succ) → ℝ)
    (hf : Continuous f) (hf' : ∀ x ≠ 0, f x > 0) :
    ∃ x : Metric.sphere 0 1, ∀ y : Metric.sphere 0 1, f x.1 ≤ f y.1 := by
  have h₀ : HasCompactSupport
    fun (x : ↑(Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) 1)) ↦ f ↑x := by
    rw [hasCompactSupport_def]
    rw [Function.support]
    have : @setOf ↑(Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) (1:ℝ)) (fun x ↦ f x.1 ≠ 0)
      = Set.univ := by
      apply subset_antisymm
      simp
      intro a ha
      suffices f a > 0 by
        aesop
      apply hf'
      intro hc
      have : ‖a.1‖ = 1 := norm_eq_of_mem_sphere a
      rw [hc] at this
      simp at this
    rw [this]
    simp
    exact CompactSpace.isCompact_univ
  have ⟨m,hm⟩ := @Continuous.exists_forall_le_of_hasCompactSupport ℝ
    (Metric.sphere (0:EuclideanSpace ℝ (Fin n.succ)) 1) _
    _ _ _ (by
      have := (@NormedSpace.sphere_nonempty (EuclideanSpace ℝ (Fin n.succ))
        _ _ _ 0 1).mpr (by simp)
      exact Set.Nonempty.to_subtype this) _
        (fun x => f x) (by
          refine Continuous.comp' hf ?_
          exact continuous_subtype_val) h₀
  use m

/-- A continuous multilinear map is bilinear. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMap {n : ℕ}
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ) :
    (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := {
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

/-- In 0-dimensional Euclidean space, coercivity is automatic. -/
lemma coercive_zero {f : EuclideanSpace ℝ (Fin 0) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin 0)} :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  simp [IsCoercive, continuousBilinearMap_of_continuousMultilinearMap]
  use 1
  constructor
  · simp
  · intro u
    have : u = ![] := by refine PiLp.ext ?_; intro z;have := z.2;simp at this
    subst this
    simp
    have : @norm (EuclideanSpace ℝ (Fin 0)) (PiLp.normedAddCommGroup 2 fun x ↦ ℝ).toNorm
      (@Matrix.vecEmpty ℝ : Fin 0 → ℝ) = 0 := by simp;exact Subsingleton.eq_zero ![]
    rw [this]
    simp
    have : f = fun z => f ![] := by
      ext z
      congr
      ext i
      have := i.2
      simp at this
    rw [this]
    simp
    rw [iteratedFDeriv_succ_apply_left]
    simp
    rw [iteratedFDeriv]
    simp

/-- The iterated Frechet derivative is continuous. -/
theorem continuous_hessian' {k n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} :
    Continuous fun y ↦ (iteratedFDeriv ℝ k f x₀) fun _ => y :=
  Continuous.comp' (iteratedFDeriv ℝ k f x₀).coe_continuous
    <| continuous_pi fun _ => continuous_id'

/-- The Hessian is continuous. -/
theorem continuous_hessian {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} :
    Continuous fun y ↦ (iteratedFDeriv ℝ 2 f x₀) ![y, y] := by
  convert @continuous_hessian' (k := 2) n f x₀ using 3
  ext i j
  fin_cases i <;> simp

/-- Positive definiteness implies coercivity. -/
lemma coercive_of_posdef {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  by_cases H : n = 0
  · subst H
    exact @coercive_zero f x₀
  obtain ⟨m,hm⟩ : ∃ m : ℕ, n = m.succ := by exact Nat.exists_eq_succ_of_ne_zero H
  subst hm
  have := @sphere_min_of_pos_of_nonzero m (iteratedFDerivQuadraticMap f x₀)
    continuous_hessian hf
  simp [IsCoercive, continuousBilinearMap_of_continuousMultilinearMap]
  simp [iteratedFDerivQuadraticMap] at this
  obtain ⟨m,hm⟩ := this
  have := hm.2
  use (iteratedFDeriv ℝ 2 f x₀) ![m, m]
  have := hf m (by intro hc;subst hc;simp at hm)
  simp [iteratedFDerivQuadraticMap] at this
  constructor
  · exact this
  · intro u
    by_cases hu : u = 0
    · subst hu
      simp
      rw [iteratedFDeriv_succ_apply_left]
      simp
    · have h₁ : ‖u‖ ≠ 0 := by exact norm_ne_zero_iff.mpr hu
      have h₂ : 0 < ‖u‖⁻¹ := Right.inv_pos.mpr <| norm_pos_iff.mpr hu
      have h₃ : ‖u‖ * ‖u‖⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel ‖u‖ h₁
      repeat (
        refine le_of_mul_le_mul_right ?_ h₂
        rw [mul_assoc, h₃]
        simp)
      have : (iteratedFDeriv ℝ 2 f x₀) ![u, u] * ‖u‖⁻¹
        = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] := by
        rw [mul_comm]
        rw [iteratedFDeriv_succ_apply_left]
        rw [iteratedFDeriv_succ_apply_left]
        simp
        left
        congr
      rw [this]
      have h₄ : (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] * ‖u‖⁻¹
        = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, ‖u‖⁻¹ • u] := by
        let G := iteratedFDeriv ℝ 2 f x₀
        change G ![‖u‖⁻¹ • u, u] * ‖u‖⁻¹ = G ![‖u‖⁻¹ • u, ‖u‖⁻¹ • u]
        rw [mul_comm]
        let v := ‖u‖⁻¹ • u
        change  ‖u‖⁻¹ * G ![v, u] = G ![v, ‖u‖⁻¹ • u]
        change  ‖u‖⁻¹ * G.toFun ![v, u] = G.toFun ![v, ‖u‖⁻¹ • u]
        simp
        have := G.map_update_smul' ![v,u] 1 ‖u‖⁻¹ u
        repeat rw [update₁] at this
        symm
        simp at this ⊢
        rw [this]
      rw [h₄]
      have := hm.2 (‖u‖⁻¹ • u) (by simp [norm_smul];field_simp)
      simp at this ⊢
      exact this

/-- Higher Taylor coefficient. -/
noncomputable def higher_taylor_coeff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :=
    fun x =>
    (1 / Nat.factorial k : ℝ) * (iteratedFDeriv ℝ k f x₀ fun _ => x - x₀)

/-- Higher Taylor polynomial. -/
noncomputable def higher_taylor {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  ∑ i ∈ Finset.range (k+1), higher_taylor_coeff f x₀ i

/-- Second partial derivative test in terms of `higher_taylor`. -/
theorem isLocalMin_of_PosDef_of_Littleo {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : (fun x => |f x - higher_taylor f x₀ 2 x|) =o[nhds x₀] fun x => ‖x - x₀‖ ^ 2)
    (h₀ : gradient f x₀ = 0)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsLocalMin f x₀ := by
  have ⟨C,hC⟩ : IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) :=  @coercive_of_posdef n f x₀ hf
  simp [Asymptotics.IsLittleO, Asymptotics.IsBigOWith] at h
  apply Filter.Eventually.mono <| h (half_pos hC.1)
  intro x
  have h₄ := hC.2 (x - x₀)
  simp [continuousBilinearMap_of_continuousMultilinearMap] at h₄
  have h₃ : ∑ x_1 ∈ Finset.range 3, higher_taylor_coeff f x₀ x_1 x
   = higher_taylor_coeff f x₀ 0 x + higher_taylor_coeff f x₀ 1 x +
     higher_taylor_coeff f x₀ 2 x := by
    repeat rw [Finset.range_succ]; simp
    linarith
  simp [higher_taylor]
  rw [h₃]
  simp [higher_taylor_coeff]
  intro h₁
  have h₂ : inner ℝ (gradient f x₀) (x - x₀) = (fderiv ℝ f x₀) (x - x₀) := by
    unfold gradient; simp
  rw [h₀] at h₂
  simp at h₂
  rw [← h₂] at h₁
  simp at h₁
  rw [mul_assoc,show ![x - x₀, x - x₀] = fun _ => x - x₀ by
    ext i j; fin_cases i <;> simp] at h₄
  rw [(Lean.Grind.Semiring.pow_two ‖x - x₀‖).symm] at h₄
  have h₅ : - (f x - (f x₀ + 2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) fun x_1 => x - x₀))
    ≤ (C / 2) * ‖x - x₀‖ ^ 2 := le_of_max_le_right h₁
  ring_nf at h₅
  linarith

/-- `higher_taylor_coeff` expresses power series correctly. -/
lemma eliminate_higher_taylor_coeff {n : ℕ} {r : NNReal}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x₀ x : EuclideanSpace ℝ (Fin n))
  (p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  (h : @HasFPowerSeriesOnBall ℝ (EuclideanSpace ℝ (Fin n)) ℝ _
    _ _ _ _ f p x₀ r) (k : ℕ) :
  (p k) (fun _ => x - x₀) = higher_taylor_coeff f x₀ k x := by
  have h₀ := @HasFPowerSeriesOnBall.factorial_smul ℝ _
    (EuclideanSpace ℝ (Fin n)) _ _ ℝ _ _ p f x₀ r h (x - x₀) _ k
  unfold higher_taylor_coeff
  rw [← h₀]
  norm_num
  rw [← smul_eq_mul]
  rw [← smul_eq_mul]
  rw [← smul_assoc]
  have : ((Nat.factorial k : ℝ)⁻¹) • (Nat.factorial k : ℝ) = 1 := by
    ring_nf
    field_simp
  rw [this]
  simp


/-- Having a power series implies quadratic approximation. -/
lemma littleO_of_powerseries {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    (h₀ : gradient f x₀ = 0) {r : NNReal} (hr : 0 < r)
    (h₁ : HasFPowerSeriesOnBall f p x₀ r) :
        (fun x => |f x - p.partialSum 3 (x - x₀)|)
          =o[nhds x₀]
          fun x => ‖x - x₀‖ ^ 2 := by
  simp [Asymptotics.IsLittleO, Asymptotics.IsBigOWith]
  intro D hD
  obtain ⟨a,ha⟩ := HasFPowerSeriesOnBall.uniform_geometric_approx' h₁ (by
      change ENNReal.ofNNReal ((r / 2)) < r
      simp
      refine ENNReal.half_lt_self ?_ ?_
      · simp
        intro hc
        subst hc
        simp at hr
      · simp)
  obtain ⟨C,hC⟩ := ha.2
  have h₃ (x) := hC.2 (x - x₀)
  refine eventually_nhds_iff.mpr ?_
  use Metric.ball x₀ (min (r/2) (D / (C * (a * (2/r))^3)))
  constructor
  · intro x hx
    have h₂ := h₃ x (by aesop) 3
    simp at h₂
    apply h₂.trans
    simp at hx
    by_cases H : ‖x-x₀‖ = 0
    · have : x - x₀ = 0 := norm_eq_zero.mp H
      have : x = x₀ := by
        refine PiLp.ext ?_
        intro i
        have : (x - x₀) i = 0 := congrFun this i
        simp_all
        linarith
      subst this
      simp
    suffices  (C * (a * (‖x - x₀‖ / (↑r / 2))) ^ 3) * ‖x-x₀‖⁻¹
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
    simp
    have :  C * (a * (‖x - x₀‖ / (↑r / 2))) ^ 3 * ‖x - x₀‖⁻¹ * ‖x - x₀‖⁻¹
         =  C * (a * (1 / (↑r / 2))) ^ 3 * ‖x - x₀‖  := by
        field_simp
        ring_nf
    rw [this]
    have := hx.2
    conv at this =>
      left
      change ‖x - x₀‖
    simp at this ⊢
    let Q :=  (C * (a * (2 / ↑r)) ^ 3)
    conv at this =>
      right
      right
      change Q
    have : Q * ‖x - x₀‖ ≤ Q * (D / Q) := by
      refine (mul_le_mul_iff_of_pos_left ?_).mpr <| le_of_lt this
      simp [Q]
      aesop
    convert this using 2
    field_simp
    ring_nf
    rw [mul_comm Q D, mul_assoc]
    have : Q ≠ 0 := by
      simp [Q]
      constructor
      aesop
      constructor
      intro hc
      subst hc
      have := ha.1
      simp at this
      intro hc
      subst hc
      have := ha.1
      simp at this
      aesop
    have : Q * Q⁻¹ = 1 := by
      field_simp
    rw [this]
    simp
  · constructor
    · exact Metric.isOpen_ball
    · simp
      constructor
      · tauto
      · simp_all

/-- Second partial derivative test. -/
theorem second_derivative_test {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ}
    (h₀ : gradient f x₀ = 0) {r : NNReal} (hr : 0 < r)
    (h₁ : HasFPowerSeriesOnBall f p x₀ r)
    (hf : (iteratedFDerivQuadraticMap f x₀).PosDef) : IsLocalMin f x₀ := by
have : (fun x ↦ |f x - ∑ x_1 ∈ Finset.range (2 + 1), (p x_1) fun x_2 ↦ x - x₀|)
     = (fun x ↦ |f x - ∑ x_1 ∈ Finset.range (2 + 1), higher_taylor_coeff f x₀ x_1 x|) := by
  ext
  congr
  ext
  rw [eliminate_higher_taylor_coeff f x₀ _ p h₁]
exact isLocalMin_of_PosDef_of_Littleo (this ▸ littleO_of_powerseries h₀ hr h₁) h₀ hf
