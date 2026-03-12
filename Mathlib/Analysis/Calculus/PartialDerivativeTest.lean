/-
Copyright (c) 2025 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.IteratedFDeriv

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

@[expose] public section

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
    [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a b => iteratedFDeriv ℝ 2 f x₀ ![a,b] + iteratedFDeriv ℝ 2 f x₀ ![b,a])
    (fun _ _ _ ↦ by simp [Matrix.vecCons, ← curryLeft_apply]; abel)
    (by simp [Matrix.vecCons, ← curryLeft_apply, mul_add])
    (fun _ _ _ ↦ by simp [Matrix.vecCons, ← curryLeft_apply]; abel)
    (by simp [Matrix.vecCons, ← curryLeft_apply, mul_add])


/-- The second iterated Frechét derivative as a quadratic map. -/
noncomputable def iteratedFDerivQuadraticMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (f : V → ℝ) (x₀ : V) : QuadraticMap ℝ V ℝ := {
  toFun := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
  exists_companion' := ⟨hessianBilinearCompanion f x₀, fun x y => by
    have ha (u v b) := (iteratedFDeriv ℝ 2 f x₀).map_update_add' ![u,v] b x y
    have ha₀ := ha x (x + y) 0
    have ha₁ (u) := ha u x 1
    simp only [update₀, MultilinearMap.toFun_eq_coe, coe_coe, update₁, hessianBilinearCompanion]
        at ha₀ ha₁ ha ⊢
    rw [ha₀, ha₁, ha₁, add_assoc, add_assoc]
    apply add_left_cancel_iff.mpr
    rw [← add_assoc, add_comm]
    simp⟩
  toFun_smul := fun u v => by
    have hsm (b c) := (iteratedFDeriv ℝ 2 f x₀).map_update_smul' ![b,v] c u v
    have hsm₀ := hsm v 0
    have hsm₁ := hsm (u • v) 1
    simp only [update₀, update₁, MultilinearMap.toFun_eq_coe, coe_coe, smul_eq_mul]
        at hsm₀ hsm₁ hsm
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



-- Aristotle start

def QuadraticMap.toMultilinearMap {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticMap ℝ V ℝ) :
  MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
  let B := Q.polarBilin
  { toFun := fun v => B (v 0) (v 1)
    map_update_add' := by
      simp +zetaDelta at *
    map_update_smul' := by
      simp +decide [ Function.update_apply ] }

noncomputable def QuadraticMap.toMultilinearMapHALF {V : Type*} [AddCommGroup V] [Module ℝ V]
  (Q : QuadraticMap ℝ V ℝ) :
  MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
  let B := Q.polarBilin
  { toFun := fun v => (1/2) * B (v 0) (v 1)
    map_update_add' := by
      simp +zetaDelta only [one_div, Fin.isValue, polarBilin_apply_apply, Fin.forall_fin_two,
        update_self, ne_eq, one_ne_zero, not_false_eq_true, update_of_ne, polar_add_left,
        zero_ne_one, polar_add_right, forall_const] at *
      intro m
      apply And.intro
      · intro x y
        exact Distrib.left_distrib 2⁻¹ _ _
      · intro x y
        exact Distrib.left_distrib 2⁻¹ _ _
    map_update_smul' := by
      simp +decide only [one_div, Fin.isValue, update_apply, smul_eq_mul, Fin.forall_fin_two,
        ↓reduceIte, map_smul, one_ne_zero, LinearMap.smul_apply, zero_ne_one, forall_const]
      intros
      constructor
      · intros
        ring_nf
      · intros
        ring_nf
      }

/-
The multilinear map associated to a quadratic map is continuous.
-/
theorem QuadraticMap.toMultilinearMap_continuous {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) : Continuous Q.toMultilinearMap := by
  have h_bilinear : ∃ B : V →ₗ[ℝ] V →L[ℝ] ℝ, ∀ x y, B x y = Q.toMultilinearMap ![x, y] := by
    have h_bilinear : ∃ B : V →ₗ[ℝ] V →L[ℝ] ℝ, ∀ x y, B x y = Q.polarBilin x y := by
      have h_bilinear : ∀ x : V, ∃ Bx : V →L[ℝ] ℝ, ∀ y : V, Bx y = Q.polarBilin x y := by
        exact fun x => ⟨ ContinuousLinearMap.mk ( Q.polarBilin x ), fun y => rfl ⟩
      choose B hB using h_bilinear;
      refine ⟨ { toFun := B, map_add' := ?_, map_smul' := ?_ }, hB ⟩ <;> aesop;
    aesop;
  -- Since $B$ is a linear map between finite-dimensional spaces, it is continuous.
  obtain ⟨B, hB⟩ := h_bilinear;
  have hB_cont : Continuous B := by
    exact B.continuous_of_finiteDimensional;
  convert hB_cont.comp ( show Continuous fun v : Fin 2 → V => v 0 from continuous_apply 0 ) |>
    Continuous.clm_apply <| show Continuous fun v : Fin 2 → V => v 1 from continuous_apply 1 using 1
    ; aesop;

theorem QuadraticMap.toMultilinearMap_continuousHALF {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) : Continuous Q.toMultilinearMapHALF := by
  have h_bilinear : ∃ B : V →ₗ[ℝ] V →L[ℝ] ℝ, ∀ x y, B x y = Q.toMultilinearMapHALF ![x, y] := by
    have h_bilinear : ∃ B : V →ₗ[ℝ] V →L[ℝ] ℝ, ∀ x y, B x y = (1/2) * Q.polarBilin x y := by
      have h_bilinear : ∀ x : V, ∃ Bx : V →L[ℝ] ℝ, ∀ y : V, Bx y = (1/2) * Q.polarBilin x y := by
        intro x
        refine ⟨ ContinuousLinearMap.mk (by
          let q := fun y : V => (1/2) * Q.polarBilin x y
          refine IsLinearMap.mk' q ?_
          refine { map_add := ?_, map_smul := ?_ }
          · intro a b
            unfold q
            have : Q.polarBilin x (a+b) =
                  Q.polarBilin x a +
                  Q.polarBilin x b := by exact LinearMap.map_add (Q.polarBilin x) a b
            rw [this]
            linarith
          · intro c a
            unfold q
            simp
            linarith), fun y => by simp ⟩
      choose B hB using h_bilinear;
      refine ⟨ { toFun := B, map_add' := ?_, map_smul' := ?_ }, hB ⟩
      · intro x y
        simp_all only [one_div, polarBilin_apply_apply]
        ext i
        rw [hB (x+y) i]
        simp only [polar_add_left, ContinuousLinearMap.add_apply]
        rw [hB x i, hB y i]
        linarith
      intro m x
      ext y
      rw [hB (m • x)]
      simp only [one_div, map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul,
        RingHom.id_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [hB]
      simp
      linarith
    simp_all only [one_div, polarBilin_apply_apply]
    obtain ⟨w, h⟩ := h_bilinear
    unfold QuadraticMap.toMultilinearMapHALF
    simp only [one_div, Fin.isValue, polarBilin_apply_apply, MultilinearMap.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    use w
  -- Since $B$ is a linear map between finite-dimensional spaces, it is continuous.
  obtain ⟨B, hB⟩ := h_bilinear;
  have hB_cont : Continuous B := by
    exact B.continuous_of_finiteDimensional;
  convert hB_cont.comp ( show Continuous fun v : Fin 2 → V => v 0 from continuous_apply 0 ) |>
    Continuous.clm_apply <| show Continuous fun v : Fin 2 → V => v 1 from continuous_apply 1 using 1
    ; aesop

/-
Construct a continuous multilinear map from a quadratic map on a finite dimensional space.
-/
def QuadraticMap.toContinuousMultilinearMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) :
  ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ :=
  { Q.toMultilinearMap with
    cont := Q.toMultilinearMap_continuous }

noncomputable def QuadraticMap.toContinuousMultilinearMapHALF {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) :
  ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ :=
  { Q.toMultilinearMapHALF with
    cont := Q.toMultilinearMap_continuousHALF }

/-
The constructed continuous multilinear map agrees with the polar bilinear form.
-/
theorem QuadraticMap.toContinuousMultilinearMap_apply {V : Type*} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) (x y : V) :
  Q.toContinuousMultilinearMap ![x, y] = Q.polarBilin x y := by
    rfl

theorem QuadraticMap.toContinuousMultilinearMap_applyHALF {V : Type*} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticMap ℝ V ℝ) (x y : V) :
  Q.toContinuousMultilinearMapHALF ![x, y] = (1/2) * Q.polarBilin x y := by
    rfl


-- Aristotle end
lemma coercive_of_posdef'HALF {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {F : QuadraticMap ℝ V ℝ}
    (hf' : F.PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        F.toContinuousMultilinearMapHALF) := by
  nontriviality V
  have h₀ : ∃ x : ↑(Metric.sphere 0 1), ∀ (y : ↑(Metric.sphere 0 1)),
    (fun y ↦ F.toContinuousMultilinearMapHALF ![y, y]) x.1 ≤
      (fun y ↦ F.toContinuousMultilinearMapHALF ![y, y])
      y.1 := by
    obtain ⟨x,hx⟩ := IsCompact.exists_isMinOn
      (f := (fun y => F.toContinuousMultilinearMapHALF ![y, y]))
      (isCompact_sphere (0:V) 1) (NormedSpace.sphere_nonempty.mpr (by simp))
      (Continuous.continuousOn <| by fun_prop)
    use ⟨x,hx.1⟩
    intro y
    simp only [mem_sphere_iff_norm, sub_zero, IsMinOn, IsMinFilter,
      Filter.eventually_principal] at hx
    apply hx.2
    simp
  simp only [Subtype.forall, mem_sphere_iff_norm, sub_zero, Subtype.exists, exists_prop] at h₀
  obtain ⟨m,hm⟩ := h₀
  use F.toContinuousMultilinearMapHALF ![m, m]
  rw [continuousBilinearMap_of_continuousMultilinearMap]
  constructor
  ·   unfold QuadraticMap.toContinuousMultilinearMapHALF
        QuadraticMap.toMultilinearMapHALF
      change 0 < (fun v ↦ (1/2) * (F (v 0 + v 1) - F (v 0) - F (v 1))) ![m,m]
      have (x y : V) : F (x + y) = F x + F y + F.polarBilin x y := QuadraticMap.map_add (⇑F) x y
      simp only [succ_eq_add_one, reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, gt_iff_lt]
      rw [this]
      ring_nf
      suffices 0 < (F.polarBilin m) m by linarith
      simp only [QuadraticMap.polarBilin, LinearMap.mk₂_apply, QuadraticMap.polar_self,
        nsmul_eq_mul, cast_ofNat, ofNat_pos, mul_pos_iff_of_pos_left]
      apply hf'
      intro hc
      subst hc
      simp at hm
  · intro u
    by_cases hu : u = 0
    · subst hu
      unfold QuadraticMap.toContinuousMultilinearMapHALF
        QuadraticMap.toMultilinearMapHALF
      simp [QuadraticMap.polar]
    · have h₁ : ‖u‖ * ‖u‖⁻¹ = 1 := CommGroupWithZero.mul_inv_cancel _ <| norm_ne_zero_iff.mpr hu
      repeat (
        refine le_of_mul_le_mul_right ?_ <|Right.inv_pos.mpr <| norm_pos_iff.mpr hu
        rw [mul_assoc, h₁]
        simp only [mul_one, MultilinearMap.toFun_eq_coe, coe_coe,
          ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk])
      have h₂ := update₁ ▸ update₁ ▸
        F.toContinuousMultilinearMapHALF.map_update_smul' ![‖u‖⁻¹ • u,u] 1 ‖u‖⁻¹ u
      simp only [MultilinearMap.toFun_eq_coe, coe_coe, smul_eq_mul] at h₂
      have : F.toContinuousMultilinearMapHALF ![u, u] * ‖u‖⁻¹
           = F.toContinuousMultilinearMapHALF ![‖u‖⁻¹ • u, u] := by
        simp [Matrix.vecCons, ← curryLeft_apply, mul_comm]
      rw [this, mul_comm, ← h₂]
      exact hm.2 (‖u‖⁻¹ • u) (by
        rw [← h₁, norm_smul, mul_comm]
        congr
        refine Real.norm_of_nonneg ?_
        simp)

/-- Positive definiteness implies coercivity.
  The proof is long but it uses the general fact `coercive_of_posdef'HALF`
  but also it requires a differentiability assumption on `f`.
-/
lemma coercive_of_posdef_of_coercive_of_posdef'' {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {f : V → ℝ} {x₀ : V}
    (hf : ContDiffAt ℝ ⊤ f x₀)
    (hf' : (iteratedFDerivQuadraticMap f x₀).PosDef) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
  have := @coercive_of_posdef'HALF V _ _ _ (iteratedFDerivQuadraticMap f x₀) hf'
  convert this
  unfold QuadraticMap.toContinuousMultilinearMapHALF
  unfold QuadraticMap.toMultilinearMapHALF iteratedFDerivQuadraticMap
  simp only [one_div, Fin.isValue, QuadraticMap.polarBilin_apply_apply, QuadraticMap.coe_mk]
  unfold QuadraticMap.polar
  have (v : Fin 2 → V) :
      (iteratedFDeriv ℝ 2 f x₀) ![v 0 + v 1, v 0 + v 1] =
      (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 0 + v 1] +
      (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 0 + v 1] := by
      set F := (iteratedFDeriv ℝ 2 f x₀)
      have (α β γ : V) : F ![α + β, γ] = F ![α, γ] + F ![β, γ] :=
        F.toMultilinearMap.map_update_add' ![α,γ] 0 α β
      rw [this]
  simp_rw [this]
  have (v : Fin 2 → V) :
    (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 0 + v 1] =
    (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 0]
    +
    (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1] := by
      set F := (iteratedFDeriv ℝ 2 f x₀)
      have (α β γ : V)  :=
        F.toMultilinearMap.map_update_add' ![α,γ] 1 α β
      simp only [Fin.isValue, update₁, succ_eq_add_one, reduceAdd, MultilinearMap.toFun_eq_coe,
        coe_coe, forall_const] at this
      rw [this]
  simp_rw [this]
  have (v : Fin 2 → V) :
    (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 0 + v 1] =
    (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 0]
    +
    (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 1] := by
      set F := (iteratedFDeriv ℝ 2 f x₀)
      have (α β γ : V)  :=
        F.toMultilinearMap.map_update_add' ![β,γ] 1 α β
      simp only [Fin.isValue, update₁, succ_eq_add_one, reduceAdd, MultilinearMap.toFun_eq_coe,
        coe_coe, forall_const] at this
      rw [this]
  simp_rw [this]
  have (v : Fin 2 → V) :
    (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 0] + (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1] +
            ((iteratedFDeriv ℝ 2 f x₀) ![v 1, v 0] + (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 1]) -
          (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 0] -
        (iteratedFDeriv ℝ 2 f x₀) ![v 1, v 1]
      = (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1] +
            ((iteratedFDeriv ℝ 2 f x₀) ![v 1, v 0]) := by
      linarith
  simp_rw [this]
  have (x y : V) : (iteratedFDeriv ℝ 2 f x₀) ![x, y]
    = (iteratedFDeriv ℝ 2 f x₀) ![y, x] := by
    -- use hf'
    have := @ContDiffAt.iteratedFDeriv_comp_perm ℝ _ V _ _ ℝ _ _
      f x₀ hf 2 ![x,y] (by refine {
        toFun := fun i => ⟨1-i.1, by omega⟩
        invFun := fun i => ⟨1-i.1, by omega⟩
        left_inv := fun _ => by simp;congr;omega
        right_inv := fun _ => by simp;congr;omega
      })
    rw [← this]
    apply congrArg
    ext i
    fin_cases i <;> simp
  simp_rw [this]
  ext v
  have : v = ![v 0, v 1] := by
    ext i;fin_cases i <;> simp
  rw [this]
  change (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1] =
    2⁻¹ * ((iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1] + (iteratedFDeriv ℝ 2 f x₀) ![v 0, v 1])
  linarith

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
      (Continuous.continuousOn <| by fun_prop)
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
      have : (iteratedFDeriv ℝ 2 f x₀) ![u, u] * ‖u‖⁻¹
           = (iteratedFDeriv ℝ 2 f x₀) ![‖u‖⁻¹ • u, u] := by
        simp [Matrix.vecCons, ← curryLeft_apply, mul_comm]
      rw [this, mul_comm, ← h₂]
      exact hm.2 (‖u‖⁻¹ • u) (by
        rw [← h₁, norm_smul, mul_comm]
        congr
        refine Real.norm_of_nonneg ?_
        simp)


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
  simp only [range_add_one, range_zero, insert_empty_eq, one_div, mem_insert, OfNat.ofNat_ne_one,
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
      rw [Metric.mem_ball, mem_sphere_iff_norm.mpr rfl] at hx
      exact hx)) using 2
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
