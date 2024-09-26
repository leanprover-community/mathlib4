/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Blank docstring to be filled in

-/

open Filter Asymptotics

open scoped ENNReal

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}


/-- If a function is polynomial on a set `s`, so are its successive Fréchet derivative. -/
theorem CPolynomialOn.iteratedFDeriv (h : CPolynomialOn 𝕜 f s) (n : ℕ) :
    CPolynomialOn 𝕜 (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 𝕜 E F).symm : F →L[𝕜] E[×0]→L[𝕜] F).comp_cPolynomialOn h
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    convert ContinuousLinearMap.comp_cPolynomialOn ?g IH.fderiv
    case g => exact ↑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) ↦ E) F).symm
    simp

/-- A polynomial function is infinitely differentiable. -/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  suffices AnalyticOnNhd 𝕜 f t by
    have t_open : IsOpen t := isOpen_cPolynomialAt 𝕜 f
    exact AnalyticOnNhd.contDiffOn this t_open.uniqueDiffOn
  have H : CPolynomialOn 𝕜 f t := fun _x hx ↦ hx
  exact H.analyticOnNhd

theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : WithTop ℕ∞} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cPolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) {n : WithTop ℕ∞} {x : Π i, E i}

open FormalMultilinearSeries

lemma contDiffAt : ContDiffAt 𝕜 n f x := f.cpolynomialAt.contDiffAt

lemma contDiff : ContDiff 𝕜 n f := contDiff_iff_contDiffAt.mpr (fun _ ↦ f.contDiffAt)

end ContinuousMultilinearMap

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries ENNReal Nat

variable {p : FormalMultilinearSeries 𝕜 E F} {f : E → F} {x : E} {r : ℝ≥0∞}
  (h : HasFPowerSeriesOnBall f p x r) (y : E)

include h in
theorem iteratedFDeriv_zero_apply_diag : iteratedFDeriv 𝕜 0 f x = p 0 := by
  ext
  convert (h.hasSum <| EMetric.mem_ball_self h.r_pos).tsum_eq.symm
  · rw [iteratedFDeriv_zero_apply, add_zero]
  · rw [tsum_eq_single 0 fun n hn ↦ by haveI := NeZero.mk hn; exact (p n).map_zero]
    exact congr(p 0 $(Subsingleton.elim _ _))

open ContinuousLinearMap

private theorem factorial_smul' {n : ℕ} : ∀ {F : Type max u v} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {p : FormalMultilinearSeries 𝕜 E F}
    {f : E → F}, HasFPowerSeriesOnBall f p x r →
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  induction n with | zero => _ | succ n ih => _ <;> intro F _ _ _ p f h
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← ContinuousLinearMap.smul_apply, ih h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

variable [CompleteSpace F]
include h

theorem factorial_smul (n : ℕ) :
    n ! • p n (fun _ ↦ y) = iteratedFDeriv 𝕜 n f x (fun _ ↦ y) := by
  cases n
  · rw [factorial_zero, one_smul, h.iteratedFDeriv_zero_apply_diag]
  · rw [factorial_succ, mul_comm, mul_smul, ← derivSeries_apply_diag,
      ← ContinuousLinearMap.smul_apply, factorial_smul' _ h.fderiv, iteratedFDeriv_succ_apply_right]
    rfl

theorem hasSum_iteratedFDeriv [CharZero 𝕜] {y : E} (hy : y ∈ EMetric.ball 0 r) :
    HasSum (fun n ↦ (n ! : 𝕜)⁻¹ • iteratedFDeriv 𝕜 n f x fun _ ↦ y) (f (x + y)) := by
  convert h.hasSum hy with n
  rw [← h.factorial_smul y n, smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel₀ <| cast_ne_zero.mpr n.factorial_ne_zero, one_smul]

end HasFPowerSeriesOnBall
