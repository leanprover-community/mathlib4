import Mathlib.Tactic.DataSynth.FDeriv.Simproc
import Mathlib.Tactic.DataSynth.FDeriv.Dispatch

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
-- import Mathlib.Analysis.Calculus.FDeriv.WithLp

import Mathlib.Tactic.FieldSimp

set_option autoImplicit true

syntax (name:=noFDerivTacStx) "check_no_fderiv" : conv

open Lean Elab Tactic in
@[tactic noFDerivTacStx]
def noFDerivTac : Tactic := fun stx => do
  let goal ← getMainGoal
  let type ← goal.getType

  if type.containsConst (·==``fderiv) then
    throwErrorAt stx m!"goal {type} still contains `fderiv`!"
  pure ()

-------------------------------------------------------------------------------------

attribute [data_synth]
  HasFDerivAt.pow
  HasFDerivAt.rpow HasFDerivAt.norm_sq
  HasFDerivAt.inner
  HasFDerivAt.fun_smul HasFDerivAt.prodMk
  HasFDerivAt.clm_comp HasFDerivAt.clm_apply

example (g : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (x dx : ℝ) {g' : ℝ →L[ℝ] ℝ} {f' : ℝ × ℝ →L[ℝ] ℝ}
    (hg : HasFDerivAt g g' x) (hf : HasFDerivAt (fun yx : ℝ×ℝ => f yx.1 yx.2) f' (g x, x)) :
    fderiv ℝ (fun x : ℝ => let y := g x; f y x) x dx
    =
    let dy := g' dx
    let dz := f' (dy,dx)
    dz := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

example (x₀ : ℝ) : fderiv ℝ (fun x : ℝ => x) x₀ 1 = 1 := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

example (x₀ : ℝ) : fderiv ℝ (fun x : ℝ => x*x) x₀ 1 = x₀ + x₀ := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

example (x₀ : ℝ) : fderiv ℝ (fun x : ℝ => 2*x) x₀ 1 = 2 := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

example (x₀ : ℝ) (h : x₀ ≠ 0) : fderiv ℝ (fun x : ℝ => x⁻¹) x₀ 1 = -(x₀ ^ 2)⁻¹ := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

example (x₀ : ℝ) (h : x₀ ≠ 0) :
    fderiv ℝ (fun x : ℝ => (x*x)⁻¹) x₀ 1
    =
    -(x₀ * ((x₀ * x₀) ^ 2)⁻¹) + -(x₀ * ((x₀ * x₀) ^ 2)⁻¹) := by
  conv_lhs =>
    simp (disch:=aesop) only [fderiv_simproc]
    check_no_fderiv
    simp


example (v t : ℝ) : deriv (fun t : ℝ => 1/2 * v * t^2) t = v * t := by
  rw [← fderiv_deriv]
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

  field_simp [mul_comm, mul_assoc]


open InnerProductSpace
example (n : ℕ) (x y : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun x => (‖x‖ ^ 2 + 1/(n + 1))^ (-1/2 : ℝ)) x y
    =
    - ((‖x‖ ^ 2 + (1 + (n : ℝ))⁻¹) ^ (- 1/2 : ℝ)) ^ 3 * ⟪x, y⟫_ℝ  := by
  conv_lhs =>
    simp (disch:=positivity) only [fderiv_simproc]
    check_no_fderiv
    simp

  field_simp (disch:=positivity) [← Real.rpow_mul_natCast]
  norm_num
  simp only [add_comm, mul_comm, mul_assoc]


lemma wave_dt {d} (c : ℝ) (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    {x s : EuclideanSpace ℝ (Fin d)} {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) (t : ℝ) :
    fderiv ℝ (fun t => f₀ (inner ℝ x s - c * t)) t 1 =
    -c • (f₀' (inner ℝ x s - c * t)) 1 := by
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp
  simp

set_option autoImplicit true in
lemma wave_dx {u v : Fin d} {s : EuclideanSpace ℝ (Fin d)}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    (fun x' => fderiv ℝ (fun x => (inner ℝ (f₀ (inner ℝ x s - c * t))
    (EuclideanSpace.single u 1))) x' (EuclideanSpace.single v 1))
    =
    fun x' => (inner ℝ (f₀' (inner ℝ x' s - c * t) (s v))
    (EuclideanSpace.single u 1)) := by
  have h : ⟪EuclideanSpace.single v 1, s⟫_ℝ = s v := sorry
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp [h]


open Real
example (t ω : ℝ) (hω : ω ≠ 0) (x₀ v₀ : EuclideanSpace ℝ (Fin 1)) :
    (fderiv ℝ (fun t => cos (ω * t) • x₀ + (sin (ω * t) / ω) • v₀) t) 1 =
    -ω • sin (ω * t) • x₀ + cos (ω * t) • v₀:= by

  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp

  field_simp [mul_comm, smul_smul]

lemma wave_dx2 {u v : Fin d} {s : EuclideanSpace ℝ (Fin d)}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {f₀'' : ℝ → ℝ →L[ℝ] ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x') (f₀'' x) x) :
    (fderiv ℝ (fun x' => (inner ℝ ((f₀' (inner ℝ x' s - c * t)) (s u))
    (EuclideanSpace.single v 1))) x) (EuclideanSpace.single u 1)
    =
    inner ℝ (f₀'' (⟪x, s⟫_ℝ - c * t) (s u) (s u)) (EuclideanSpace.single v 1) := by

  have h : ⟪EuclideanSpace.single u 1, s⟫_ℝ = s u := by simp [PiLp.inner_apply]
  conv_lhs =>
    simp only [fderiv_simproc]
    check_no_fderiv
    simp [h]
