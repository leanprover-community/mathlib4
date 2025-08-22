/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of the complex `log` function

-/

assert_not_exists IsConformalMap Conformal

open Set Filter

open scoped Real Topology

namespace Complex

theorem isOpenMap_exp : IsOpenMap exp :=
  isOpenMap_of_hasStrictDerivAt hasStrictDerivAt_exp exp_ne_zero

/-- `Complex.exp` as a `PartialHomeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}`. This definition is used to prove that `Complex.log`
is complex differentiable at all points but the negative real semi-axis. -/
noncomputable def expPartialHomeomorph : PartialHomeomorph ℂ ℂ :=
  PartialHomeomorph.ofContinuousOpen
    { toFun := exp
      invFun := log
      source := {z : ℂ | z.im ∈ Ioo (-π) π}
      target := slitPlane
      map_source' := by
        rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
        refine (not_or_of_imp fun hz => ?_).symm
        obtain rfl : y = 0 := by
          rw [exp_im] at hz
          simpa [(Real.exp_pos _).ne', Real.sin_eq_zero_iff_of_lt_of_lt h₁ h₂] using hz
        rw [← ofReal_def, exp_ofReal_re]
        exact Real.exp_pos x
      map_target' := fun z h => by
        simp only [mem_setOf, log_im, mem_Ioo, neg_pi_lt_arg, arg_lt_pi_iff, true_and]
        exact h.imp_left le_of_lt
      left_inv' := fun _ hx => log_exp hx.1 (le_of_lt hx.2)
      right_inv' := fun _ hx => exp_log <| slitPlane_ne_zero hx }
    continuous_exp.continuousOn isOpenMap_exp (isOpen_Ioo.preimage continuous_im)

theorem hasStrictDerivAt_log {x : ℂ} (h : x ∈ slitPlane) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x ≠ 0 := slitPlane_ne_zero h
  expPartialHomeomorph.hasStrictDerivAt_symm h h0 <| by
    simpa [exp_log h0] using hasStrictDerivAt_exp (log x)

lemma hasDerivAt_log {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log z⁻¹ z :=
  HasStrictDerivAt.hasDerivAt <| hasStrictDerivAt_log hz

@[fun_prop]
lemma differentiableAt_log {z : ℂ} (hz : z ∈ slitPlane) : DifferentiableAt ℂ log z :=
  (hasDerivAt_log hz).differentiableAt

@[fun_prop]
theorem hasStrictFDerivAt_log_real {x : ℂ} (h : x ∈ slitPlane) :
    HasStrictFDerivAt log (x⁻¹ • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_log h).complexToReal_fderiv

theorem contDiffAt_log {x : ℂ} (h : x ∈ slitPlane) {n : WithTop ℕ∞} : ContDiffAt ℂ n log x :=
  expPartialHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt

end Complex

section LogDeriv

open Complex Filter

open scoped Topology

variable {α : Type*} [TopologicalSpace α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictFDerivAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {x : E}
    (h₁ : HasStrictFDerivAt f f' x) (h₂ : f x ∈ slitPlane) :
    HasStrictFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).comp_hasStrictFDerivAt x h₁

theorem HasStrictDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).comp x h₁

theorem HasStrictDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using (hasStrictFDerivAt_log_real h₂).comp_hasStrictDerivAt x h₁

theorem HasFDerivAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {x : E} (h₁ : HasFDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasFDerivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivAt x h₁

theorem HasDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]; exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁

theorem HasDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : f x ∈ slitPlane) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivAt x h₁

theorem DifferentiableAt.clog {f : E → ℂ} {x : E} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ slitPlane) : DifferentiableAt ℂ (fun t => log (f t)) x :=
  (h₁.hasFDerivAt.clog h₂).differentiableAt

theorem HasFDerivWithinAt.clog {f : E → ℂ} {f' : StrongDual ℂ E} {s : Set E} {x : E}
    (h₁ : HasFDerivWithinAt f f' s x) (h₂ : f x ∈ slitPlane) :
    HasFDerivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFDerivWithinAt x h₁

theorem HasDerivWithinAt.clog {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ} (h₁ : HasDerivWithinAt f f' s x)
    (h₂ : f x ∈ slitPlane) : HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁

theorem HasDerivWithinAt.clog_real {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} {f' : ℂ}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : f x ∈ slitPlane) :
    HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  simpa only [div_eq_inv_mul] using
    (hasStrictFDerivAt_log_real h₂).hasFDerivAt.comp_hasDerivWithinAt x h₁

theorem DifferentiableWithinAt.clog {f : E → ℂ} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt ℂ f s x) (h₂ : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun t => log (f t)) s x :=
  (h₁.hasFDerivWithinAt.clog h₂).differentiableWithinAt

theorem DifferentiableOn.clog {f : E → ℂ} {s : Set E} (h₁ : DifferentiableOn ℂ f s)
    (h₂ : ∀ x ∈ s, f x ∈ slitPlane) : DifferentiableOn ℂ (fun t => log (f t)) s :=
  fun x hx => (h₁ x hx).clog (h₂ x hx)

theorem Differentiable.clog {f : E → ℂ} (h₁ : Differentiable ℂ f)
    (h₂ : ∀ x, f x ∈ slitPlane) : Differentiable ℂ fun t => log (f t) := fun x =>
  (h₁ x).clog (h₂ x)

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
we are on the slitPlane. -/
lemma Complex.deriv_log_comp_eq_logDeriv {f : ℂ → ℂ} {x : ℂ} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : f x ∈ Complex.slitPlane) : deriv (Complex.log ∘ f) x = logDeriv f x := by
  have A := (HasDerivAt.clog h₁.hasDerivAt h₂).deriv
  rw [← h₁.hasDerivAt.deriv] at A
  simp only [logDeriv, Pi.div_apply, ← A, Function.comp_def]

end LogDeriv
