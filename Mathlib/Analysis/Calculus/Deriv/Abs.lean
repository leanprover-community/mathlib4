import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

open Filter Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ∞} {f g : E → ℝ} {s : Set E} {x : E}

theorem contDiffAt_abs {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ n (|·|) x := by
  obtain hx | hx := hx.lt_or_lt
  · apply contDiff_neg.contDiffAt.congr_of_eventuallyEq
    exact EqOn.eventuallyEq_of_mem (fun y hy ↦ abs_of_neg (mem_Iio.1 hy)) (Iio_mem_nhds hx)
  · apply contDiff_id.contDiffAt.congr_of_eventuallyEq
    exact EqOn.eventuallyEq_of_mem (fun y hy ↦ abs_of_pos (mem_Iio.1 hy)) (Ioi_mem_nhds hx)

theorem ContDiffAt.abs (hf : ContDiffAt ℝ n f x) (h₀ : f x ≠ 0) :
    ContDiffAt ℝ n (fun x ↦ |f x|) x :=
  (contDiffAt_abs h₀).comp x hf

theorem ContDiffWithinAt.abs (hf : ContDiffWithinAt ℝ n f s x) (h₀ : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y ↦ |f y|) s x :=
  (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

theorem ContDiffOn.abs (hf : ContDiffOn ℝ n f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y ↦ |f y|) s := fun x hx ↦ (hf x hx).abs (h₀ x hx)

theorem ContDiff.abs (hf : ContDiff ℝ n f) (h₀ : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y ↦ |f y| :=
  contDiff_iff_contDiffAt.2 fun x ↦ hf.contDiffAt.abs (h₀ x)

theorem not_differentiableAt_abs_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  intro h
  have h₁ : deriv abs (0 : ℝ) = 1 :=
    (uniqueDiffOn_Ici _ _ Set.left_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_id _ _).congr_of_mem (fun _ h ↦ abs_of_nonneg h) Set.left_mem_Ici
  have h₂ : deriv abs (0 : ℝ) = -1 :=
    (uniqueDiffOn_Iic _ _ Set.right_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt <|
      (hasDerivWithinAt_neg _ _).congr_of_mem (fun _ h ↦ abs_of_nonpos h) Set.right_mem_Iic
  linarith

theorem deriv_abs (x : ℝ) : deriv (|·|) x = SignType.sign x := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · rw [EventuallyEq.deriv_eq (f := fun x ↦ -x)]
    · simp [hx]
    · rw [EventuallyEq, eventually_iff_exists_mem]
      exact ⟨Iic 0, Iic_mem_nhds hx, by simp [hx]⟩
  · rw [deriv_zero_of_not_differentiableAt not_differentiableAt_abs_zero]
    simp
  · rw [EventuallyEq.deriv_eq (f := id)]
    · simp [hx]
    · rw [EventuallyEq, eventually_iff_exists_mem]
      exact ⟨Ici 0, Ici_mem_nhds hx, by simp [hx]⟩

theorem hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) : HasDerivAt abs (SignType.sign x : ℝ) x := by
  convert (differentiableAt_of_deriv_ne_zero ?_).hasDerivAt
  · rw [deriv_abs]
  · obtain hx | hx := hx.lt_or_lt
    all_goals rw [deriv_abs]; simp [hx]

theorem differentiableAt_abs {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ abs x :=
  (hasDerivAt_abs hx).differentiableAt
