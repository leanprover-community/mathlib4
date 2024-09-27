import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ∞} {f g : E → ℝ} {s : Set E} {x : E}

theorem contDiffAt_abs {x : ℝ} (hx : x ≠ 0) : ContDiffAt ℝ n (|·|) x := contDiffAt_norm ℝ hx

theorem ContDiffAt.abs (hf : ContDiffAt ℝ n f x) (h₀ : f x ≠ 0) :
    ContDiffAt ℝ n (fun x ↦ |f x|) x := hf.norm ℝ h₀

theorem contDiffWithinAt_abs {x : ℝ} (hx : x ≠ 0) (s : Set ℝ) :
    ContDiffWithinAt ℝ n (|·|) s x := (contDiffAt_abs hx).contDiffWithinAt

theorem ContDiffWithinAt.abs (hf : ContDiffWithinAt ℝ n f s x) (h₀ : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y ↦ |f y|) s x :=
  (contDiffAt_abs h₀).comp_contDiffWithinAt x hf

theorem contDiffOn_abs {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContDiffOn ℝ n (|·|) s := fun x hx ↦ contDiffWithinAt_abs (hs x hx) s

theorem ContDiffOn.abs (hf : ContDiffOn ℝ n f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y ↦ |f y|) s := fun x hx ↦ (hf x hx).abs (h₀ x hx)

theorem ContDiff.abs (hf : ContDiff ℝ n f) (h₀ : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y ↦ |f y| :=
  contDiff_iff_contDiffAt.2 fun x ↦ hf.contDiffAt.abs (h₀ x)

theorem hasStrictDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasStrictDerivAt (|·|) (-1) x :=
  (hasStrictDerivAt_neg x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_neg (mem_Iio.1 hy)).symm) (Iio_mem_nhds hx)

theorem hasDerivAt_abs_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt (|·|) (-1) x := (hasStrictDerivAt_abs_neg hx).hasDerivAt

theorem hasStrictDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (|·|) 1 x :=
  (hasStrictDerivAt_id x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

theorem hasDerivAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt (|·|) 1 x := (hasStrictDerivAt_abs_pos hx).hasDerivAt

theorem hasStrictDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (|·|) (SignType.sign x : ℝ) x := by
  obtain hx | hx := hx.lt_or_lt
  · simpa [hx] using hasStrictDerivAt_abs_neg hx
  · simpa [hx] using hasStrictDerivAt_abs_pos hx

theorem hasDerivAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (|·|) (SignType.sign x : ℝ) x := (hasStrictDerivAt_abs hx).hasDerivAt

theorem HasStrictFDerivAt.abs_of_neg {f' : E →L[ℝ] ℝ} (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x < 0) : HasStrictFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert (hasStrictDerivAt_abs_neg h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasFDerivAt.abs_of_neg {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x)
    (h₀ : f x < 0) : HasFDerivAt (fun x ↦ |f x|) (-f') x := by
  convert (hasDerivAt_abs_neg h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasStrictFDerivAt.abs_of_pos {f' : E →L[ℝ] ℝ} (hf : HasStrictFDerivAt f f' x)
    (h₀ : 0 < f x) : HasStrictFDerivAt (fun x ↦ |f x|) f' x := by
  convert (hasStrictDerivAt_abs_pos h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasFDerivAt.abs_of_pos {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x)
    (h₀ : 0 < f x) : HasFDerivAt (fun x ↦ |f x|) f' x := by
  convert (hasDerivAt_abs_pos h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp

theorem HasStrictFDerivAt.abs {f' : E →L[ℝ] ℝ} (hf : HasStrictFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasStrictFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert (hasStrictDerivAt_abs h₀).hasStrictFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

theorem HasFDerivAt.abs {f' : E →L[ℝ] ℝ} (hf : HasFDerivAt f f' x)
    (h₀ : f x ≠ 0) : HasFDerivAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert (hasDerivAt_abs h₀).hasFDerivAt.comp x hf using 1
  ext y
  simp [mul_comm]

theorem hasDerivWithinAt_abs_neg (s : Set ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivWithinAt (|·|) (-1) s x := (hasDerivAt_abs_neg hx).hasDerivWithinAt

theorem hasDerivWithinAt_abs_pos (s : Set ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 s x := (hasDerivAt_abs_pos hx).hasDerivWithinAt

theorem hasDerivWithinAt_abs (s : Set ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt (|·|) (SignType.sign x : ℝ) s x := (hasDerivAt_abs hx).hasDerivWithinAt

theorem hasDerivWithinAt_abs_pos {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (|·|) 1 x :=
  (hasDerivWithinAt_id x).congr_of_eventuallyEq <|
    EqOn.eventuallyEq_of_mem (fun _ hy ↦ (abs_of_pos (mem_Iio.1 hy)).symm) (Ioi_mem_nhds hx)

theorem hasDerivWithinAt_abs {x : ℝ} (hx : x ≠ 0) :
    HasDerivWithinAt (|·|) (SignType.sign x : ℝ) x := by
  obtain hx | hx := hx.lt_or_lt
  · simpa [hx] using hasDerivWithinAt_abs_neg hx
  · simpa [hx] using hasDerivWithinAt_abs_pos hx

theorem hasFDerivWithinAt.abs_of_neg {f' : E →L[ℝ] ℝ} (hf : hasFDerivWithinAt f f' x)
    (h₀ : f x < 0) : hasFDerivWithinAt (fun x ↦ |f x|) (-f') x := by
  convert (hasStrictDerivAt_abs_neg h₀).hasFDerivWithinAt.comp x hf using 1
  ext y
  simp

theorem hasFDerivWithinAt.abs_of_pos {f' : E →L[ℝ] ℝ} (hf : hasFDerivWithinAt f f' x)
    (h₀ : 0 < f x) : hasFDerivWithinAt (fun x ↦ |f x|) f' x := by
  convert (hasStrictDerivAt_abs_pos h₀).hasFDerivWithinAt.comp x hf using 1
  ext y
  simp

theorem hasFDerivWithinAt.abs {f' : E →L[ℝ] ℝ} (hf : hasFDerivWithinAt f f' x)
    (h₀ : f x ≠ 0) : hasFDerivWithinAt (fun x ↦ |f x|) ((SignType.sign (f x) : ℝ) • f') x := by
  convert (hasStrictDerivAt_abs h₀).hasFDerivWithinAt.comp x hf using 1
  ext y
  simp [mul_comm]

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
