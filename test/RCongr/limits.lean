import Mathlib.Data.Real.Basic
import Mathlib.Tactic.RCongr.Basic

-- set_option trace.aesop true

example (f g : ℝ → ℝ) (a : ℝ)
    (hf : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - f a| < ε)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |g x - g a| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |(f * g) x - (f * g) a| < ε := by
  intro ε hε
  let η : ℝ := min 1 ((|f a| + |g a| + 1)⁻¹ * ε)
  have hε : 0 < η := by apply lt_min <;> positivity
  obtain ⟨δ1, hδ1, hf'⟩ := hf η hε
  obtain ⟨δ2, hδ2, hg'⟩ := hg η hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro x hx
  have hxδ1 : |f x - f a| < η
  · apply hf'
    calc |x - a| < min δ1 δ2 := hx
      _ ≤ δ1 := min_le_left _ _
  have hxδ2 : |g x - g a| < η
  · apply hg'
    calc |x - a| < min δ1 δ2 := hx
     _ ≤ δ2 := min_le_right _ _
  calc |(f * g) x - (f * g) a|
      = |f x * g x - f a * g a| := rfl
    _ = |(f x - f a) * (g x - g a) + (f x - f a) * g a + f a * (g x - g a)| := by
      congr! 1 -- want this to be `congrm |?_|`
      ring
    _ ≤ |(f x - f a) * (g x - g a) + (f x - f a) * g a| + |f a * (g x - g a)| := by apply abs_add
    _ ≤ |(f x - f a) * (g x - g a)| + |(f x - f a) * g a| + |f a * (g x - g a)| := by
      rcongr (add apply safe abs_add)
    _ = |f x - f a| * |g x - g a| + |f x - f a| * |g a| + |f a| * |g x - g a| := by simp only [abs_mul]
    _ < η * η + η * |g a| + |f a| * η := by rcongr
    _ = η * (|f a| + |g a| + η) := by ring
    _ ≤ ((|f a| + |g a| + 1)⁻¹ * ε) * (|f a| + |g a| + 1) := by
      rcongr (add safe apply min_le_right, safe apply min_le_left)
    _ = ε := by
      have h : 0 < |f a| + |g a| + 1 := by positivity
      field_simp [h.ne']
