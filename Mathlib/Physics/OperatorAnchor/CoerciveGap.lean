import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open scoped RealInnerProductSpace

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coercivity via the quadratic form inequality. -/
def Coercive (A : H → H) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : H, c * ⟪x, x⟫ ≤ ⟪A x, x⟫

/-- Rayleigh lower bound from coercivity. -/
theorem rayleigh_lower_bound_of_coercive
    (A : H → H) (hA : Coercive A) :
    ∃ c : ℝ, 0 < c ∧ ∀ {x : H}, x ≠ 0 → c ≤ ⟪A x, x⟫ / ⟪x, x⟫ := by
  rcases hA with ⟨c, hcpos, hineq⟩
  refine ⟨c, hcpos, ?_⟩
  intro x hx
  have h := hineq x
  have hpos : 0 < ⟪x, x⟫ := by
    have hxnorm : ‖x‖ ≠ 0 := by
      intro h0
      have : x = 0 := by simpa [norm_eq_zero] using h0
      exact hx this
    simpa using sq_pos_of_ne_zero hxnorm
  exact (le_div_iff₀ hpos).2 h
