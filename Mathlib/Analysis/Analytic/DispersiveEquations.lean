import Mathlib.Tactic

noncomputable section
set_option linter.style.commandStart false

example: ∃! a : ℕ, a = 1 := by
  simp

variable {D: Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

variable (k: ℕ) (F: ((Fin k) → D) → D) (u_initial: Fin k → D)

def iteratedDerivs (k: ℕ) (u: ℝ → D): ℝ → (Fin k → D) := fun t ↦ (fun i ↦ iteratedDeriv i u t)

def solve_diffeq (a b: ℝ) (u: ℝ → D) := ∀ (i: Fin k), ∀ t ∈ Set.Ioo a b, (iteratedDeriv i u) t = F (iteratedDerivs k u t)

def solves_problem (a b: ℝ) (u: ℝ → D) (t₀: ℝ) := (t₀ ∈ Set.Ioo a b) ∧
  (iteratedDerivs k u t₀ = u_initial) ∧ (solve_diffeq k F a b u) ∧ (AnalyticOn ℝ u (Set.Ioo a b))

-- Probably should be formatted as a construction, then have a theorem about it working as intended...

theorem CauchyKowalevski(t₀: ℝ) : ∃ (a b: ℝ), ∃ (u: ℝ → D), solves_problem k F u_initial a b u t₀ := sorry
