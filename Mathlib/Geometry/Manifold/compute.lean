import Mathlib

noncomputable section

open InnerProductSpace
open scoped Real

section MissingLemmasInMathlib

/-! Mathlib did not know that the Laplacian in 1D was the second derivative, so we prove it. -/

theorem laplacianWithin_eq_iteratedDerivWithin_real {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {e : ℝ} {s : Set ℝ} (f : ℝ → F)
    (hs : UniqueDiffOn ℝ s) (he : e ∈ s) :
    (Δ[s] f) e = iteratedDerivWithin 2 f s e := by
  simp only [laplacianWithin_eq_iteratedFDerivWithin_orthonormalBasis f hs he
        (OrthonormalBasis.singleton (Fin 1) ℝ),
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, OrthonormalBasis.singleton_apply,
    Finset.sum_const, Finset.card_singleton, one_smul]
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
  congr
  ext i; fin_cases i <;> simp

theorem laplacian_eq_iteratedDeriv_real {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {e : ℝ} (f : ℝ → F) :
    Δ f e = iteratedDeriv 2 f e := by
  rw [← laplacianWithin_univ, laplacianWithin_eq_iteratedDerivWithin_real _ (by simp) (by simp),
    iteratedDerivWithin_univ]

end MissingLemmasInMathlib

/-- A definition of classical solutions to the heat equation. -/
def IsClassical1DHeatSolution (U : Set ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ u xt.1 xt.2) (U ×ˢ Set.Ioi 0)
    ∧ ∀ x ∈ U, ∀ t, 0 < t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

/-- `ℝ[n]` is notation for `EuclideanSpace ℝ (Fin n)` -/
macro "ℝ[" n:term "]" : term => `(EuclideanSpace ℝ (Fin $n))
/-- Notation for the standard orthonormal basis of `ℝ[n]` -/
local notation "e" => stdOrthonormalBasis ℝ _

variable {n : ℕ} {U : Set ℝ[n]} {u f g : ℝ[n] → ℝ} {x : ℝ[n]}
  {F : FormalMultilinearSeries ℝ ℝ[n] ℝ → ℝ[n] → ℝ}

/-- A definition of classical solutions to the heat equation. -/
def IsClassicalHeatSolution (U : Set ℝ[n]) (u : ℝ[n] → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun xt : ℝ[n] × ℝ ↦ u xt.1 xt.2) (U ×ˢ Set.Ioi 0)
    ∧ ∀ x ∈ U, ∀ t, 0 < t → deriv (fun s ↦ u x s) t - Δ (fun y ↦ u y t) x = 0

/-! Let's check a 1D solution. -/
section OneD

/-- The fundamental solution to the 1D heat equation. -/
def Ψ x t := (√(4 * π * t))⁻¹ * rexp (- x^2 / (4 * t))

/-- First derivative of Ψ with respect to time. -/
lemma deriv_Ψ_t {x t : ℝ} (ht : t > 0) :
    deriv (fun t ↦ Ψ x t) t = (Ψ x t) * (-2/t + x^2/t^2) / 4 := by
  simp_rw [Ψ]
  rw [deriv_fun_mul, deriv_fun_inv'', deriv_sqrt, deriv_const_mul, deriv_id'', deriv_exp,
    deriv_fun_div, deriv_const, deriv_const_mul, deriv_id'']
  · rw [Real.sq_sqrt (by positivity)]
    grind
  any_goals fun_prop (disch := positivity)
  all_goals positivity

/-- First derivative of Ψ with respect to space. -/
lemma deriv_Ψ_x {x t : ℝ} (ht : t > 0) :
    deriv (fun x ↦ Ψ x t) x = Ψ x t * (-x / (2 * t)) := by
  simp_rw [Ψ]
  simp only [deriv_const_mul_field']
  rw [mul_assoc _ _ (-x / (2 * t))]
  congr
  rw [deriv_exp (by fun_prop)]
  simp only [deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, mul_eq_mul_left_iff,
    Real.exp_ne_zero, or_false]
  field_simp
  ring

/-- Ψ is differentiable in space. -/
@[fun_prop]
lemma differentiableAt_Ψ (x t : ℝ) : DifferentiableAt ℝ (fun x ↦ Ψ x t) x := by
  unfold Ψ
  fun_prop

/-- Second derivative of Ψ with respect to space. -/
lemma deriv2_Ψ_x {x t : ℝ} (ht : t > 0) :
    iteratedDeriv 2 (fun x ↦ Ψ x t) x = (Ψ x t) * (-2/t + x^2/t^2) / 4 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one] -- copilot wrote that
  suffices deriv (fun x ↦ Ψ x t * (-x / (2 * t))) x = Ψ x t * (-2 / t + x ^ 2 / t ^ 2) / 4 by
    convert this using 2
    ext x
    exact deriv_Ψ_x ht
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_Ψ_x ht]
  simp only [deriv_div_const, deriv_neg'']
  grind

/-- Ψ is twice continuously differentiable on ℝ × (0, ∞). -/
lemma condDiff_two_Ψ : ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ Ψ xt.1 xt.2) (Set.univ ×ˢ Set.Ioi 0) := by
  simp_rw [Ψ]
  rintro ⟨x, t⟩ ht
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at ht
  fun_prop (disch := positivity)

/-- Ψ is a classical solution to the 1D heat equation on ℝ × (0, ∞). -/
lemma isClassical1DHeatSolution_Ψ :
    IsClassical1DHeatSolution (Set.univ : Set ℝ) Ψ := by
  constructor
  · exact condDiff_two_Ψ
  · intros x hx t ht
    rw [laplacian_eq_iteratedDeriv_real, deriv_Ψ_t ht, deriv2_Ψ_x ht]
    ring

end OneD

/-! Let's check the n-dimensional solution -/
section

/-- The fundamental solution to the n-dimensional heat equation. -/
def Ψ' : ℝ[n] → ℝ → ℝ := fun x t ↦ ((4 * π * t) ^ (((n : ℝ) / 2)))⁻¹ * rexp (- ‖x‖ ^ 2 / (4 * t))

/-- First derivative of Ψ' with respect to time. -/
lemma fderiv_Ψ'_t {x : ℝ[n]} {t : ℝ} (ht : t > 0) :
    deriv (fun t ↦ Ψ' x t) t = (Ψ' x t) * (-2 * n / t + ‖x‖ ^ 2/t^2) / 4 := by
  simp_rw [Ψ']
  rw [deriv_fun_mul, deriv_fun_inv'', deriv_rpow_const, deriv_const_mul, deriv_id'', deriv_exp,
    deriv_fun_div, deriv_const, deriv_const_mul, deriv_id'']
  · simp only [mul_one, zero_mul, neg_mul, sub_neg_eq_add, zero_add]
    -- Cancel common factors (which are positive).
    field_simp
    calc
      _ = -(2 * (4 * π * t) ^ ((n : ℝ) / 2) * ((2 * t)) * n) + 2 * (4 * π * t) ^ ((n : ℝ) / 2) * ‖x‖ ^ 2 := by
        congr! 1
        field_simp
        have (a : ℝ) : (a - 2) / 2 = a / 2 - 1 := by field_simp
        rw [this n, Real.rpow_sub_one (by positivity)]
        field_simp
        ring
      _ = _ := by
        field_simp
  any_goals fun_prop (disch := positivity)
  on_goal 2 => left
  all_goals positivity

#exit

/-- First derivative of Ψ' with respect to space. -/
lemma deriv_Ψ'_x {x : ℝ[n]} {t : ℝ} (ht : t > 0) :
    fderiv (fun x ↦ Ψ' x t) x = Ψ' x t * (-x / (2 * t)) := by
  simp_rw [Ψ]
  simp only [deriv_const_mul_field']
  rw [mul_assoc _ _ (-x / (2 * t))]
  congr
  rw [deriv_exp (by fun_prop)]
  simp only [deriv_div_const, deriv.fun_neg', differentiableAt_fun_id, deriv_fun_pow,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, mul_eq_mul_left_iff,
    Real.exp_ne_zero, or_false]
  field_simp
  ring

/-- Ψ' is differentiable in space. -/
@[fun_prop]
lemma differentiableAt_Ψ' (x t : ℝ) : DifferentiableAt ℝ (fun x ↦ Ψ' x t) x := by
  unfold Ψ'
  fun_prop

/-- Second derivative of Ψ with respect to space. -/
lemma deriv2_Ψ_x {x t : ℝ} (ht : t > 0) :
    iteratedDeriv 2 (fun x ↦ Ψ x t) x = (Ψ x t) * (-2/t + x^2/t^2) / 4 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one] -- copilot wrote that
  suffices deriv (fun x ↦ Ψ x t * (-x / (2 * t))) x = Ψ x t * (-2 / t + x ^ 2 / t ^ 2) / 4 by
    convert this using 2
    ext x
    exact deriv_Ψ_x ht
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_Ψ_x ht]
  simp only [deriv_div_const, deriv_neg'']
  grind

/-- Ψ is twice continuously differentiable on ℝ × (0, ∞). -/
lemma condDiff_two_Ψ : ContDiffOn ℝ 2 (fun xt : ℝ × ℝ ↦ Ψ xt.1 xt.2) (Set.univ ×ˢ Set.Ioi 0) := by
  simp_rw [Ψ]
  rintro ⟨x, t⟩ ht
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at ht
  fun_prop (disch := positivity)

/-- Ψ is a classical solution to the 1D heat equation on ℝ × (0, ∞). -/
lemma isClassical1DHeatSolution_Ψ :
    IsClassical1DHeatSolution (Set.univ : Set ℝ) Ψ := by
  constructor
  · exact condDiff_two_Ψ
  · intros x hx t ht
    rw [laplacian_eq_iteratedDeriv_real, deriv_Ψ_t ht, deriv2_Ψ_x ht]
    ring

end
