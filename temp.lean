import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

theorem Isometry.separableMetricSpace {α : Type u_1} {β : Type u_2} [MetricSpace α]
  [MetricSpace β] {f : α → β} [TopologicalSpace.SeparableSpace β]
    (hf : Embedding f) : TopologicalSpace.SeparableSpace α := by
    have := UniformSpace.secondCountable_of_separable β
    have := Embedding.secondCountableTopology hf
    exact TopologicalSpace.SecondCountableTopology.to_separableSpace


theorem biSup_range_eq {α : Type*} [CompleteSemilatticeSup α] (f : ℕ → α) (N : ℕ) :
    ⨆ n ∈ Finset.range (N + 1), f n = ⨆ n ∈ {n | n ≤ N}, f n := by simp [Nat.lt_add_one_iff]

#find_home! biSup_range_eq


-- Harmonic functions on the plane

variable (α : Type*) (l₁ : Filter α ) (l₂ : Filter α)

#check l₁ ≤ l₂

noncomputable

def laplace : (ℂ → ℝ) → (ℂ → ℝ) := by

  intro f
  let F : ℝ × ℝ → ℝ := fun x ↦ f (x.1 + x.2 * Complex.I)

  let e₁ : ℝ × ℝ := ⟨1, 0⟩
  let e₂ : ℝ × ℝ := ⟨0, 1⟩

  let F₁ := fun x ↦ lineDeriv ℝ F x e₁
  let F₁₁ := fun x ↦ lineDeriv ℝ F₁ x e₁
  let F₂ := fun x ↦ lineDeriv ℝ F x e₂
  let F₂₂ := fun x ↦ lineDeriv ℝ F₂ x e₂

  exact fun x ↦ F₁₁ ⟨x.1, x.2⟩ + F₂₂ ⟨x.1, x.2⟩


example : ∀ z₀ : ℂ, laplace (fun z ↦ (z*z).re) z₀ = 0 := by
  intro z₀
  unfold laplace
  dsimp [lineDeriv]
  simp
  conv =>
    lhs
    lhs
    arg 1
    intro t
    rw [deriv_sub] <;> tactic => try fun_prop
    rw [deriv_mul] <;> tactic => try fun_prop
    rw [deriv_const_add]
    simp
    ring_nf
  conv =>
    lhs
    rhs
    arg 1
    intro t
    rw [deriv_sub] <;> tactic => try fun_prop
    rw [deriv_const]
    rw [deriv_mul] <;> tactic => try fun_prop
    rw [deriv_const_add]
    simp
    ring_nf
  rw [deriv_const_add, deriv_sub] <;> try fun_prop
  simp


example : ∀ z₀ : ℂ, laplace (fun z ↦ (Complex.exp z).re) z₀ = 0 := by
  intro z₀
  unfold laplace
  dsimp [lineDeriv]
  simp
  conv =>
    lhs
    lhs
    arg 1
    intro t
    tactic =>
      simp_rw [Complex.exp_re]
      simp
    rw [deriv_exp] <;> tactic => try fun_prop
    rw [deriv_const_add]
    simp
  conv =>
    lhs
    lhs
    rw [deriv_mul] <;> tactic => try fun_prop
    rw [deriv_const]
    rw [deriv_exp] <;> tactic => try fun_prop
    rw [deriv_const_add]
    simp
  conv =>
    lhs
    rhs
    arg 1
    intro t
    tactic =>
      simp_rw [Complex.exp_re]
      simp
    rhs
    rw [deriv_cos] <;> tactic => try fun_prop
    rw [deriv_const_add]
    simp
  conv =>
    lhs
    rhs
    arg 1
    intro t
    rw [← Real.sin_neg]
    simp
  conv =>
    lhs
    rhs
    rw [deriv_const_mul] <;> tactic => try fun_prop
    rhs
    simp
    rw [deriv_sin] <;> tactic => try fun_prop
    simp
    · skip
    tactic =>
      apply DifferentiableAt.sin
      fun_prop
  simp
