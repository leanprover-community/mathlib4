module

public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Complex.Basic

/-! # Tests for `gcongr` and `grw` with `=O` and `=o` -/

open Asymptotics Filter

variable {α E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {l : Filter α}

/-! ### `=O` goals with `=O` rules -/

example {f : α → E} {g k : α → F} (h₁ : f =O[l] g) (h₂ : g =O[l] k) : f =O[l] k := by
  grw [← h₂]
  exact h₁

example {f g : α → E} {k : α → F} (h₁ : f =O[l] g) (h₂ : g =O[l] k) : f =O[l] k := by
  grw [h₁]
  exact h₂

example {f : α → E} {g k : α → F} (h₁ : f =O[l] g) (h₂ : g =O[l] k) : f =O[l] k := by
  grw [h₂] at h₁
  exact h₁

example {f g : α → E} {k : α → F} (h₁ : f =O[l] g) (h₂ : g =O[l] k) : f =O[l] k := by
  grw [← h₁] at h₂
  exact h₂

example {f : α → E} {g₁ g₂ : α → F} (h : g₁ =O[l] g₂) : f =O[l] g₁ → f =O[l] g₂ := by
  gcongr

example {f₁ f₂ : α → E} {g : α → F} (h : f₁ =O[l] f₂) : f₂ =O[l] g → f₁ =O[l] g := by
  gcongr

example {f₁ f₂ : α → E} {g₁ g₂ : α → F} (hf : f₁ =O[l] f₂) (hg : g₁ =O[l] g₂) :
    f₂ =O[l] g₁ → f₁ =O[l] g₂ := by
  gcongr

example {f₁ f₂ : α → E} {g₁ g₂ : α → F} (hf : f₁ =O[l] f₂) (hg : g₁ =O[l] g₂) :
    f₂ =o[l] g₁ → f₁ =o[l] g₂ := by
  gcongr

/-! ### `=O` goals with `=o` rules, using the `gcongr_forward` extension -/

example {f : α → E} {g k : α → F} (h₁ : f =O[l] g) (h₂ : g =o[l] k) : f =O[l] k := by
  grw [← h₂]
  exact h₁

example {f g : α → E} {k : α → F} (h₁ : f =o[l] g) (h₂ : g =O[l] k) : f =O[l] k := by
  grw [h₁]
  exact h₂

/-! ### `=o` goals with `=O` rules -/

example {f : α → E} {g k : α → F} (h₁ : f =o[l] g) (h₂ : g =O[l] k) : f =o[l] k := by
  grw [← h₂]
  exact h₁

example {f g : α → E} {k : α → F} (h₁ : f =O[l] g) (h₂ : g =o[l] k) : f =o[l] k := by
  grw [h₁]
  exact h₂

example {f : α → E} {g k : α → F} (h₁ : f =o[l] g) (h₂ : g =O[l] k) : f =o[l] k := by
  grw [h₂] at h₁
  exact h₁

/-! ### `=o` goals with `=o` rules: the goal becomes an `=O` goal -/

example {f g : α → E} {k : α → F} (h₁ : f =o[l] g) (h₂ : g =O[l] k) : f =o[l] k := by
  grw [h₁]
  guard_target =ₛ g =O[l] k
  exact h₂

example {f : α → E} {g k : α → F} (h₁ : f =O[l] g) (h₂ : g =o[l] k) : f =o[l] k := by
  grw [← h₂]
  guard_target =ₛ f =O[l] g
  exact h₁

/-! ### A `ℂ`-valued function with real-valued bounds -/

example {f : ℝ → ℂ} (h₁ : f =O[atTop] fun t ↦ t ^ 2)
    (h₂ : (fun t : ℝ ↦ t ^ 2) =O[atTop] fun t ↦ t ^ 3) :
    f =O[atTop] fun t ↦ t ^ 3 := by
  grw [← h₂]
  exact h₁

example {f : ℝ → ℂ} (h₁ : f =O[atTop] fun t ↦ t ^ 2)
    (h₂ : (fun t : ℝ ↦ t ^ 2) =o[atTop] fun t ↦ t ^ 3) :
    f =o[atTop] fun t ↦ t ^ 3 := by
  grw [← h₂]
  exact h₁
