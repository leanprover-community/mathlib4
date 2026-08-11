/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.QuadraticAlgebra.Discr
public import Mathlib.Data.Rat.Squarefree

/-!
# Quadratic algebras over `ℚ`

Every quadratic algebra over `ℚ` with nonzero discriminant is isomorphic to a standard form
`QuadraticAlgebra ℚ d 0` for a unique squarefree integer `d`. This classifies quadratic algebras
over `ℚ` by squarefree integers.

## Main results

* `QuadraticAlgebra.Rat.exists_squarefree_algEquiv`: every `QuadraticAlgebra ℚ a b` with nonzero
  discriminant is isomorphic to `QuadraticAlgebra ℚ d 0` for a squarefree integer `d`.
* `QuadraticAlgebra.Rat.nonempty_algEquiv_iff`: over `ℚ`, the squarefree integer `d` is a
  complete invariant of the standard form `QuadraticAlgebra ℚ d 0`.
-/

public section

namespace QuadraticAlgebra.Rat

/-- Every `QuadraticAlgebra ℚ a b` with nonzero discriminant is isomorphic to
`QuadraticAlgebra ℚ d 0` for a squarefree integer `d`. -/
theorem exists_squarefree_algEquiv (a b : ℚ) (hd : discr a b ≠ 0) :
    ∃ d : ℤ, Squarefree d ∧
      Nonempty (QuadraticAlgebra ℚ a b ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  obtain ⟨d, r, hd', hc⟩ := Rat.exists_sq_mul_squarefree (discr a b)
  have hr : r ≠ 0 := by
    intro rfl
    exact hd (by simpa using hc)
  exact ⟨d, hd', ⟨(algEquivDiscrZero a b).trans
    (mapEquiv (d : ℚ) 0 (Units.mk0 r hr) 0 (by simpa [Units.val_mk0] using hc) (by ring))⟩⟩

/-- For squarefree integers `d₁`, `d₂`, the standard forms `QuadraticAlgebra ℚ d₁ 0` and
`QuadraticAlgebra ℚ d₂ 0` are isomorphic if and only if `d₁ = d₂`. -/
theorem nonempty_algEquiv_iff {d₁ d₂ : ℤ} (h₁ : Squarefree d₁) (h₂ : Squarefree d₂) :
    Nonempty (QuadraticAlgebra ℚ (d₁ : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (d₂ : ℚ) 0) ↔ d₁ = d₂ := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨h ▸ AlgEquiv.refl⟩⟩
  have hd := discr_eq_im_sq_mul_discr' e
  rw [discr_def, discr_def] at hd
  exact Rat.sq_mul_squarefree_unique h₁ h₂ _ (e ω).im one_ne_zero (by grind)

end QuadraticAlgebra.Rat
