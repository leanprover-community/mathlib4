/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/

namespace AbsoluteValue

variable {R : Type*} [Semiring R]

/-- Two absolute values `f, g` on `R` with values in `ℝ` are *equivalent* if there exists
a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`. -/
def Equiv (f g : AbsoluteValue R ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (f · ^ c) = g

/-- Equivalence of absolute values is reflexive. -/
lemma equiv_refl (f : AbsoluteValue R ℝ) : Equiv f f :=
  ⟨1, Real.zero_lt_one, funext fun x ↦ Real.rpow_one (f x)⟩

/-- Equivalence of absolute values is symmetric. -/
lemma equiv_symm {f g : AbsoluteValue R ℝ} (hfg : Equiv f g) : Equiv g f := by
  rcases hfg with ⟨c, hcpos, h⟩
  refine ⟨1 / c, one_div_pos.mpr hcpos, ?_⟩
  simp [← h, Real.rpow_rpow_inv (apply_nonneg f _) (ne_of_lt hcpos).symm]

/-- Equivalence of absolute values is transitive. -/
lemma equiv_trans {f g k : AbsoluteValue R ℝ} (hfg : Equiv f g) (hgk : Equiv g k) :
    Equiv f k := by
  rcases hfg with ⟨c, hcPos, hfg⟩
  rcases hgk with ⟨d, hdPos, hgk⟩
  refine ⟨c * d, mul_pos hcPos hdPos, ?_⟩
  simp [← hgk, ← hfg, Real.rpow_mul (apply_nonneg f _)]

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma eq_trivial_of_equiv_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    (f : AbsoluteValue R ℝ) :
    f.Equiv .trivial ↔ f = .trivial := by
  refine ⟨fun ⟨c, hc₀, hc⟩ ↦ ext fun x ↦ ?_, fun H ↦ H ▸ equiv_refl f⟩
  apply_fun (· x) at hc
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [ne_eq, hx, not_false_eq_true, trivial_apply] at hc ⊢
    exact (Real.rpow_left_inj (f.nonneg x) zero_le_one hc₀.ne').mp <| (Real.one_rpow c).symm ▸ hc

instance : Setoid (AbsoluteValue R ℝ) where
  r := Equiv
  iseqv := {
    refl := equiv_refl
    symm := equiv_symm
    trans := equiv_trans
  }

end AbsoluteValue