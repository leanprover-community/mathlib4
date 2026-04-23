/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Bounds for values of Dirichlet characters

We consider Dirichlet characters `χ` with values in a normed field `F`.

We show that `‖χ a‖ = 1` if `a` is a unit and `‖χ a‖ ≤ 1` in general.
-/

public section

variable {F : Type*} [NormedField F] {n : ℕ} (χ : DirichletCharacter F n)

namespace DirichletCharacter

/-- The value at a unit of a Dirichlet character with target a normed field has norm `1`. -/
@[simp] lemma unit_norm_eq_one (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one,
    norm_one]

/-- The values of a Dirichlet character with target a normed field have norm bounded by `1`. -/
lemma norm_le_one (a : ZMod n) : ‖χ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one


end DirichletCharacter
