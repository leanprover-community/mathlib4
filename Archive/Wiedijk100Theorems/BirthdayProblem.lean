/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module wiedijk_100_theorems.birthday_problem
! leanprover-community/mathlib commit 5563b1b49e86e135e8c7b556da5ad2f5ff881cad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Probability.CondCount
import Mathlib.Probability.Notation

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As opposed to the standard probabilistic statement, we instead state the birthday problem
in terms of injective functions. The general result about `fintype.card (α ↪ β)` which this proof
uses is `fintype.card_embedding_eq`.
-/


namespace Theorems100

local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

/-- **Birthday Problem**: set cardinality interpretation. -/
theorem birthday :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧ 2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ := by
  simp only [Nat.descFactorial, Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_fun]
#align theorems_100.birthday Theorems100.birthday

section MeasureTheory

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory ENNReal

variable {n m : ℕ}

/- In order for Lean to understand that we can take probabilities in `fin 23 → fin 365`, we must
tell Lean that there is a `measurable_space` structure on the space. Note that this instance
is only for `fin m` - Lean automatically figures out that the function space `fin n → fin m`
is _also_ measurable, by using `measurable_space.pi`, and furthermore that all sets are measurable,
from `measurable_singleton_class.pi`. -/
instance : MeasurableSpace (Fin m) :=
  ⊤

instance : MeasurableSingletonClass (Fin m) :=
  ⟨fun _ => trivial⟩

/- We then endow the space with a canonical measure, which is called ℙ.
We define this to be the conditional counting measure. -/
noncomputable instance : MeasureSpace (Fin n → Fin m) :=
  ⟨condCount Set.univ⟩

-- The canonical measure on `fin n → fin m` is a probability measure (except on an empty space).
instance : IsProbabilityMeasure (ℙ : Measure (Fin n → Fin (m + 1))) :=
  condCount_isProbabilityMeasure Set.finite_univ Set.univ_nonempty

theorem FinFin.measure_apply {s : Set <| Fin n → Fin m} :
    ℙ s = |s.toFinite.toFinset| / ‖Fin n → Fin m‖ := by
  erw [condCount_univ, Measure.count_apply_finite]
#align theorems_100.fin_fin.measure_apply Theorems100.FinFin.measure_apply

theorem _root_.ENNReal.mul_div (a b c : ℝ≥0∞) : a * (b / c) = (a * b) / c := sorry

/-- **Birthday Problem**: first probabilistic interpretation. -/
theorem birthday_measure :
    ℙ ({f | (Function.Injective f)} : Set ((Fin 23) → (Fin 365))) < 1 / 2 := by
  -- most of this proof is essentially converting it to the same form as `birthday`.
  rw [FinFin.measure_apply]
  generalize_proofs hfin
  rw [ENNReal.lt_div_iff_mul_lt, mul_comm, ENNReal.mul_div]
  swap; left; norm_num
  swap; left; exact ENNReal.two_ne_top
  apply ENNReal.div_lt_of_lt_mul
  have : ∀ a b : ℕ, 2 * a < b → 2 * (a : ℝ≥0∞) < b := fun _ _ h => by norm_cast
  rw [one_mul, Fintype.card_fun]
  apply this
  suffices : hfin.toFinset.card = 42200819302092359872395663074908957253749760700776448000000
  · rw [this]; norm_num
  trans ‖Fin 23 ↪ Fin 365‖
  · rw [← Fintype.card_coe]
    simp_rw [Set.Finite.coeSort_toFinset]
    simp_rw [Set.coe_setOf] -- these two simp_rws are really slow
    exact Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _) -/
  · simp only [Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial]

#align theorems_100.birthday_measure Theorems100.birthday_measure

end MeasureTheory

end Theorems100
