/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality

/-!
# The `ContinuumHypothesis` typeclass

We make this a typeclass rather than an axiom so that it is immediately obvious when a theorem
assumes this hypothesis.

In mathlib, we show consequences of the continuum hpyothesis with `[ContinuumHypothesis]` in
assumptions.
If in downstream projects you want to assume this as an axiom, you can write
```
@[instance] axiom continuumHypothesis : ContinuumHypothesis
```

## Main results

* `ContinuumHypothesis.iff_exists_sierpinski_pathological_partition`: Sierpiński's 1919 theorem.
-/

open scoped Cardinal

/-- The statement that the continuum hypothesis holds.

To avoid a universe parameter, we only state that this holds in universe `0`, since it can be lifted
to other universes with subsequent theorems.

See `ContinuumHypothesis.iff_aleph0_covby_continuum` and
`ContinuumHypothesis.iff_continuum_eq_aleph_one` for typical characterizations.
-/
class ContinuumHypothesis where
  /-- See `ContinuumHypothesis.of_continuum_eq_aleph_one'` for the universe-generic version. -/
  of_continuum_eq_aleph_one' ::
    /-- See `ContinuumHypothesis.continuum_eq_aleph_one` for the universe-generic version. -/
    continuum_eq_aleph_one' : (𝔠 : Cardinal.{0}) = ℵ₁

namespace ContinuumHypothesis

/-- See `ContinuumHypothesis.iff_continuum_eq_aleph_one` for the universe-generic version. -/
theorem iff_continuum_eq_aleph_one' : ContinuumHypothesis ↔ (𝔠 : Cardinal.{0}) = ℵ₁ :=
  ⟨(·.continuum_eq_aleph_one'), .of_continuum_eq_aleph_one'⟩

section basic_constructors

theorem iff_continuum_eq_aleph_one.{u} : ContinuumHypothesis ↔ (𝔠 : Cardinal.{u}) = ℵ₁ := by
  rw [iff_continuum_eq_aleph_one', ← Cardinal.lift_continuum.{u, 0}, Cardinal.lift_eq_aleph_one]

theorem continuum_eq_aleph_one.{u} [ContinuumHypothesis] : (𝔠 : Cardinal.{u}) = ℵ₁ :=
  iff_continuum_eq_aleph_one.1 ‹_›

alias ⟨_, of_continuum_eq_aleph_one⟩ := iff_continuum_eq_aleph_one

theorem iff_aleph0_covby_continuum : ContinuumHypothesis ↔ ℵ₀ ⋖ 𝔠 := by
  rw [← Order.succ_eq_iff_covBy, Cardinal.succ_aleph0, eq_comm, iff_continuum_eq_aleph_one]

theorem aleph0_covby_continuum.{u} [ContinuumHypothesis] : ℵ₀ ⋖ (𝔠 : Cardinal.{u}) :=
  iff_aleph0_covby_continuum.1 ‹_›

alias ⟨_, of_aleph0_covby_continuum⟩ := iff_aleph0_covby_continuum

end basic_constructors

open Set in
theorem exists_sierpinski_pathological_pred [ContinuumHypothesis] :
    ∃ f : ℝ → ℝ → Prop, (∀ x, {y | ¬ f x y}.Countable) ∧ ∀ y, {x : ℝ | f x y}.Countable := by
  have Hcont : #ℝ = ℵ₁ := by rw [← continuum_eq_aleph_one, Cardinal.mk_real]
  rcases Cardinal.ord_eq ℝ with ⟨r, hr, H⟩
  refine ⟨r, fun x => ?_, fun y => ?_⟩
  · have : {y | ¬r x y} = {y | r y x} ∪ {x} := by
      ext y
      simp only [mem_setOf_eq, mem_insert_iff, union_singleton]
      rcases trichotomous_of r x y with (h | rfl | h)
      · simp only [h, not_or, false_iff, not_true]
        constructor
        · rintro rfl; exact irrefl_of r y h
        · exact asymm h
      · simp only [true_or, iff_true]; exact irrefl x
      · simp only [h, iff_true, or_true]; exact asymm h
    rw [this]
    apply Countable.union _ (countable_singleton _)
    rw [Cardinal.countable_iff_lt_aleph_one, ← Hcont]
    exact Cardinal.card_typein_lt r x H
  · rw [Cardinal.countable_iff_lt_aleph_one, ← Hcont]
    exact Cardinal.card_typein_lt r y H

/--
Alternate statement of `iff_exists_sierpinski_pathological_partition` using a predicate to assign
points to sets.
-/
theorem iff_exists_sierpinski_pathological_pred :
    ContinuumHypothesis ↔
      ∃ f : ℝ → ℝ → Prop, (∀ x, {y | ¬ f x y}.Countable) ∧ ∀ y, {x : ℝ | f x y}.Countable := by
  refine ⟨(·.exists_sierpinski_pathological_pred), fun ⟨f, hnf, hf⟩ => ?_⟩
  suffices #ℝ ≤ ℵ₁ by
    rw [iff_continuum_eq_aleph_one]
    apply le_antisymm (Cardinal.mk_real.symm.trans_le this)
    exact Cardinal.aleph_one_le_continuum
  by_contra! h_c_gt
  obtain ⟨S, hS_card : #S = ℵ₁⟩ := Cardinal.le_mk_iff_exists_set.mp h_c_gt.le
  haveI : Nonempty S := by
    rw [Set.nonempty_coe_sort, ← Cardinal.mk_set_ne_zero_iff, hS_card]
    exact (Cardinal.aleph_pos _).ne'
  let C := ⋃ x ∈ S, {y | ¬ f x y}
  have hC_le : #C ≤ ℵ₁ := by
    calc #C ≤ #S * ℵ₀ := by
            grw [Cardinal.mk_biUnion_le _ _]
            gcongr
            refine ciSup_le fun x => ?_
            grw [Cardinal.le_aleph0_iff_set_countable.2 (hnf _)]
         _ = ℵ₁ * ℵ₀ := by rw [hS_card]
         _ = ℵ₁      := Cardinal.aleph_mul_aleph0 1
  obtain ⟨y', hy_notin : y' ∉ C⟩ := Cardinal.compl_nonempty_of_mk_lt_mk (hC_le.trans_lt h_c_gt)
  have h_sub : S ⊆ {x | f x y'} := by simpa [C] using hy_notin
  have h_S_count : S.Countable := (hf y').mono h_sub
  rw [← Cardinal.le_aleph0_iff_set_countable, hS_card] at h_S_count
  exact h_S_count.not_gt Cardinal.aleph0_lt_aleph_one

/-- Forward direction of `iff_exists_sierpinski_pathological_partition`. -/
theorem exists_sierpinski_pathological_partition [ContinuumHypothesis] :
    ∃ S T : Set (ℝ × ℝ), IsCompl S T ∧
      (∀ x, {y | (x, y) ∈ S}.Countable) ∧ ∀ y, {x : ℝ | (x, y) ∈ T}.Countable := by
  let ⟨f, hS, hT⟩ := exists_sierpinski_pathological_pred
  refine ⟨{p | ¬f p.1 p.2}, {p | f p.1 p.2}, isCompl_compl.symm, hS, hT⟩

/--
The continuum hypothesis is equivalent to the statement that
the plane $\mathbb{R}^2$ can be partitioned into two sets,
$A$ and $B$, such that every horizontal line intersects $A$ in a countable number of points,
and every vertical line intersects $B$ in a countable number of points.

This is Sierpiński (1919).
-/
theorem iff_exists_sierpinski_pathological_partition :
    ContinuumHypothesis ↔
      ∃ S T : Set (ℝ × ℝ), IsCompl S T ∧
        (∀ x, {y | (x, y) ∈ S}.Countable) ∧ ∀ y, {x : ℝ | (x, y) ∈ T}.Countable := by
  refine ⟨(·.exists_sierpinski_pathological_partition), ?_⟩
  rw [iff_exists_sierpinski_pathological_pred]
  rintro ⟨S, T, hST, hS, hT⟩
  obtain rfl := hST.eq_compl
  refine ⟨fun x y => (x, y) ∈ T, hS, hT⟩

end ContinuumHypothesis
