/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# UCB

`α` is the arm space.

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} {ν : Kernel α ℝ} {k : ℕ → α} {t : ℕ} {a : α}

section MeasureSpace

structure Bandit (α : Type*) [MeasurableSpace α] where
  /-- Conditional distribution of the rewards given the arm pulled. -/
  ν : Kernel α ℝ
  hν : IsMarkovKernel ν
  /-- Policy or sampling rule: distribution of the next pull. -/
  policy : (n : ℕ) → Kernel (Iic n → α × ℝ) α
  h_policy n : IsMarkovKernel (policy n)
  /-- Distribution of the first pull. -/
  p0 : Measure α
  hp0 : IsProbabilityMeasure p0

instance (b : Bandit α) : IsMarkovKernel b.ν := b.hν

instance (b : Bandit α) (n : ℕ) : IsMarkovKernel (b.policy n) := b.h_policy n

instance (b : Bandit α) : IsProbabilityMeasure b.p0 := b.hp0

namespace Bandit

noncomputable
def stepKernel (b : Bandit α) (n : ℕ) : Kernel (Iic n → α × ℝ) (α × ℝ) :=
  (b.policy n) ⊗ₖ b.ν.prodMkLeft (Iic n → α × ℝ)

instance (b : Bandit α) (n : ℕ) : IsMarkovKernel (b.stepKernel n) := by
  rw [stepKernel]
  infer_instance

noncomputable def traj (b : Bandit α) (n : ℕ) : Kernel (Iic n → α × ℝ) (ℕ → α × ℝ) :=
  ProbabilityTheory.Kernel.traj (X := fun _ ↦ α × ℝ) b.stepKernel n

instance (b : Bandit α) (n : ℕ) : IsMarkovKernel (b.traj n) := by
  rw [traj]
  infer_instance

def MeasurableEquiv.piIicZero (α : Type*) [MeasurableSpace α] :
    (Iic 0 → α) ≃ᵐ α :=
  have : Unique (Iic 0) := by
    simp only [mem_Iic, nonpos_iff_eq_zero]
    exact Unique.subtypeEq 0
  MeasurableEquiv.funUnique _ _

noncomputable
def measure (b : Bandit α) : Measure (ℕ → α × ℝ) :=
  (b.traj 0) ∘ₘ ((b.p0 ⊗ₘ b.ν).map (MeasurableEquiv.piIicZero _).symm)

instance (b : Bandit α) : IsProbabilityMeasure b.measure := by
  rw [Bandit.measure]
  have : IsProbabilityMeasure ((b.p0 ⊗ₘ b.ν).map (MeasurableEquiv.piIicZero _).symm) :=
    isProbabilityMeasure_map <| by fun_prop
  infer_instance

end Bandit

/-- `A n` is the arm pulled at time `n`. This is a random variable on the measurable space
`ℕ → α × ℝ`. -/
def A (n : ℕ) (h : ℕ → α × ℝ) : α := (h n).1

/-- `X n` is the reward at time `n`. This is a random variable on the measurable space
`ℕ → α × ℝ`. -/
def X (n : ℕ) (h : ℕ → α × ℝ) : ℝ := (h n).2

/-- `H n` is the history up to time `n`. This is a random variable on the measurable space
`ℕ → α × ℝ`. -/
def H (n : ℕ) (h : ℕ → α × ℝ) : Iic n → α × ℝ := fun i ↦ h i

def ℱ (α : Type*) [MeasurableSpace α] :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → α × ℝ)) :=
  MeasureTheory.Filtration.piLE (X := fun _ ↦ α × ℝ)

lemma condDistrib_AX [StandardBorelSpace α] [Nonempty α] (b : Bandit α) (n : ℕ) :
    condDistrib (fun h ↦ (A n h, X n h)) (H n) b.measure = b.stepKernel n := by
  sorry

lemma condDistrib_X (b : Bandit α) (n : ℕ) :
    condDistrib (X n) (A n) b.measure = ν := by
  sorry

lemma condDistrib_A [StandardBorelSpace α] [Nonempty α] (b : Bandit α) (n : ℕ) :
    condDistrib (A n) (H n) b.measure = b.policy n := by
  sorry

end MeasureSpace

section Regret

/-! ### Definitions of regret, gaps, pull counts -/

noncomputable
def regret (ν : Kernel α ℝ) (k : ℕ → α) (t : ℕ) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (k s))[id]

noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

open Classical in
noncomputable def pullCount (k : ℕ → α) (a : α) (t : ℕ) : ℕ := #(filter (fun s ↦ k s = a) (range t))

lemma sum_pullCount_mul [Fintype α] (k : ℕ → α) (f : α → ℝ) (t : ℕ) :
    ∑ a, pullCount k a t * f a = ∑ s ∈ range t, f (k s) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) k f

lemma sum_pullCount [Fintype α] : ∑ a, pullCount k a t = t := by
  suffices ∑ a, pullCount k a t * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν k t = ∑ a, pullCount k a t * gap ν a := by
  simp_rw [sum_pullCount_mul, regret, gap, sum_sub_distrib]
  simp

end Regret

section ETC

/-! ### Explore-then-Commit algorithm -/



end ETC


section UCB

/-! ### UCB algorithm -/

variable [Fintype α] [Nonempty α] {c : ℝ} {μ : α → ℝ} {N : α → ℕ} {a : α}

noncomputable def bestArm (ν : Kernel α ℝ) : α :=
  (exists_max_image univ (fun a ↦ (ν a)[id]) (univ_nonempty_iff.mpr inferInstance)).choose

lemma le_bestArm (a : α) : (ν a)[id] ≤ (ν (bestArm ν))[id] :=
  (exists_max_image univ (fun a ↦ (ν a)[id])
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

lemma gap_eq_bestArm_sub : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := by
  rw [gap]
  congr
  refine le_antisymm ?_ (le_ciSup (f := fun a ↦ (ν a)[id]) (by simp) (bestArm ν))
  exact ciSup_le le_bestArm

noncomputable def ucbWidth (c : ℝ) (N : α → ℕ) (t : ℕ) (a : α) : ℝ := √(c * log t / N a)

noncomputable
def ucbArm (c : ℝ) (μ : α → ℝ) (N : α → ℕ) (t : ℕ) : α :=
  (exists_max_image univ (fun a ↦ μ a + ucbWidth c N t a)
    (univ_nonempty_iff.mpr inferInstance)).choose

lemma le_ucb (a : α) :
    μ a + ucbWidth c N t a ≤ μ (ucbArm c μ N t) + ucbWidth c N t (ucbArm c μ N t) :=
  (exists_max_image univ (fun a ↦ μ a + ucbWidth c N t a)
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

lemma gap_ucbArm_le_two_mul_ucbWidth
    (h_best : (ν (bestArm ν))[id] ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν))
    (ha : μ (ucbArm c μ N t) - ucbWidth c N t (ucbArm c μ N t) ≤ (ν (ucbArm c μ N t))[id]) :
    gap ν (ucbArm c μ N t) ≤ 2 * ucbWidth c N t (ucbArm c μ N t) := by
  rw [gap_eq_bestArm_sub, sub_le_iff_le_add']
  calc (ν (bestArm ν))[id]
  _ ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν) := h_best
  _ ≤ μ (ucbArm c μ N t) + ucbWidth c N t (ucbArm c μ N t) := le_ucb _
  _ ≤ (ν (ucbArm c μ N t))[id] + 2 * ucbWidth c N t (ucbArm c μ N t) := by
    rw [two_mul, ← add_assoc]
    gcongr
    rwa [sub_le_iff_le_add] at ha

lemma N_ucbArm_le
    (h_best : (ν (bestArm ν))[id] ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν))
    (ha : μ (ucbArm c μ N t) - ucbWidth c N t (ucbArm c μ N t) ≤ (ν (ucbArm c μ N t))[id]) :
    N (ucbArm c μ N t) ≤ 4 * c * log t / gap ν (ucbArm c μ N t) ^ 2 := by
  have h_gap := gap_ucbArm_le_two_mul_ucbWidth h_best ha
  rw [ucbWidth] at h_gap
  sorry

end UCB

end Bandits
