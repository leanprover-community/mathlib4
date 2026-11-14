/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Path measures of Markov chains

This file defines the distribution of a Markov chain with a given transition kernel `P` and
starting distribution `μ`. In other words, if `X ∼ P.markovChainMeasure μ`, then
```
X 0 ∼ μ
X (n + 1) | X 0, …, X n ∼ P (X n)
```

## Main definitions

* `ProbabilityTheory.Kernel.markovChainMeasure`: the distribution of the trajectories `ℕ → E` of a
Markov chain with state space `E`, transition kernel `P` and starting distribution `μ`.

## Main results

* `ProbabilityTheory.Kernel.markovChainMeasure_map_eval`: the coordinate of a Markov chain
  at time `n` has law `(P ^ n) ∘ₘ μ`.
-/

@[expose] public section

open MeasureTheory Preorder

namespace ProbabilityTheory.Kernel

variable {E : Type*} [MeasurableSpace E]

/-- `markovTransitionFamily P n` is the transition kernel from the history of the
first `n+1`-steps `x : Finset.Iic n → E` of a Markov chain with transition kernel `P`,
to the next step. It is defined by `markovTransitionFamily P n x = P (x n)`. -/
def markovTransitionFamily (P : Kernel E E) (n : ℕ) : Kernel (Finset.Iic n → E) E where
  toFun x := P (x ⟨n, by grind⟩)
  measurable' := by fun_prop

@[simp]
lemma markovTransitionFamily_apply (P : Kernel E E) (n : ℕ) (x : Finset.Iic n → E) :
    P.markovTransitionFamily n x = P (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := rfl

instance (P : Kernel E E) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (P.markovTransitionFamily n) where
  isProbabilityMeasure x :=
    inferInstanceAs (IsProbabilityMeasure (P (x ⟨n, by grind⟩)))

/-- `P.markovChainMeasure μ` is the distribution of the trajectories `ℕ → E` of a Markov chain
with state space `E`, transition kernel `P` and starting distribution `μ`. -/
noncomputable def markovChainMeasure (μ : Measure E) (P : Kernel E E) [IsMarkovKernel P] :
    Measure (ℕ → E) := trajMeasure μ (P.markovTransitionFamily)

lemma markovChainMeasure_def (μ : Measure E) (P : Kernel E E) [IsMarkovKernel P] :
    markovChainMeasure μ P = trajMeasure μ (P.markovTransitionFamily) := rfl

instance (μ : Measure E) [SFinite μ] (P : Kernel E E) [IsMarkovKernel P] :
    SFinite (P.markovChainMeasure μ) :=
  inferInstanceAs (SFinite (trajMeasure (X := fun _ ↦ E) μ P.markovTransitionFamily))

instance (μ : Measure E) [IsProbabilityMeasure μ] (P : Kernel E E) [IsMarkovKernel P] :
    IsProbabilityMeasure (P.markovChainMeasure μ) :=
  inferInstanceAs (IsProbabilityMeasure (trajMeasure (X := fun _ ↦ E) μ P.markovTransitionFamily))

variable (μ : Measure E) (P : Kernel E E) [IsMarkovKernel P]

lemma markovChainMeasure_map_eval_zero : (P.markovChainMeasure μ).map (fun x ↦ x 0) = μ := by
  rw [markovChainMeasure_def, map_eval_zero_trajMeasure]

variable [SFinite μ]

lemma markovChainMeasure_map_frestrictLe_compProd (n : ℕ) :
    (markovChainMeasure μ P).map (frestrictLe n) ⊗ₘ P.markovTransitionFamily n =
      (markovChainMeasure μ P).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
  simp [markovChainMeasure_def, map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure]

lemma markovChainMeasure_map_eval_succ (n : ℕ) :
    (markovChainMeasure μ P).map (fun x ↦ x (n + 1)) =
      P ∘ₘ (markovChainMeasure μ P).map (fun x ↦ x n) := by
  rw [Measure.bind_map (measurable_pi_apply n).aemeasurable P.aemeasurable]
  simpa (disch := fun_prop) [Measure.snd_map_prodMk, Measure.bind_map] using
    congrArg Measure.snd (markovChainMeasure_map_frestrictLe_compProd μ P n).symm

lemma markovChainMeasure_map_eval (n : ℕ) :
    (markovChainMeasure μ P).map (fun x ↦ x n) = (P ^ n) ∘ₘ μ := by
  induction n with
  | zero => exact (markovChainMeasure_map_eval_zero μ P).trans Measure.id_comp.symm
  | succ n ih =>
    rw [markovChainMeasure_map_eval_succ, ih, pow_succ']
    exact Measure.comp_assoc

end ProbabilityTheory.Kernel
