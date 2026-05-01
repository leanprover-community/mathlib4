/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.InformationTheory.EntropyNumber.Basic
public import Mathlib.InformationTheory.Entropy.Shannon
public import Mathlib.InformationTheory.Entropy.Axioms

@[expose] public section


/-!
# Physics: Common Definitions

This file defines the common types and helper definitions used by
the three canonical statistical-mechanics distributions
(Bose--Einstein, Fermi--Dirac, Maxwell--Boltzmann) and the
`H_physical_system` entropy function that evaluates to
`C * log k` on uniform distributions.

## Main definitions

* `MBMacrostate`, `UDMacrostate` -- occupancy vectors summing to M.
* `SymFin` -- multisets of size M over `Fin N`.
* `C_physical_NNReal` -- the physical constant C (set to 1).
* `H_physical_system_uniform_only_calc` -- entropy for uniform dists.
* `H_physical_system` -- dispatches uniform vs non-uniform.

## Main results

* `Multiset.count_finset_sum` -- `Multiset.count` distributes over a `Finset` sum of multisets.
* `card_fin_eq_self` -- `Fintype.card (Fin k) = k`.

## Tags

physics, statistical mechanics, entropy, uniform distribution
-/

namespace InformationTheory.Physics.Common

open InformationTheory

/-- Maxwell-Boltzmann macrostate: an occupancy vector over `Fin N` summing to `M`. -/
def MBMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }
/-- Uniform-distribution macrostate: an occupancy vector over `Fin N` summing to `M`. -/
def UDMacrostate (N M : ℕ) := { q : Fin N → ℕ // ∑ i, q i = M }
/-- Multisets of size `M` over `Fin N`, via `Sym`. -/
@[reducible] def SymFin (N M : ℕ) := Sym (Fin N) M

-- This axiom states that the true entropy of physical systems
-- behaves according to Rota's postulates.

/-- `Multiset.count` distributes over a `Finset` sum of
multisets. -/
@[simp] lemma Multiset.count_finset_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset β}
    (f : β → Multiset α) (a : α) :
    Multiset.count a (∑ i ∈ s, f i) =
      ∑ i ∈ s, Multiset.count a (f i) := by
  -- We proceed by induction on the structure of `s`.
  refine Finset.induction ?base ?step s
  · -- base case: `s = ∅`
    simp
  · -- inductive step: `s = insert b s'` with `b ∉ s'`
    intro b s' hb_not_mem ih
    simp [Finset.sum_insert (s := s') hb_not_mem,
      Multiset.count_add, ih]

/-- Convert `Real.log k` to `NNReal`, given `k ≥ 1` so the log is non-negative. -/
noncomputable def RealLogNatToNNReal (k : ℕ)
    (hk_ge1 : k ≥ 1) : NNReal :=
  ⟨Real.log (k : ℝ), by
    apply Real.log_nonneg
    rw [Nat.one_le_cast]
    exact hk_ge1
  ⟩

/-- The physical constant `C` as an `NNReal`, set to 1 for simplicity. -/
noncomputable def C_physical_NNReal : NNReal := 1.0

/--
Calculates `C_physical_NNReal * log k` for a uniform distribution
over `k` states.
Requires `k ≥ 1` (as `k=0` has no uniform dist and `log 0` is
undefined). Outputs NNReal.
-/
noncomputable def H_physical_system_uniform_only_calc
    (k : ℕ) (hk_ge1 : k ≥ 1) : NNReal :=
  if _hk_eq_1 : k = 1 then
    0 -- H(uniform_1) = C * log 1 = 0
  else
    C_physical_NNReal * RealLogNatToNNReal k hk_ge1

/--
Phase 1 concrete definition of H_physical_system.
For uniform distributions, it computes C * log k.
For non-uniform distributions, its behavior is currently 0 for
this phase. This is a placeholder until general distributions are
handled in Phase 2.
-/
noncomputable def H_physical_system {α : Type}
    [Fintype α] (p : α → NNReal) : NNReal :=
  let k := Fintype.card α
  if hk_is_0 : k = 0 then
    0 -- No states, entropy is 0
  else
    let k_pos_proof : 0 < k := Nat.pos_of_ne_zero hk_is_0
    if _h_is_uniform : p = uniformDist k_pos_proof then
        H_physical_system_uniform_only_calc k
          (Nat.one_le_of_lt k_pos_proof)
    else
        0 -- Placeholder for non-uniform distributions

/-- Evaluate `H_physical_system` on a `Fin k` distribution and coerce to `ℝ`. -/
noncomputable def eval_H_phys_system_on_fin_dist_to_real
    {k : ℕ} (p_dist : Fin k → NNReal) : ℝ :=
  (InformationTheory.Physics.Common.H_physical_system
    (α := Fin k) p_dist : ℝ)

/-- `Fintype.card (Fin k) = k`. -/
lemma card_fin_eq_self (k : ℕ) :
    Fintype.card (Fin k) = k := by
  simp only [Fintype.card_fin]

end InformationTheory.Physics.Common
