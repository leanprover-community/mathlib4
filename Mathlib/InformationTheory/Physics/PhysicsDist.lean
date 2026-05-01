/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.InformationTheory.EntropyNumber.Basic
public import Mathlib.InformationTheory.Entropy.Shannon
public import Mathlib.InformationTheory.Entropy.Axioms
public import Mathlib.InformationTheory.Physics.Common
public import Mathlib.InformationTheory.Entropy.Uniqueness
public import Mathlib.InformationTheory.Physics.UniformSystems
public import Mathlib.InformationTheory.Physics.StatisticalDistributions
public import Mathlib.InformationTheory.Entropy.SourceCoding



/-!
# Formalizing "Physics Distribution" To Mean A Combinatorial
State Spaces, Or, Counting Problem Under Constraints

## Three Disjoint Constraint Cases Describe All Physical Systems

Let `N` boxes (states) and `M` balls (particles). A microstate is
a way of allocating the `M` balls among the `N` boxes. There are
exactly three canonical constraint families for how balls may
occupy boxes in statistical mechanics:

* **Maxwell-Boltzmann (MB)**: Balls are **distinguishable**,
  boxes are **distinguishable**. Any number of balls may occupy
  a box.
* **Fermi-Dirac (FD)**: Balls are **indistinguishable**, boxes
  are **distinguishable**, **with at most one ball per box**.
* **Bose-Einstein (BE)**: Balls are **indistinguishable**, boxes
  are **distinguishable**, **with any number of balls per box**.

This file consumes the proofs from each of the three statistics
files and defines a `PhysicsDist` as a weighted linear combination
of the three canonical distributions.

## Main definitions

* `StatSystemType` -- enum for BE, FD, and MB system types.
* `SystemParams` -- parameters `N` (states) and `M` (particles) for a system.
* `entropy_of_stat_system` -- computes axiomatic entropy for a given system type and parameters.
* `shannon_entropy_of_stat_system` -- computes Shannon entropy for a given system type.
* `SystemWeights` -- weights for linearly combining the three canonical distributions.
* `H_physics_dist_linear_combination` -- weighted linear combination of the three entropies.
* `PhysicsSystemConfig` -- a bundled configuration for a physics system.

## Main results

* `entropy_BE_eq_C_shannon` -- BE component entropy equals `C * Shannon`.
* `entropy_FD_eq_C_shannon` -- FD component entropy equals `C * Shannon`.
* `entropy_MB_eq_C_shannon` -- MB component entropy equals `C * Shannon`.
* `H_physics_dist_linear_combination_eq_generalized_C_Shannon`
  -- the linearly combined entropy equals `C * weighted Shannon`.

## Tags

physics distribution, statistical mechanics, entropy
-/

@[expose] public section

namespace InformationTheory.Physics.PhysicsDist

open InformationTheory
open InformationTheory.Physics.Common
open InformationTheory.Physics.UniformSystems
open InformationTheory.Physics.StatisticalDistributions

/-- The physical constant `C` coerced to `ℝ`. -/
noncomputable def C_axiom_val : ℝ :=
  (C_physical_NNReal : ℝ)

/-- Enum for the three canonical statistical-mechanics system types. -/
inductive StatSystemType
  | BoseEinstein | FermiDirac | MaxwellBoltzmann

/-- Parameters (number of states `N` and particles `M`) for a statistical system. -/
structure SystemParams where
  /-- The number of available single-particle states. -/
  N : ℕ
  /-- The number of particles in the system. -/
  M : ℕ

/--
Calculates the entropy of a given statistical system (BE, FD, MB)
using the axiomatic H_physical_system.
-/
@[nolint unusedArguments]
noncomputable def entropy_of_stat_system
    (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    (InformationTheory.Physics.Common.H_physical_system
      (p_UD_fin params.N params.M) : ℝ)
  | StatSystemType.FermiDirac =>
    (InformationTheory.Physics.Common.H_physical_system
      (InformationTheory.Physics.StatisticalDistributions.p_FD_fin
        params.N params.M) : ℝ)
  | StatSystemType.MaxwellBoltzmann =>
    (InformationTheory.Physics.Common.H_physical_system
      (InformationTheory.Physics.StatisticalDistributions.p_MB_fin
        params.N params.M) : ℝ)

/--
Calculates the standard Shannon entropy (ln-based) of a given
statistical system's canonical (uniform) probability distribution.
-/
@[nolint unusedArguments]
noncomputable def shannon_entropy_of_stat_system
    (type : StatSystemType) (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    ℝ :=
  match type with
  | StatSystemType.BoseEinstein =>
    shannonEntropy
      (p_UD_fin params.N params.M)
  | StatSystemType.FermiDirac =>
    shannonEntropy
      (InformationTheory.Physics.StatisticalDistributions.p_FD_fin
        params.N params.M)
  | StatSystemType.MaxwellBoltzmann =>
    shannonEntropy
      (InformationTheory.Physics.StatisticalDistributions.p_MB_fin
        params.N params.M)

/--
Theorem: The axiomatic entropy of a Bose-Einstein system is
C_axiom * its Shannon entropy.
-/
theorem entropy_BE_eq_C_shannon
    (params : SystemParams)
    (h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    entropy_of_stat_system
      StatSystemType.BoseEinstein params
      h_domain_valid =
    C_axiom_val *
      shannon_entropy_of_stat_system
        StatSystemType.BoseEinstein params
        h_domain_valid := by
  simp only [entropy_of_stat_system,
    shannon_entropy_of_stat_system]
  exact H_BE_from_Multiset_eq_C_shannon params.N
    params.M h_domain_valid

/--
Theorem: The axiomatic entropy of a Fermi-Dirac system is
C_axiom * its Shannon entropy.
Note: FD requires `M ≤ N`.
-/
theorem entropy_FD_eq_C_shannon
    (params : SystemParams)
    (_h_domain_valid : params.N ≠ 0 ∨ params.M = 0)
    (h_fd : params.M ≤ params.N) :
    entropy_of_stat_system
      StatSystemType.FermiDirac params
      _h_domain_valid =
    C_axiom_val *
      shannon_entropy_of_stat_system
        StatSystemType.FermiDirac params
        _h_domain_valid := by
  simp only [entropy_of_stat_system,
    shannon_entropy_of_stat_system]
  exact H_FD_eq_C_shannon params.N params.M h_fd

/--
Theorem: The axiomatic entropy of a Maxwell-Boltzmann system is
C_axiom * its Shannon entropy.
-/
theorem entropy_MB_eq_C_shannon
    (params : SystemParams)
    (h_domain_valid : params.N ≠ 0 ∨ params.M = 0) :
    entropy_of_stat_system
      StatSystemType.MaxwellBoltzmann params
      h_domain_valid =
    C_axiom_val *
      shannon_entropy_of_stat_system
        StatSystemType.MaxwellBoltzmann params
        h_domain_valid := by
  simp only [entropy_of_stat_system,
    shannon_entropy_of_stat_system]
  exact H_MB_eq_C_shannon params.N params.M
    h_domain_valid

/-- Weights for the three statistical-mechanics components (BE, FD, MB). -/
structure SystemWeights where
  /-- The Bose-Einstein component weight. -/
  w_BE : NNReal
  /-- The Fermi-Dirac component weight. -/
  w_FD : NNReal
  /-- The Maxwell-Boltzmann component weight. -/
  w_MB : NNReal

/--
Defines the total entropy of a "Physics Distribution" as a
weighted sum of the axiomatic entropies of its constituent
statistical components (BE, FD, MB).
-/
noncomputable def H_physics_dist_linear_combination
    (weights : SystemWeights)
    (params_BE : SystemParams)
    (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams)
    (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0)
    (params_MB : SystemParams)
    (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0)
    : ℝ :=
  (weights.w_BE : ℝ) *
    entropy_of_stat_system
      StatSystemType.BoseEinstein params_BE
      h_valid_BE +
  (weights.w_FD : ℝ) *
    entropy_of_stat_system
      StatSystemType.FermiDirac params_FD
      h_valid_FD +
  (weights.w_MB : ℝ) *
    entropy_of_stat_system
      StatSystemType.MaxwellBoltzmann params_MB
      h_valid_MB

/--
The "Generalized PhysicsDistCShannon definition".
This is C_axiom multiplied by the weighted sum of the Shannon
entropies of the constituent statistical components.
-/
noncomputable def
    generalized_PhysicsDist_C_times_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams)
    (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams)
    (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0)
    (params_MB : SystemParams)
    (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0)
    : ℝ :=
  C_axiom_val * (
    (weights.w_BE : ℝ) *
      shannon_entropy_of_stat_system
        StatSystemType.BoseEinstein params_BE
        h_valid_BE +
    (weights.w_FD : ℝ) *
      shannon_entropy_of_stat_system
        StatSystemType.FermiDirac params_FD
        h_valid_FD +
    (weights.w_MB : ℝ) *
      shannon_entropy_of_stat_system
        StatSystemType.MaxwellBoltzmann params_MB
        h_valid_MB
  )

/--
Main Theorem for PhysicsDist:
The linearly combined axiomatic entropy is equal to the
generalized C * Shannon form.
-/
theorem
    H_physics_dist_linear_combination_eq_generalized_C_Shannon
    (weights : SystemWeights)
    (params_BE : SystemParams)
    (h_valid_BE : params_BE.N ≠ 0 ∨ params_BE.M = 0)
    (params_FD : SystemParams)
    (h_valid_FD : params_FD.N ≠ 0 ∨ params_FD.M = 0)
    (h_fd : params_FD.M ≤ params_FD.N)
    (params_MB : SystemParams)
    (h_valid_MB : params_MB.N ≠ 0 ∨ params_MB.M = 0)
    : H_physics_dist_linear_combination weights
        params_BE h_valid_BE params_FD h_valid_FD
        params_MB h_valid_MB =
      generalized_PhysicsDist_C_times_Shannon weights
        params_BE h_valid_BE params_FD h_valid_FD
        params_MB h_valid_MB := by
  simp only [H_physics_dist_linear_combination,
    generalized_PhysicsDist_C_times_Shannon]
  rw [entropy_BE_eq_C_shannon params_BE h_valid_BE]
  rw [entropy_FD_eq_C_shannon params_FD h_valid_FD
    h_fd]
  rw [entropy_MB_eq_C_shannon params_MB h_valid_MB]
  ring

/-- Complete configuration for a physics system: weights and parameters for each component. -/
structure PhysicsSystemConfig where
  /-- The mixing weights between the three statistical components. -/
  weights   : SystemWeights
  /-- Parameters for the Bose-Einstein component. -/
  params_BE : SystemParams
  /-- Parameters for the Fermi-Dirac component. -/
  params_FD : SystemParams
  /-- Parameters for the Maxwell-Boltzmann component. -/
  params_MB : SystemParams

/--
Calculates the weighted sum of Shannon entropies for a given
configuration. Handles domain validity internally for each
component. Returns 0 if a component's domain is invalid and its
weight is non-zero.
-/
noncomputable def
    generalized_shannon_entropy_for_config
    (config : PhysicsSystemConfig) : ℝ :=
  let h_valid_BE :=
    config.params_BE.N ≠ 0 ∨ config.params_BE.M = 0
  let entropy_BE := if h : h_valid_BE then
    shannon_entropy_of_stat_system
      StatSystemType.BoseEinstein config.params_BE h
    else 0
  let h_valid_FD :=
    config.params_FD.N ≠ 0 ∨ config.params_FD.M = 0
  let entropy_FD := if h : h_valid_FD then
    shannon_entropy_of_stat_system
      StatSystemType.FermiDirac config.params_FD h
    else 0
  let h_valid_MB :=
    config.params_MB.N ≠ 0 ∨ config.params_MB.M = 0
  let entropy_MB := if h : h_valid_MB then
    shannon_entropy_of_stat_system
      StatSystemType.MaxwellBoltzmann config.params_MB
      h
    else 0
  (config.weights.w_BE : ℝ) * entropy_BE +
  (config.weights.w_FD : ℝ) * entropy_FD +
  (config.weights.w_MB : ℝ) * entropy_MB

/-! ## Photonic Systems as Computable Programs -/

/-!
This section establishes the core principle for photonic systems,
which are governed by Bose-Einstein (BE) statistics. It proves
that any BE system has an equivalent `Program` whose complexity
is determined by the system's Shannon entropy.

### Main results

* `be_system_has_equivalent_program` -- for any BE system, there
  exists a `Program` whose complexity is
  `⌈logb 2 (Nat.multichoose N M)⌉`.
-/

/--
**Theorem (Bose-Einstein System Has Equivalent Program):**

For any Bose-Einstein system defined by `N` states and `M`
particles, there exists a `Program` that can specify one of its
microstates. The complexity of this program is the smallest
integer number of bits required to encode the system's total
information content, which is its Shannon entropy.

This theorem is the formal statement of
`BE Statistics <-> Computability`.
-/
theorem be_system_has_equivalent_program (N M : ℕ)
    (h_valid : N ≠ 0 ∨ M = 0) :
    ∃ (prog : Program),
      prog.complexity =
        Nat.ceil
          (Real.logb 2 (Nat.multichoose N M)) := by
  let k_card := Fintype.card (OmegaUD N M)
  have hk_card_pos : 0 < k_card :=
    StatisticalDistributions.card_omega_BE_pos' N M h_valid
  let p_be := p_UD_fin N M
  have h_sum_one : (∑ i, p_be i) = 1 :=
    StatisticalDistributions.p_BE_fin_sums_to_one N M h_valid
  have h_entropy_eq :
      shannonEntropyOfDist p_be =
        Real.logb 2 (Nat.multichoose N M) := by
    have h_entropy_is_logb_k :
        shannonEntropyOfDist p_be =
          Real.logb 2 k_card := by
      simp only [shannonEntropyOfDist]
      have h_p_be_is_uniform :
          p_be = canonicalUniformDist k_card
            hk_card_pos := by
        funext i
        simp [p_be, p_UD_fin, canonicalUniformDist,
          uniformProb, uniformDist,
          Fintype.card_fin, if_pos hk_card_pos]
        aesop
      rw [h_p_be_is_uniform]
      -- stdShannonEntropyLn is definitionally shannonEntropy
      change shannonEntropy
        (canonicalUniformDist k_card hk_card_pos) /
        Real.log 2 = _
      rw [shannonEntropy_canonicalUniform k_card
        hk_card_pos, Real.logb]
    rw [h_entropy_is_logb_k]
    rw [← card_omega_be N M]
  rcases exists_program_of_dist p_be h_sum_one
    with ⟨prog, h_complexity⟩
  use prog
  rw [h_complexity, h_entropy_eq]

/-!
### Conclusion

The theorem `be_system_has_equivalent_program` provides a direct,
sorry-free, and constructive link from the statistical physics of
a photonic system to the computational model. It demonstrates
that the information required to specify a physical state is
definitionally equivalent to the complexity of a computer program
that encodes it.
-/

end InformationTheory.Physics.PhysicsDist
