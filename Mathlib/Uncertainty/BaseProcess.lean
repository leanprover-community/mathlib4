/-
Copyright (c) 2026 Prof. Dr. Fei Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prof. Dr. Fei Gao <gaof@whut.edu.cn>
-/

module

public import Mathlib.Uncertainty.BaseDistribution

/-! # Uncertainty Process -/

@[expose] public section

open Filter
open scoped Topology
open scoped BigOperators

noncomputable section

namespace Uncertainty

/-- Time-indexed uncertain process with pointwise measurability. -/
structure UncertainProcess (U : UncertainSpace) where
  /-- Sample paths: for each time, a real-valued uncertain variable on `U.Ω`. -/
  proc : ℝ → U.Ω → ℝ
  /-- Measurability at each fixed time. -/
  measurable : ∀ t x, {ω | proc t ω ≤ x} ∈ U.𝒜

/-- A simple model for an uncertain renewal process. -/
structure UncertainRenewalProcess (U : UncertainSpace) where
  /-- Interarrival uncertain variables. -/
  interarrival : ℕ → UncertainVariable U  -- ξ₁, ξ₂, …
  iid : ∀ n m, uncertainDistribution U (interarrival n)
          = uncertainDistribution U (interarrival m)
  positive : ∀ n ω, (interarrival n).f ω > 0
  /-- Nₜ = max{n ≥ 0 | Sₙ ≤ t} where Sₙ = ξ₁ + … + ξₙ -/
  N : ℝ → UncertainVariable U

/-- Chapter-13 renewal/update theorem package (statement level, replacing `True` skeletons). -/
class RenewalUpdateTheoryStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  /-- Distribution statement for the elementary renewal theorem. -/
  elementary_renewal_distribution_statement : UncertainRenewalProcess U → Prop
  /-- Expectation statement for the elementary renewal theorem. -/
  elementary_renewal_expectation_statement : UncertainRenewalProcess U → Prop
  /-- Distribution statement for the renewal-reward theorem. -/
  renewal_reward_distribution_statement : Prop
  /-- Expectation statement for the renewal-reward theorem. -/
  renewal_reward_expectation_statement : Prop
  elementary_renewal_distribution_axiom :
    ∀ renewal : UncertainRenewalProcess U,
      elementary_renewal_distribution_statement renewal
  elementary_renewal_expectation_axiom :
    ∀ renewal : UncertainRenewalProcess U,
      elementary_renewal_expectation_statement renewal
  renewal_reward_distribution_axiom : renewal_reward_distribution_statement
  renewal_reward_expectation_axiom : renewal_reward_expectation_statement

/-- Stronger assumption package to auto-derive `RenewalUpdateTheoryStructure`. -/
class RenewalUpdateStrongAssumption (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  /-- Distribution statement for the elementary renewal theorem. -/
  elementary_renewal_distribution_statement : UncertainRenewalProcess U → Prop
  /-- Expectation statement for the elementary renewal theorem. -/
  elementary_renewal_expectation_statement : UncertainRenewalProcess U → Prop
  /-- Distribution statement for the renewal-reward theorem. -/
  renewal_reward_distribution_statement : Prop
  /-- Expectation statement for the renewal-reward theorem. -/
  renewal_reward_expectation_statement : Prop
  elementary_renewal_distribution_axiom :
    ∀ renewal : UncertainRenewalProcess U,
      elementary_renewal_distribution_statement renewal
  elementary_renewal_expectation_axiom :
    ∀ renewal : UncertainRenewalProcess U,
      elementary_renewal_expectation_statement renewal
  renewal_reward_distribution_axiom : renewal_reward_distribution_statement
  renewal_reward_expectation_axiom : renewal_reward_expectation_statement

/-- One-line constructor template for `RenewalUpdateStrongAssumption`. -/
def mkRenewalUpdateStrongAssumption (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    (distribution_stmt : UncertainRenewalProcess U → Prop)
    (expectation_stmt : UncertainRenewalProcess U → Prop)
    (reward_distribution_stmt reward_expectation_stmt : Prop)
    (distribution_axiom_rule : ∀ renewal : UncertainRenewalProcess U,
      distribution_stmt renewal)
    (expectation_axiom_rule : ∀ renewal : UncertainRenewalProcess U,
      expectation_stmt renewal)
    (reward_distribution_axiom_rule : reward_distribution_stmt)
    (reward_expectation_axiom_rule : reward_expectation_stmt) :
    RenewalUpdateStrongAssumption U where
  elementary_renewal_distribution_statement := distribution_stmt
  elementary_renewal_expectation_statement := expectation_stmt
  renewal_reward_distribution_statement := reward_distribution_stmt
  renewal_reward_expectation_statement := reward_expectation_stmt
  elementary_renewal_distribution_axiom := distribution_axiom_rule
  elementary_renewal_expectation_axiom := expectation_axiom_rule
  renewal_reward_distribution_axiom := reward_distribution_axiom_rule
  renewal_reward_expectation_axiom := reward_expectation_axiom_rule

/-- Build `RenewalUpdateStrongAssumption` from `RenewalUpdateTheoryStructure`. -/
def renewalUpdateStrong_of_structure
    (U : UncertainSpace) [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateTheoryStructure U] :
    RenewalUpdateStrongAssumption U where
  elementary_renewal_distribution_statement :=
    RenewalUpdateTheoryStructure.elementary_renewal_distribution_statement (U := U)
  elementary_renewal_expectation_statement :=
    RenewalUpdateTheoryStructure.elementary_renewal_expectation_statement (U := U)
  renewal_reward_distribution_statement :=
    RenewalUpdateTheoryStructure.renewal_reward_distribution_statement (U := U)
  renewal_reward_expectation_statement :=
    RenewalUpdateTheoryStructure.renewal_reward_expectation_statement (U := U)
  elementary_renewal_distribution_axiom :=
    RenewalUpdateTheoryStructure.elementary_renewal_distribution_axiom (U := U)
  elementary_renewal_expectation_axiom :=
    RenewalUpdateTheoryStructure.elementary_renewal_expectation_axiom (U := U)
  renewal_reward_distribution_axiom :=
    RenewalUpdateTheoryStructure.renewal_reward_distribution_axiom (U := U)
  renewal_reward_expectation_axiom :=
    RenewalUpdateTheoryStructure.renewal_reward_expectation_axiom (U := U)

instance (priority := 100) renewalUpdate_of_strongAssumption
    (U : UncertainSpace) [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateStrongAssumption U] :
    RenewalUpdateTheoryStructure U where
  elementary_renewal_distribution_statement :=
    RenewalUpdateStrongAssumption.elementary_renewal_distribution_statement (U := U)
  elementary_renewal_expectation_statement :=
    RenewalUpdateStrongAssumption.elementary_renewal_expectation_statement (U := U)
  renewal_reward_distribution_statement :=
    RenewalUpdateStrongAssumption.renewal_reward_distribution_statement (U := U)
  renewal_reward_expectation_statement :=
    RenewalUpdateStrongAssumption.renewal_reward_expectation_statement (U := U)
  elementary_renewal_distribution_axiom :=
    RenewalUpdateStrongAssumption.elementary_renewal_distribution_axiom (U := U)
  elementary_renewal_expectation_axiom :=
    RenewalUpdateStrongAssumption.elementary_renewal_expectation_axiom (U := U)
  renewal_reward_distribution_axiom :=
    RenewalUpdateStrongAssumption.renewal_reward_distribution_axiom (U := U)
  renewal_reward_expectation_axiom :=
    RenewalUpdateStrongAssumption.renewal_reward_expectation_axiom (U := U)

/-- Distribution-level elementary renewal theorem (Chapter 13 interface). -/
theorem elementary_renewal_theorem_distribution (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateTheoryStructure U] (renewal : UncertainRenewalProcess U) :
    RenewalUpdateTheoryStructure.elementary_renewal_distribution_statement
      (U := U) renewal :=
  RenewalUpdateTheoryStructure.elementary_renewal_distribution_axiom renewal

/-- Expectation-level elementary renewal theorem (Chapter 13 interface). -/
theorem elementary_renewal_theorem_expectation (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateTheoryStructure U] (renewal : UncertainRenewalProcess U) :
    RenewalUpdateTheoryStructure.elementary_renewal_expectation_statement
      (U := U) renewal :=
  RenewalUpdateTheoryStructure.elementary_renewal_expectation_axiom renewal

/-- Renewal reward theorem in distribution form (Chapter 13 interface). -/
theorem renewal_reward_theorem_distribution (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateTheoryStructure U] :
    RenewalUpdateTheoryStructure.renewal_reward_distribution_statement (U := U) :=
  RenewalUpdateTheoryStructure.renewal_reward_distribution_axiom (U := U)

/-- Renewal reward theorem in expectation form (Chapter 13 interface). -/
theorem renewal_reward_theorem_expectation (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [RenewalUpdateTheoryStructure U] :
    RenewalUpdateTheoryStructure.renewal_reward_expectation_statement (U := U) :=
  RenewalUpdateTheoryStructure.renewal_reward_expectation_axiom (U := U)

/-- Uncertain variable induced by a process at fixed time. -/
noncomputable def processAt (U : UncertainSpace) (P : UncertainProcess U) (t : ℝ) :
    UncertainVariable U where
  f := P.proc t
  measurable := P.measurable t

@[simp] theorem processAt_f (U : UncertainSpace) (P : UncertainProcess U) (t : ℝ) (ω : U.Ω) :
    (processAt U P t).f ω = P.proc t ω := rfl

/-- Increment uncertain variable `P_t - P_s`. -/
noncomputable def increment_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (P : UncertainProcess U) (s t : ℝ) : UncertainVariable U :=
  sub_uncertain U (processAt U P t) (processAt U P s)

@[simp] theorem increment_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (P : UncertainProcess U) (s t : ℝ) (ω : U.Ω) :
    (increment_uncertain U P s t).f ω = P.proc t ω - P.proc s ω := by
  simp [increment_uncertain, processAt]

/-- Distribution law of a process increment. -/
noncomputable def IncrementLaw (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (P : UncertainProcess U) (s t : ℝ) : ℝ → ℝ :=
  uncertainDistribution U (increment_uncertain U P s t)

@[simp] theorem incrementLaw_apply (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (P : UncertainProcess U) (s t x : ℝ) :
    IncrementLaw U P s t x = uncertainDistribution U (increment_uncertain U P s t) x := rfl

/-- Minimal uncertain differential equation interface: drift, diffusion, initial value. -/
structure UncertainDE where
  /-- Drift coefficient. -/
  drift : ℝ → ℝ → ℝ
  /-- Diffusion coefficient. -/
  diffusion : ℝ → ℝ → ℝ
  /-- Initial value at time zero. -/
  x0 : ℝ

/-- One-step Euler update as an uncertain variable. -/
noncomputable def eulerStep (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (de : UncertainDE) (P : UncertainProcess U) (t dt x : ℝ) : UncertainVariable U :=
  let driftTerm := const_uncertain U (de.drift t x * dt)
  let noiseTerm := smul_uncertain U (de.diffusion t x) (increment_uncertain U P t (t + dt))
  add_uncertain U (add_uncertain U (const_uncertain U x) driftTerm) noiseTerm

@[simp] theorem eulerStep_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (de : UncertainDE) (P : UncertainProcess U) (t dt x : ℝ) (ω : U.Ω) :
    (eulerStep U de P t dt x).f ω
      = x + de.drift t x * dt
          + de.diffusion t x * (P.proc (t + dt) ω - P.proc t ω) := by
  simp [eulerStep, add_assoc]

/-- Euler trace on sample paths: `n`-th approximation value at `ω`. -/
def eulerTracePath (U : UncertainSpace) (de : UncertainDE)
    (P : UncertainProcess U) (dt : ℝ) : ℕ → U.Ω → ℝ
  | 0 => fun _ => de.x0
  | n + 1 => fun ω =>
      let t : ℝ := (n : ℝ) * dt
      let xn := eulerTracePath U de P dt n ω
      xn + de.drift t xn * dt
        + de.diffusion t xn * (P.proc (t + dt) ω - P.proc t ω)

/-- Short alias for Euler path trace. -/
abbrev eulerTrace (U : UncertainSpace) (de : UncertainDE)
    (P : UncertainProcess U) (dt : ℝ) : ℕ → U.Ω → ℝ :=
  eulerTracePath U de P dt

@[simp] theorem eulerTrace_zero (U : UncertainSpace) (de : UncertainDE)
    (P : UncertainProcess U) (dt : ℝ) (ω : U.Ω) :
    eulerTrace U de P dt 0 ω = de.x0 := rfl

@[simp] theorem eulerTrace_succ (U : UncertainSpace) (de : UncertainDE)
    (P : UncertainProcess U) (dt : ℝ) (n : ℕ) (ω : U.Ω) :
    eulerTrace U de P dt (n + 1) ω
      =
        let t : ℝ := (n : ℝ) * dt
        let xn := eulerTrace U de P dt n ω
        xn + de.drift t xn * dt
          + de.diffusion t xn * (P.proc (t + dt) ω - P.proc t ω) := rfl

/-- Wrap Euler path trace into uncertain variables under a measurability assumption. -/
noncomputable def eulerTraceVar (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    (hMeas : ∀ n x, {ω | eulerTrace U de P dt n ω ≤ x} ∈ U.𝒜) :
    ℕ → UncertainVariable U :=
  fun n =>
    { f := fun ω => eulerTrace U de P dt n ω
      measurable := hMeas n }

@[simp] theorem eulerTraceVar_f (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    (hMeas : ∀ n x, {ω | eulerTrace U de P dt n ω ≤ x} ∈ U.𝒜)
    (n : ℕ) (ω : U.Ω) :
    (eulerTraceVar U de P dt hMeas n).f ω = eulerTrace U de P dt n ω := rfl

@[simp] theorem eulerTraceVar_zero (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    (hMeas : ∀ n x, {ω | eulerTrace U de P dt n ω ≤ x} ∈ U.𝒜)
    (ω : U.Ω) :
    (eulerTraceVar U de P dt hMeas 0).f ω = de.x0 := by
  simp [eulerTraceVar]

@[simp] theorem eulerTraceVar_succ (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    (hMeas : ∀ n x, {ω | eulerTrace U de P dt n ω ≤ x} ∈ U.𝒜)
    (n : ℕ) (ω : U.Ω) :
    (eulerTraceVar U de P dt hMeas (n + 1)).f ω
      =
        let t : ℝ := (n : ℝ) * dt
        let xn := (eulerTraceVar U de P dt hMeas n).f ω
        xn + de.drift t xn * dt
          + de.diffusion t xn * (P.proc (t + dt) ω - P.proc t ω) := by
  simp [eulerTraceVar, eulerTrace_succ]

/-- Euler scheme interface: keeps trace variables and recursive update form, with
future hooks for consistency/convergence statements. -/
class EulerSchemeStructure (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ) where
  /-- Euler trace variables indexed by grid step. -/
  traceVar : ℕ → UncertainVariable U
  /-- Target process used for terminal-error comparison (may differ from the driver). -/
  targetProc : UncertainProcess U := P
  /-- Grid time `t_n = n * dt`. -/
  gridTime : ℕ → ℝ := fun n => (n : ℝ) * dt
  trace_zero : ∀ ω, (traceVar 0).f ω = de.x0
  trace_succ : ∀ n ω,
    (traceVar (n + 1)).f ω
      =
        let t : ℝ := gridTime n
        let xn := (traceVar n).f ω
        xn + de.drift t xn * dt
          + de.diffusion t xn * (P.proc (t + dt) ω - P.proc t ω)
  /-- Terminal-time pathwise error on grid index `n`. -/
  terminalPathError : ℝ → ℕ → U.Ω → ℝ :=
    fun T n ω => |(traceVar n).f ω - targetProc.proc T ω|
  /-- Terminal-time error event `{ |X̂_n(T)-X(T)| ≥ ε }`. -/
  terminalErrorEvent : ℝ → ℕ → Set U.Ω :=
    fun ε n => {ω | terminalPathError (gridTime n) n ω ≥ ε}
  /-- Terminal-time error measure on grid index `n`. -/
  terminalErrorMeasure : ℝ → ℕ → ℝ :=
    fun ε n => U.M (terminalErrorEvent ε n)
  /-- Grid-level consistency marker for the scheme. -/
  consistencyAtGrid : Prop := True
  /-- Convergence-in-measure marker for the scheme. -/
  convergenceInMeasure : Prop := True
  /-- Terminal consistency statement. -/
  terminalConsistency : Prop :=
    ∀ ε > 0, ∀ δ > 0, ∃ N0 : ℕ, ∀ n ≥ N0,
      terminalErrorMeasure ε n ≤ δ
  /-- Terminal convergence-in-measure statement. -/
  terminalConvergence : Prop :=
    ∀ ε > 0,
      Tendsto (fun n => terminalErrorMeasure ε n) atTop (𝓝 0)

/-- Canonical Euler scheme instance induced by `eulerTraceVar`. -/
noncomputable def mkEulerSchemeFromTrace (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    (hMeas : ∀ n x, {ω | eulerTrace U de P dt n ω ≤ x} ∈ U.𝒜) :
    EulerSchemeStructure U de P dt where
  traceVar := eulerTraceVar U de P dt hMeas
  targetProc := P
  trace_zero := by
    intro ω
    exact eulerTraceVar_zero U de P dt hMeas ω
  trace_succ := by
    intro n ω
    exact eulerTraceVar_succ U de P dt hMeas n ω

/-- Accessor for scheme trace variables. -/
noncomputable def eulerSchemeTraceVar (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] :
    ℕ → UncertainVariable U :=
  fun n => (EulerSchemeStructure.traceVar (U := U) (de := de) (P := P) (dt := dt)) n

/-- Canonical grid time for Euler scheme (outside class access). -/
noncomputable def eulerGridTime (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] :
    ℕ → ℝ :=
  EulerSchemeStructure.gridTime (U := U) (de := de) (P := P) (dt := dt)

/-- Terminal pathwise error for Euler scheme at index `n`. -/
noncomputable def eulerTerminalPathError (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] :
    ℝ → ℕ → U.Ω → ℝ :=
  EulerSchemeStructure.terminalPathError (U := U) (de := de) (P := P) (dt := dt)

/-- Terminal error event for Euler scheme at index `n`. -/
noncomputable def eulerTerminalErrorEvent (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] :
    ℝ → ℕ → Set U.Ω :=
  EulerSchemeStructure.terminalErrorEvent (U := U) (de := de) (P := P) (dt := dt)

/-- Terminal error measure for Euler scheme at index `n`. -/
noncomputable def eulerTerminalErrorMeasure (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] :
    ℝ → ℕ → ℝ :=
  EulerSchemeStructure.terminalErrorMeasure (U := U) (de := de) (P := P) (dt := dt)

/-- Signature-style terminal consistency statement carrier (no proof here). -/
def EulerTerminalConsistency (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] : Prop :=
  EulerSchemeStructure.terminalConsistency (U := U) (de := de) (P := P) (dt := dt)

/-- Signature-style terminal convergence-in-measure carrier (no proof here). -/
def EulerTerminalConvergenceInMeasure (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] : Prop :=
  EulerSchemeStructure.terminalConvergence (U := U) (de := de) (P := P) (dt := dt)

/-- Bridge assumptions: terminal convergence implies consistency properties. -/
class EulerTerminalBridgeStructure (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] where
  terminalConvergence_to_terminalConsistency :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerTerminalConsistency U de P dt
  terminalConvergence_to_gridConsistency :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerSchemeStructure.consistencyAtGrid (U := U) (de := de) (P := P) (dt := dt)

/-- Stronger assumption package used to auto-derive bridge implications. -/
class EulerTerminalStrongAssumption (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] where
  convergence_implies_terminalConsistency :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerTerminalConsistency U de P dt
  convergence_implies_gridConsistency :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerSchemeStructure.consistencyAtGrid (U := U) (de := de) (P := P) (dt := dt)

/-- Default bridge instance template: if the stronger assumptions are provided,
we get `EulerTerminalBridgeStructure` automatically. -/
instance (priority := 100)
    eulerTerminalBridge_of_strongAssumption
    (U : UncertainSpace) (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] [EulerTerminalStrongAssumption U de P dt] :
    EulerTerminalBridgeStructure U de P dt where
  terminalConvergence_to_terminalConsistency :=
    EulerTerminalStrongAssumption.convergence_implies_terminalConsistency
  terminalConvergence_to_gridConsistency :=
    EulerTerminalStrongAssumption.convergence_implies_gridConsistency

/-- Bridge theorem 1: terminal convergence implies terminal consistency. -/
theorem euler_terminalConsistency_of_terminalConvergence (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] [EulerTerminalBridgeStructure U de P dt] :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerTerminalConsistency U de P dt :=
  EulerTerminalBridgeStructure.terminalConvergence_to_terminalConsistency

/-- Bridge theorem 2: terminal convergence implies grid consistency. -/
theorem euler_gridConsistency_of_terminalConvergence (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] [EulerTerminalBridgeStructure U de P dt] :
    EulerTerminalConvergenceInMeasure U de P dt →
      EulerSchemeStructure.consistencyAtGrid (U := U) (de := de) (P := P) (dt := dt) :=
  EulerTerminalBridgeStructure.terminalConvergence_to_gridConsistency

/-- D-line start: Ito layer as interface-only assumptions. -/
class ItoStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] where
  /-- Ito formula statement for uncertain processes. -/
  ito_formula_statement : UncertainProcess U → Prop
  ito_formula_axiom : ∀ P : UncertainProcess U, ito_formula_statement P

/-- Interface theorem shell for Ito formula (no heavy proof in main branch). -/
theorem ito_formula_interface (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    [ItoStructure U] (P : UncertainProcess U) :
    ItoStructure.ito_formula_statement (U := U) P :=
  ItoStructure.ito_formula_axiom (U := U) P

/-- D-line start: existence/uniqueness layer for uncertain DEs. -/
class UncertainDEWellposednessStructure (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] where
  /-- Existence statement for the uncertain differential equation under the scheme. -/
  existence_statement : Prop
  /-- Uniqueness statement for the uncertain differential equation under the scheme. -/
  uniqueness_statement : Prop
  existence_axiom : existence_statement
  uniqueness_axiom : uniqueness_statement

theorem uncertainDE_existence_interface (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] [UncertainDEWellposednessStructure U de P dt] :
    UncertainDEWellposednessStructure.existence_statement
      (U := U) (de := de) (P := P) (dt := dt) :=
  UncertainDEWellposednessStructure.existence_axiom (U := U) (de := de) (P := P) (dt := dt)

theorem uncertainDE_uniqueness_interface (U : UncertainSpace)
    (de : UncertainDE) (P : UncertainProcess U) (dt : ℝ)
    [EulerSchemeStructure U de P dt] [UncertainDEWellposednessStructure U de P dt] :
    UncertainDEWellposednessStructure.uniqueness_statement
      (U := U) (de := de) (P := P) (dt := dt) :=
  UncertainDEWellposednessStructure.uniqueness_axiom (U := U) (de := de) (P := P) (dt := dt)

/-- D-line start: uncertain programming / solver correctness interface. -/
class UncertainProgrammingStructure (U : UncertainSpace) where
  /-- Decision variable type for the uncertain programming problem. -/
  Decision : Type _
  /-- Objective function to be minimized. -/
  Objective : Decision → ℝ
  /-- Feasibility predicate for candidate decisions. -/
  Feasible : Decision → Prop
  /-- Distinguished solver output (candidate optimum). -/
  solver : Decision
  /-- The solver output is feasible. -/
  solver_feasible : Feasible solver
  /-- The solver output is optimal among all feasible candidates. -/
  solver_optimal : ∀ d, Feasible d → Objective solver ≤ Objective d

theorem uncertainProgramming_solver_correct (U : UncertainSpace)
    [UncertainProgrammingStructure U] :
    (UncertainProgrammingStructure.Feasible (U := U)
      (UncertainProgrammingStructure.solver (U := U))) ∧
    (∀ d,
      UncertainProgrammingStructure.Feasible (U := U) d →
      UncertainProgrammingStructure.Objective (U := U)
        (UncertainProgrammingStructure.solver (U := U))
        ≤ UncertainProgrammingStructure.Objective (U := U) d) := by
  constructor
  · exact UncertainProgrammingStructure.solver_feasible (U := U)
  · intro d hd
    exact UncertainProgrammingStructure.solver_optimal (U := U) d hd

/-- Stage 4: simplified Liu process with only increment-level axioms. -/
structure LiuProcess (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] where
  /-- Underlying uncertain process. -/
  toProcess : UncertainProcess U
  /-- Starts at zero. -/
  start_zero : ∀ ω, toProcess.proc 0 ω = 0
  /-- Independent increments on ordered disjoint intervals. -/
  indep_increments :
    ∀ s t u v, s ≤ t → t ≤ u → u ≤ v →
      ExpectationIndependenceStructure.Independent
        (increment_uncertain U toProcess s t)
        (increment_uncertain U toProcess u v)

/-- Convenience projection: value of a Liu process at time `t`. -/
noncomputable def liuAt (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : LiuProcess U) (t : ℝ) : UncertainVariable U :=
  processAt U L.toProcess t

@[simp] theorem liuAt_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : LiuProcess U) (t : ℝ) (ω : U.Ω) :
    (liuAt U L t).f ω = L.toProcess.proc t ω := rfl

theorem liu_increment_independent (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : LiuProcess U) (s t u v : ℝ) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    ExpectationIndependenceStructure.Independent
      (increment_uncertain U L.toProcess s t)
      (increment_uncertain U L.toProcess u v) :=
  L.indep_increments s t u v hst htu huv

/-- Stage 5: complete Liu process adds path continuity on top of increment axioms. -/
structure CompleteLiuProcess (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    extends LiuProcess U where
  /-- Path continuity for each sample point. -/
  path_continuous : ∀ ω, Continuous (fun t => toLiuProcess.toProcess.proc t ω)
  /--
  Stationary increments at distribution level:
  equal interval lengths give equal increment laws.
  -/
  stationary_increment_law : ∀ s t u v,
    t - s = v - u →
      IncrementLaw U toLiuProcess.toProcess s t = IncrementLaw U toLiuProcess.toProcess u v

theorem completeLiu_increment_independent (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : CompleteLiuProcess U) (s t u v : ℝ) (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) :
    ExpectationIndependenceStructure.Independent
      (increment_uncertain U L.toLiuProcess.toProcess s t)
      (increment_uncertain U L.toLiuProcess.toProcess u v) :=
  L.toLiuProcess.indep_increments s t u v hst htu huv

theorem completeLiu_path_continuous (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : CompleteLiuProcess U) (ω : U.Ω) :
    Continuous (fun t => L.toLiuProcess.toProcess.proc t ω) :=
  L.path_continuous ω

theorem completeLiu_increment_stationary_dist (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : CompleteLiuProcess U) (s t u v : ℝ) (hlen : t - s = v - u) :
    IncrementLaw U L.toLiuProcess.toProcess s t
      = IncrementLaw U L.toLiuProcess.toProcess u v :=
  L.stationary_increment_law s t u v hlen

theorem completeLiu_increment_stationary_shift_dist (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (L : CompleteLiuProcess U) (a s t : ℝ) :
    IncrementLaw U L.toLiuProcess.toProcess (s + a) (t + a)
      = IncrementLaw U L.toLiuProcess.toProcess s t := by
  apply L.stationary_increment_law
  ring

/-- Stage 5 end-to-end chain (abstract): affine map -> center -> zero expectation. -/
theorem e2e_centered_affine_zero (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationConstStructure U]
    (c d : ℝ) (X Y : UncertainVariable U) :
    E U (centered_uncertain U (linearComb_uncertain U c d X Y)) = 0 := by
  exact E_centered U (linearComb_uncertain U c d X Y)

/-- Stage 5 end-to-end concrete check on the linear-distribution branch. -/
theorem e2e_exampleLinear_pipeline :
    (createLinearVariable exampleLinearParams).cdf 2 = linearDistribution exampleLinearParams 2 ∧
    uncertainExpectedValue exampleLinearParams = 2 := by
  constructor
  · rfl
  · exact exampleExpectation


end Uncertainty
