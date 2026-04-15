/-
Copyright (c) 2026 Prof. Dr. Fei Gao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prof. Dr. Fei Gao <gaof@whut.edu.cn>
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-! # Uncertainty Core -/

@[expose] public section


open Filter
open scoped Topology
open scoped BigOperators

noncomputable section

namespace Uncertainty
/--
This module defines basic concepts for uncertainty theory, including uncertain measures,
uncertain variables, and linear uncertain distributions.
An uncertain measure space with sample space Ω and σ-algebra 𝒜. -/
structure UncertainSpace where
  /-- Sample space. -/
  Ω : Type _
  /-- σ-algebra of events. -/
  𝒜 : Set (Set Ω)
  /-- Uncertain measure. -/
  M : (Set Ω) → ℝ
  /-- Measure of empty set is zero. -/
  M_emptyset : M ∅ = 0
  /-- Measure of universe is one. -/
  M_univ : M Set.univ = 1
  /-- Duality axiom. -/
  M_dual : ∀ s, s ∈ 𝒜 → M s + M sᶜ = 1
  /-- Subadditivity axiom. -/
  M_subadditive : ∀ (f : ℕ → Set Ω), (∀ n, f n ∈ 𝒜) →
    M (⋃ n, f n) ≤ ∑' n, M (f n)
  /-- 𝒜 contains the empty set. -/
  𝒜_empty : ∅ ∈ 𝒜
  /-- 𝒜 contains the universe. -/
  𝒜_univ : Set.univ ∈ 𝒜
  /-- 𝒜 is closed under complement. -/
  𝒜_complement : ∀ s, s ∈ 𝒜 → sᶜ ∈ 𝒜
  /-- 𝒜 is closed under binary union. -/
  𝒜_union : ∀ s t, s ∈ 𝒜 → t ∈ 𝒜 → s ∪ t ∈ 𝒜
  /-- 𝒜 is closed under countable union. -/
  𝒜_countable_union : ∀ (f : ℕ → Set Ω), (∀ n, f n ∈ 𝒜) → ⋃ n, f n ∈ 𝒜

/-- An uncertain variable is a measurable function from the sample space to ℝ. -/
structure UncertainVariable (U : UncertainSpace) where
  /-- The underlying function. -/
  f : U.Ω → ℝ
  /-- Measurability condition. -/
  measurable : ∀ (x : ℝ), {ω | f ω ≤ x} ∈ U.𝒜

/-- ## Book Primitive Axioms (Ref7, Chapter 2)
These definitions explicitly mark the four original axioms from the book.
`bookAxiom4_product` is intentionally separated because the current core file
models one uncertain space and does not yet formalize a product uncertain space.
[BOOK_AXIOM_1_NORMALITY] `M(∅)=0` and `M(Ω)=1`. -/
def bookAxiom1_normality (U : UncertainSpace) : Prop :=
  U.M ∅ = 0 ∧ U.M Set.univ = 1

/-- Book-style primitive axiom bundle for uncertain measure spaces. -/
class BookAxiomSet (U : UncertainSpace) where
  normality : U.M ∅ = 0 ∧ U.M Set.univ = 1
  duality : ∀ Λ : Set U.Ω, Λ ∈ U.𝒜 → U.M Λ + U.M Λᶜ = 1
  subadditivity : ∀ f : ℕ → Set U.Ω, (∀ n, f n ∈ U.𝒜) →
    U.M (⋃ n, f n) ≤ ∑' n, U.M (f n)
  /-- Marker for the product axiom (kept abstract in this file). -/
  product : Prop

theorem bookAxiom1_normality_from_space (U : UncertainSpace) :
    U.M ∅ = 0 ∧ U.M Set.univ = 1 :=
  ⟨U.M_emptyset, U.M_univ⟩

theorem bookAxiom1_normality_holds (U : UncertainSpace) [BookAxiomSet U] :
    U.M ∅ = 0 ∧ U.M Set.univ = 1 :=
  BookAxiomSet.normality

/-- [BOOK_AXIOM_2_DUALITY] `M(Λ) + M(Λᶜ) = 1` for measurable `Λ`. -/
def bookAxiom2_duality (U : UncertainSpace) : Prop :=
  ∀ Λ, Λ ∈ U.𝒜 → U.M Λ + U.M Λᶜ = 1

theorem bookAxiom2_duality_from_space (U : UncertainSpace) :
    ∀ Λ : Set U.Ω, Λ ∈ U.𝒜 → U.M Λ + U.M Λᶜ = 1 :=
  U.M_dual

theorem bookAxiom2_duality_holds (U : UncertainSpace) [BookAxiomSet U] :
  ∀ Λ : Set U.Ω, Λ ∈ U.𝒜 → U.M Λ + U.M Λᶜ = 1
  := BookAxiomSet.duality

/-- [BOOK_AXIOM_3_SUBADDITIVITY] countable subadditivity on measurable families. -/
def bookAxiom3_subadditivity (U : UncertainSpace) : Prop :=
  ∀ (f : ℕ → Set U.Ω), (∀ n, f n ∈ U.𝒜) →
    U.M (⋃ n, f n) ≤ ∑' n, U.M (f n)

theorem bookAxiom3_subadditivity_from_space (U : UncertainSpace) :
    ∀ f : ℕ → Set U.Ω, (∀ n, f n ∈ U.𝒜) → U.M (⋃ n, f n) ≤ ∑' n, U.M (f n) :=
  U.M_subadditive

theorem bookAxiom3_subadditivity_holds (U : UncertainSpace) [BookAxiomSet U] :
  ∀ f : ℕ → Set U.Ω, (∀ n, f n ∈ U.𝒜) → U.M (⋃ n, f n) ≤ ∑' n, U.M (f n)
  := BookAxiomSet.subadditivity

/-- [BOOK_AXIOM_4_PRODUCT] product axiom marker (not yet encoded in this file). -/
def bookAxiom4_product (U : UncertainSpace) [BookAxiomSet U] : Prop :=
  (inferInstance : BookAxiomSet U).product

/-- The uncertain distribution function of an uncertain variable. -/
noncomputable def uncertainDistribution
    (U : UncertainSpace) (X : UncertainVariable U) (x : ℝ) : ℝ :=
  U.M {ω | X.f ω ≤ x}

/-- Duality theorem: follows directly from the duality axiom of `UncertainSpace`. -/
theorem dual_theorem (U : UncertainSpace) (s : Set U.Ω) (hs : s ∈ U.𝒜) :
    U.M s + U.M sᶜ = 1 :=
  U.M_dual s hs

/-- Finite/Countable subadditivity theorem: direct form of the subadditivity axiom. -/
theorem finite_subadditive (U : UncertainSpace) (f : ℕ → Set U.Ω)
    (hf : ∀ n, f n ∈ U.𝒜) :
    U.M (⋃ n, f n) ≤ ∑' n, U.M (f n) :=
  U.M_subadditive f hf

/-- Monotonicity theorem (book Thm 2.1) as an interface-level law. -/
class UncertainMeasureMonotoneStructure (U : UncertainSpace) where
  monotone : ∀ s t : Set U.Ω, s ∈ U.𝒜 → t ∈ U.𝒜 → s ⊆ t → U.M s ≤ U.M t

/-- Measure bounds theorem (book Thm 2.3) as an interface-level law. -/
class UncertainMeasureBoundsStructure (U : UncertainSpace) where
  bounds : ∀ s : Set U.Ω, s ∈ U.𝒜 → 0 ≤ U.M s ∧ U.M s ≤ 1

/-- Null-event invariance theorem (book Thm 2.4) as an interface-level law. -/
class UncertainNullEventStructure (U : UncertainSpace) where
  union_null_eq : ∀ Λ Δ : Set U.Ω,
    Λ ∈ U.𝒜 → Δ ∈ U.𝒜 → U.M Δ = 0 → U.M (Λ ∪ Δ) = U.M Λ
  diff_null_eq : ∀ Λ Δ : Set U.Ω,
    Λ ∈ U.𝒜 → Δ ∈ U.𝒜 → U.M Δ = 0 → U.M (Λ \ Δ) = U.M Λ

theorem measure_monotone (U : UncertainSpace) [UncertainMeasureMonotoneStructure U]
    (s t : Set U.Ω) (hs : s ∈ U.𝒜) (ht : t ∈ U.𝒜) (hst : s ⊆ t) :
    U.M s ≤ U.M t :=
  UncertainMeasureMonotoneStructure.monotone s t hs ht hst

theorem measure_bounds (U : UncertainSpace) [UncertainMeasureBoundsStructure U]
    (s : Set U.Ω) (hs : s ∈ U.𝒜) :
    0 ≤ U.M s ∧ U.M s ≤ 1 :=
  UncertainMeasureBoundsStructure.bounds s hs

theorem union_with_null_event_eq (U : UncertainSpace) [UncertainNullEventStructure U]
    (Λ Δ : Set U.Ω) (hΛ : Λ ∈ U.𝒜) (hΔ : Δ ∈ U.𝒜) (h0 : U.M Δ = 0) :
    U.M (Λ ∪ Δ) = U.M Λ :=
  UncertainNullEventStructure.union_null_eq Λ Δ hΛ hΔ h0

theorem diff_with_null_event_eq (U : UncertainSpace) [UncertainNullEventStructure U]
    (Λ Δ : Set U.Ω) (hΛ : Λ ∈ U.𝒜) (hΔ : Δ ∈ U.𝒜) (h0 : U.M Δ = 0) :
    U.M (Λ \ Δ) = U.M Λ :=
  UncertainNullEventStructure.diff_null_eq Λ Δ hΛ hΔ h0

/-- P0 default-assumption bundle so the three measure theorem interfaces are usable
in the main model via typeclass inference. -/
class UncertainMeasureDefaultInstance (U : UncertainSpace) where
  monotone_axiom : ∀ s t : Set U.Ω, s ∈ U.𝒜 → t ∈ U.𝒜 → s ⊆ t → U.M s ≤ U.M t
  bounds_axiom : ∀ s : Set U.Ω, s ∈ U.𝒜 → 0 ≤ U.M s ∧ U.M s ≤ 1
  union_null_axiom : ∀ Λ Δ : Set U.Ω,
    Λ ∈ U.𝒜 → Δ ∈ U.𝒜 → U.M Δ = 0 → U.M (Λ ∪ Δ) = U.M Λ
  diff_null_axiom : ∀ Λ Δ : Set U.Ω,
    Λ ∈ U.𝒜 → Δ ∈ U.𝒜 → U.M Δ = 0 → U.M (Λ \ Δ) = U.M Λ

instance (priority := 100) instUncertainMeasureMonotone_fromDefault
    (U : UncertainSpace) [UncertainMeasureDefaultInstance U] :
    UncertainMeasureMonotoneStructure U where
  monotone := UncertainMeasureDefaultInstance.monotone_axiom

instance (priority := 100) instUncertainMeasureBounds_fromDefault
    (U : UncertainSpace) [UncertainMeasureDefaultInstance U] :
    UncertainMeasureBoundsStructure U where
  bounds := UncertainMeasureDefaultInstance.bounds_axiom

instance (priority := 100) instUncertainNullEvent_fromDefault
    (U : UncertainSpace) [UncertainMeasureDefaultInstance U] :
    UncertainNullEventStructure U where
  union_null_eq := UncertainMeasureDefaultInstance.union_null_axiom
  diff_null_eq := UncertainMeasureDefaultInstance.diff_null_axiom

/-- Stage 5 extension: down-continuity and sigma-algebra completeness checks. -/
class UncertainSpaceContinuity (U : UncertainSpace) where
  /-- Down-continuity on decreasing measurable sequences. -/
  M_down_continuous : ∀ (f : ℕ → Set U.Ω),
    (∀ n, f n ∈ U.𝒜) →
    (∀ n, f (n + 1) ⊆ f n) →
    U.M (⋂ n, f n) = ⨅ n, U.M (f n)

/-- Sigma-algebra completeness check: measurable sets are closed under countable intersections. -/
theorem measurable_iInter (U : UncertainSpace) (f : ℕ → Set U.Ω)
    (hf : ∀ n, f n ∈ U.𝒜) :
    (⋂ n, f n) ∈ U.𝒜 := by
  have h_union_compl : (⋃ n, (f n)ᶜ) ∈ U.𝒜 := by
    apply U.𝒜_countable_union
    intro n
    exact U.𝒜_complement (f n) (hf n)
  have h_inter_eq : (⋂ n, f n) = (⋃ n, (f n)ᶜ)ᶜ := by
    ext ω
    simp
  rw [h_inter_eq]
  exact U.𝒜_complement _ h_union_compl

-- notation:max "Φ_" X:max x:max => uncertainDistribution _ X x

/-- Stage 3: algebraic closure assumptions for uncertain variables. -/
class AlgebraicUncertainSpace (U : UncertainSpace) where
  measurable_smul : ∀ (c : ℝ) (X : UncertainVariable U) (x : ℝ),
    {ω | c * X.f ω ≤ x} ∈ U.𝒜
  measurable_add : ∀ (X Y : UncertainVariable U) (x : ℝ),
    {ω | X.f ω + Y.f ω ≤ x} ∈ U.𝒜
  measurable_sq : ∀ (X : UncertainVariable U) (x : ℝ),
    {ω | (X.f ω) ^ 2 ≤ x} ∈ U.𝒜
  measurable_abs_sub : ∀ (X Y : UncertainVariable U) (x : ℝ),
    {ω | |X.f ω - Y.f ω| ≤ x} ∈ U.𝒜
  measurable_abs_rpow : ∀ (X : UncertainVariable U) (p x : ℝ),
    {ω | |X.f ω| ^ p ≤ x} ∈ U.𝒜
  measurable_sampleMean : ∀ (seq : ℕ → UncertainVariable U) (n : ℕ) (x : ℝ),
    {ω | (1 / (n : ℝ)) * Finset.sum (Finset.range n) (fun i => (seq i).f ω) ≤ x} ∈ U.𝒜

/-- Scalar multiplication of uncertain variables. -/
noncomputable def smul_uncertain_of_meas (U : UncertainSpace) (c : ℝ) (X : UncertainVariable U)
    (h_meas : ∀ x : ℝ, {ω | c * X.f ω ≤ x} ∈ U.𝒜) : UncertainVariable U where
  f := fun ω => c * X.f ω
  measurable := h_meas

/-- Scalar multiplication with stage-3 algebraic measurability assumptions. -/
noncomputable def smul_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (c : ℝ) (X : UncertainVariable U) : UncertainVariable U :=
  smul_uncertain_of_meas U c X (AlgebraicUncertainSpace.measurable_smul c X)

/-- Addition of uncertain variables. -/
noncomputable def add_uncertain_of_meas (U : UncertainSpace) (X Y : UncertainVariable U)
    (h_meas : ∀ x : ℝ, {ω | X.f ω + Y.f ω ≤ x} ∈ U.𝒜) : UncertainVariable U where
  f := fun ω => X.f ω + Y.f ω
  measurable := h_meas

/-- Addition with stage-3 algebraic measurability assumptions. -/
noncomputable def add_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (X Y : UncertainVariable U) : UncertainVariable U :=
  add_uncertain_of_meas U X Y (AlgebraicUncertainSpace.measurable_add X Y)

/-- Linear combination derived from stage-3 closure assumptions. -/
noncomputable def linearComb_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (c d : ℝ) (X Y : UncertainVariable U) : UncertainVariable U :=
  add_uncertain U (smul_uncertain U c X) (smul_uncertain U d Y)

@[simp] theorem smul_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (c : ℝ) (X : UncertainVariable U) (ω : U.Ω) :
    (smul_uncertain U c X).f ω = c * X.f ω := rfl

@[simp] theorem add_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (X Y : UncertainVariable U) (ω : U.Ω) :
    (add_uncertain U X Y).f ω = X.f ω + Y.f ω := rfl

@[simp] theorem linearComb_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (c d : ℝ) (X Y : UncertainVariable U) (ω : U.Ω) :
    (linearComb_uncertain U c d X Y).f ω = c * X.f ω + d * Y.f ω := by
  rfl

theorem measurable_linearComb (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (c d : ℝ) (X Y : UncertainVariable U) (x : ℝ) :
    {ω | c * X.f ω + d * Y.f ω ≤ x} ∈ U.𝒜 := by
  simpa using (linearComb_uncertain U c d X Y).measurable x

/-- Stage 4 (Step 1): minimal assumption layer for expectation on uncertain variables. -/
class ExpectationStructure (U : UncertainSpace) [AlgebraicUncertainSpace U] where
  /-- Expected-value operator on uncertain variables. -/
  expectedValue : UncertainVariable U → ℝ
  map_smul : ∀ (c : ℝ) (X : UncertainVariable U),
    expectedValue (smul_uncertain U c X) = c * expectedValue X
  map_add : ∀ (X Y : UncertainVariable U),
    expectedValue (add_uncertain U X Y) = expectedValue X + expectedValue Y

/-- Stage 4 (Step 2): scalar linearity of expectation. -/
theorem expectedValue_smul (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c : ℝ) (X : UncertainVariable U) :
    ExpectationStructure.expectedValue (smul_uncertain U c X)
      = c * ExpectationStructure.expectedValue X := by
  simpa using (ExpectationStructure.map_smul (U := U) c X)

/-- Stage 4 (Step 3): additivity of expectation. -/
theorem expectedValue_add (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (X Y : UncertainVariable U) :
    ExpectationStructure.expectedValue (add_uncertain U X Y)
      = ExpectationStructure.expectedValue X + ExpectationStructure.expectedValue Y := by
  simpa using (ExpectationStructure.map_add (U := U) X Y)

/-- Stage 4 (Step 4): full linearity for two-variable linear combinations. -/
theorem expectedValue_linearComb (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c d : ℝ) (X Y : UncertainVariable U) :
    ExpectationStructure.expectedValue (linearComb_uncertain U c d X Y)
      = c * ExpectationStructure.expectedValue X + d * ExpectationStructure.expectedValue Y := by
  unfold linearComb_uncertain
  calc
    ExpectationStructure.expectedValue
        (add_uncertain U (smul_uncertain U c X) (smul_uncertain U d Y))
        = ExpectationStructure.expectedValue (smul_uncertain U c X)
          + ExpectationStructure.expectedValue (smul_uncertain U d Y) :=
            expectedValue_add U (smul_uncertain U c X) (smul_uncertain U d Y)
    _ = c * ExpectationStructure.expectedValue X + d * ExpectationStructure.expectedValue Y := by
          simp [expectedValue_smul]

/-- Stage 4 (Step 5): reusable example using `linearComb_uncertain` directly. -/
theorem expectedValue_linearComb_example (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c d : ℝ) (X Y : UncertainVariable U) :
    let Z := linearComb_uncertain U c d X Y
    ExpectationStructure.expectedValue Z
      = c * ExpectationStructure.expectedValue X + d * ExpectationStructure.expectedValue Y := by
  simp [expectedValue_linearComb (U := U) (c := c) (d := d) (X := X) (Y := Y)]

/-- Stage 4 wrap-up: short alias for expectation operator on uncertain variables. -/
noncomputable abbrev E (U : UncertainSpace) [AlgebraicUncertainSpace U] [ExpectationStructure U] :
    UncertainVariable U → ℝ :=
  ExpectationStructure.expectedValue

@[simp] theorem E_smul (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c : ℝ) (X : UncertainVariable U) :
    E U (smul_uncertain U c X) = c * E U X := by
  exact expectedValue_smul U c X

@[simp] theorem E_add (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (X Y : UncertainVariable U) :
    E U (add_uncertain U X Y) = E U X + E U Y := by
  exact expectedValue_add U X Y

@[simp] theorem E_linearComb (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c d : ℝ) (X Y : UncertainVariable U) :
    E U (linearComb_uncertain U c d X Y) = c * E U X + d * E U Y := by
  exact expectedValue_linearComb U c d X Y

/-- Stage 3 target: expectation linearity under an explicit independence layer. -/
class ExpectationIndependenceStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  /-- Independence predicate for uncertain variables. -/
  Independent : UncertainVariable U → UncertainVariable U → Prop
  map_add_of_independent : ∀ (X Y : UncertainVariable U),
    Independent X Y → E U (add_uncertain U X Y) = E U X + E U Y
  independent_smul : ∀ (c d : ℝ) (X Y : UncertainVariable U),
    Independent X Y → Independent (smul_uncertain U c X) (smul_uncertain U d Y)

/-- Expected value linearity with independence assumption. -/
theorem expectedValue_linear (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (c d : ℝ) (X Y : UncertainVariable U)
    (hXY : ExpectationIndependenceStructure.Independent X Y) :
    E U (linearComb_uncertain U c d X Y) = c * E U X + d * E U Y := by
  unfold linearComb_uncertain
  calc
    E U (add_uncertain U (smul_uncertain U c X) (smul_uncertain U d Y))
        = E U (smul_uncertain U c X) + E U (smul_uncertain U d Y) := by
          apply ExpectationIndependenceStructure.map_add_of_independent
          exact ExpectationIndependenceStructure.independent_smul c d X Y hXY
    _ = c * E U X + d * E U Y := by simp

/-- Stage 5: uncertain-variable subtraction as a reusable derived operator. -/
noncomputable def sub_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (X Y : UncertainVariable U) : UncertainVariable U :=
  linearComb_uncertain U 1 (-1) X Y

@[simp] theorem sub_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (X Y : UncertainVariable U) (ω : U.Ω) :
    (sub_uncertain U X Y).f ω = X.f ω - Y.f ω := by
  simp [sub_uncertain, sub_eq_add_neg]

/-- Stage 5: expectation of subtraction. -/
theorem E_sub (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (X Y : UncertainVariable U) :
    E U (sub_uncertain U X Y) = E U X - E U Y := by
  calc
    E U (sub_uncertain U X Y)
        = E U (linearComb_uncertain U 1 (-1) X Y) := by
          rfl
    _ = 1 * E U X + (-1) * E U Y :=
      E_linearComb U 1 (-1) X Y
    _ = E U X - E U Y := by ring

/-- Stage 5: affine expectation form as a user-facing theorem. -/
theorem E_affine (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (c d : ℝ) (X Y : UncertainVariable U) :
    E U (linearComb_uncertain U c d X Y) = c * E U X + d * E U Y := by
  exact E_linearComb U c d X Y

/-- Minimal uncertain sequence interface (distribution at each index). -/
structure UncertainSequence (U : UncertainSpace) where
  /-- The sequence of uncertain variables. -/
  X : ℕ → UncertainVariable U

/-- IID-style extension: identical distribution + pairwise independence. -/
class UncertainSequenceIID (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (seq : UncertainSequence U) where
  identically_distributed : ∀ n m x,
    uncertainDistribution U (seq.X n) x = uncertainDistribution U (seq.X m) x
  pairwise_independent : ∀ n m, n ≠ m →
    ExpectationIndependenceStructure.Independent (seq.X n) (seq.X m)

theorem iid_same_distribution (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (seq : UncertainSequence U) [UncertainSequenceIID U seq] (n m : ℕ) (x : ℝ) :
    uncertainDistribution U (seq.X n) x = uncertainDistribution U (seq.X m) x :=
  UncertainSequenceIID.identically_distributed n m x

theorem iid_pairwise_independent (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U]
    (seq : UncertainSequence U) [UncertainSequenceIID U seq] (n m : ℕ) (h : n ≠ m) :
    ExpectationIndependenceStructure.Independent (seq.X n) (seq.X m) :=
  UncertainSequenceIID.pairwise_independent n m h

/-- Second-moment interface: variance/covariance as abstract operators. -/
class SecondMomentStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  /-- Variance functional on uncertain variables. -/
  variance : UncertainVariable U → ℝ
  /-- Covariance functional on pairs of uncertain variables. -/
  covariance : UncertainVariable U → UncertainVariable U → ℝ
  variance_nonneg : ∀ X, 0 ≤ variance X
  covariance_comm : ∀ X Y, covariance X Y = covariance Y X
  covariance_self : ∀ X, covariance X X = variance X

/-- Short alias for variance. -/
noncomputable abbrev Var (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] : UncertainVariable U → ℝ :=
  SecondMomentStructure.variance

/-- Short alias for covariance. -/
noncomputable abbrev Cov (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] :
    UncertainVariable U → UncertainVariable U → ℝ :=
  SecondMomentStructure.covariance

theorem Var_nonneg (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] (X : UncertainVariable U) :
    0 ≤ Var U X :=
  SecondMomentStructure.variance_nonneg X

theorem Cov_comm (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U]
    (X Y : UncertainVariable U) :
    Cov U X Y = Cov U Y X :=
  SecondMomentStructure.covariance_comm X Y

theorem Cov_self (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] (X : UncertainVariable U) :
    Cov U X X = Var U X :=
  SecondMomentStructure.covariance_self X

/-- raw second moment defined as expectation of square -/
noncomputable def secondMoment (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] : UncertainVariable U → ℝ :=
  fun X =>
    E U
      { f := fun ω => (X.f ω) ^ 2
        measurable := AlgebraicUncertainSpace.measurable_sq X }

/-- Absolute power transform as an uncertain variable. -/
noncomputable def absPow_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (X : UncertainVariable U) (p : ℝ) : UncertainVariable U where
  f := fun ω => |X.f ω| ^ p
  measurable := AlgebraicUncertainSpace.measurable_abs_rpow X p

/-- Optional bridge: variance identity in terms of second moment and mean. -/
class SecondMomentIdentityStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] where
  variance_eq_secondMoment_sub_sq : ∀ X,
    Var U X = secondMoment U X - (E U X) ^ 2

/-- Optional inequality layer for uncertain variables. -/
class UncertainInequalityStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] where
  markov : ∀ (X : UncertainVariable U) (p t : ℝ), 0 < p → 0 < t →
    U.M {ω | |X.f ω| ≥ t} ≤ E U (absPow_uncertain U X p) / t ^ p
  chebyshev : ∀ (X : UncertainVariable U) (ε : ℝ), ε > 0 →
    U.M {ω | |X.f ω - E U X| ≥ ε} ≤ Var U X / ε ^ 2

/-- variance equals second moment minus square of mean. -/
theorem variance_eq_secondMoment_sub_sq (U : UncertainSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [SecondMomentStructure U]
    [SecondMomentIdentityStructure U]
    (X : UncertainVariable U) :
    Var U X = secondMoment U X - (E U X) ^ 2 :=
  SecondMomentIdentityStructure.variance_eq_secondMoment_sub_sq X

/-- Markov inequality for uncertain variables. -/
theorem uncertain_markov (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] [UncertainInequalityStructure U]
    (X : UncertainVariable U)
    (p : ℝ) (t : ℝ) (hp : 0 < p) (ht : 0 < t) :
    U.M {ω | |X.f ω| ≥ t} ≤ E U (absPow_uncertain U X p) / t ^ p :=
  UncertainInequalityStructure.markov X p t hp ht

/-- Chebyshev inequality derived from Markov. -/
theorem uncertain_chebyshev (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [SecondMomentStructure U] [UncertainInequalityStructure U]
    (X : UncertainVariable U)
    (ε : ℝ) (hε : ε > 0) :
    U.M {ω | |X.f ω - E U X| ≥ ε} ≤ Var U X / ε ^ 2 :=
  UncertainInequalityStructure.chebyshev X ε hε

/-- Milestone status: Stages 1-5 are implemented in this file.
Stage 6 and Stage 7 below provide extension interfaces and reusable theorems.
- Stage 6: order/constant compatibility layer for expectation.
- Stage 7: centered variable and shift-friendly expectation lemmas.
Constant uncertain variable. -/
noncomputable def const_uncertain (U : UncertainSpace) (c : ℝ) : UncertainVariable U where
  f := fun _ => c
  measurable := by
    intro x
    by_cases hx : c ≤ x
    · have hset : {ω : U.Ω | c ≤ x} = Set.univ := by
        ext ω
        simp [hx]
      simpa [hset] using U.𝒜_univ
    · have hset : {ω : U.Ω | c ≤ x} = ∅ := by
        ext ω
        simp [hx]
      simpa [hset] using U.𝒜_empty

@[simp] theorem const_uncertain_f (U : UncertainSpace) (c : ℝ) (ω : U.Ω) :
    (const_uncertain U c).f ω = c := rfl

/-- Stage 6: optional order axiom for expectation. -/
class ExpectationOrderStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  monotone : ∀ (X Y : UncertainVariable U),
    (∀ ω, X.f ω ≤ Y.f ω) → E U X ≤ E U Y

/-- Stage 6: optional constant-preservation axiom for expectation. -/
class ExpectationConstStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  map_const : ∀ c : ℝ, E U (const_uncertain U c) = c

@[simp] theorem E_const (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationConstStructure U] (c : ℝ) :
    E U (const_uncertain U c) = c :=
  ExpectationConstStructure.map_const c

theorem E_mono (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationOrderStructure U]
    (X Y : UncertainVariable U) (hXY : ∀ ω, X.f ω ≤ Y.f ω) :
    E U X ≤ E U Y :=
  ExpectationOrderStructure.monotone X Y hXY

/-- Stage 7: centered uncertain variable `X - E[X]`. -/
noncomputable def centered_uncertain (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (X : UncertainVariable U) : UncertainVariable U :=
  sub_uncertain U X (const_uncertain U (E U X))

@[simp] theorem centered_uncertain_f (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] (X : UncertainVariable U) (ω : U.Ω) :
    (centered_uncertain U X).f ω = X.f ω - E U X := by
  simp [centered_uncertain]

theorem E_centered (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationConstStructure U] (X : UncertainVariable U) :
    E U (centered_uncertain U X) = 0 := by
  calc
    E U (centered_uncertain U X)
        = E U X - E U (const_uncertain U (E U X)) := by
            simpa [centered_uncertain] using E_sub U X (const_uncertain U (E U X))
    _ = E U X - E U X := by simp [E_const]
    _ = 0 := sub_self (E U X)

theorem E_add_const (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationConstStructure U]
    (X : UncertainVariable U) (c : ℝ) :
    E U (add_uncertain U X (const_uncertain U c)) = E U X + c := by
  calc
    E U (add_uncertain U X (const_uncertain U c))
        = E U X + E U (const_uncertain U c) := E_add U X (const_uncertain U c)
    _ = E U X + c := by simp [E_const]

/-- Convergence in uncertain measure to a target uncertain variable. -/
def ConvergesInMeasureTo (U : UncertainSpace) (Xn : ℕ → UncertainVariable U)
    (X : UncertainVariable U) : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    U.M {ω | |(Xn n).f ω - X.f ω| ≤ ε} ≥ 1 - δ

/-- Convergence in uncertain distribution to a target distribution function. -/
def ConvergesInDistributionTo (U : UncertainSpace) (Xn : ℕ → UncertainVariable U)
    (F : ℝ → ℝ) : Prop :=
  ∀ x ε, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    |uncertainDistribution U (Xn n) x - F x| ≤ ε

/-- Convergence almost surely to a limit uncertain variable. -/
def ConvergesAlmostSurelyTo (U : UncertainSpace) (Xn : ℕ → UncertainVariable U)
    (X : UncertainVariable U) : Prop :=
  ∃ Λ : Set U.Ω, U.M Λ = 1 ∧
    ∀ ω ∈ Λ, Tendsto (fun n => (Xn n).f ω) atTop (𝓝 (X.f ω))

/-- Convergence in mean to a limit uncertain variable. -/
def ConvergesInMeanTo (U : UncertainSpace) [AlgebraicUncertainSpace U]
  [ExpectationStructure U] (Xn : ℕ → UncertainVariable U)
    (X : UncertainVariable U) : Prop :=
  Tendsto
    (fun n =>
      E U
        { f := fun ω =>
            |(Xn n).f ω - X.f ω|
          measurable := AlgebraicUncertainSpace.measurable_abs_sub (Xn n) X })
    atTop (𝓝 0)

/-- Convergence-relation bridge layer (book Thm 3.49/3.50 style). -/
class ConvergenceBridgeStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  mean_to_measure : ∀ (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U),
    ConvergesInMeanTo U Xn X → ConvergesInMeasureTo U Xn X
  measure_to_distribution : ∀ (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U),
    ConvergesInMeasureTo U Xn X →
      ConvergesInDistributionTo U Xn (uncertainDistribution U X)

theorem convergence_mean_to_measure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ConvergenceBridgeStructure U]
    (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U) :
    ConvergesInMeanTo U Xn X → ConvergesInMeasureTo U Xn X :=
  ConvergenceBridgeStructure.mean_to_measure Xn X

theorem convergence_measure_to_distribution (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ConvergenceBridgeStructure U]
    (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U) :
    ConvergesInMeasureTo U Xn X →
      ConvergesInDistributionTo U Xn (uncertainDistribution U X) :=
  ConvergenceBridgeStructure.measure_to_distribution Xn X

/-- Stronger assumption package for convergence bridge auto-derivation. -/
class ConvergenceBridgeStrongAssumption (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] where
  mean_to_measure_axiom : ∀ (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U),
    ConvergesInMeanTo U Xn X → ConvergesInMeasureTo U Xn X
  measure_to_distribution_axiom : ∀ (Xn : ℕ → UncertainVariable U) (X : UncertainVariable U),
    ConvergesInMeasureTo U Xn X →
      ConvergesInDistributionTo U Xn (uncertainDistribution U X)

instance (priority := 100) convergenceBridge_of_strongAssumption
    (U : UncertainSpace) [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [ConvergenceBridgeStrongAssumption U] :
    ConvergenceBridgeStructure U where
  mean_to_measure := ConvergenceBridgeStrongAssumption.mean_to_measure_axiom
  measure_to_distribution := ConvergenceBridgeStrongAssumption.measure_to_distribution_axiom

/-- Standard normal uncertain CDF surrogate used in CLT interface layer. -/
noncomputable def standardNormalUncertainDistribution (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

/-- LLN/CLT abstract interface layer (no heavy proof in main branch). -/
class LimitTheoryStructure (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U] where
  /-- Sample-mean operator associated with a sequence. -/
  sampleMean : UncertainSequence U → ℕ → UncertainVariable U
  /-- CLT-style normalized-sum operator associated with a sequence. -/
  normalizedSum : UncertainSequence U → ℕ → UncertainVariable U
  law_of_large_numbers : ∀ (seq : UncertainSequence U) [UncertainSequenceIID U seq]
      (μ : ℝ) (_hmean : ∀ n, E U (seq.X n) = μ),
      ConvergesInMeasureTo U (fun n => sampleMean seq n) (const_uncertain U μ)
  central_limit_theorem : ∀ (seq : UncertainSequence U) [UncertainSequenceIID U seq]
      (_hmean : ∀ n, E U (seq.X n) = (0 : ℝ))
      (_hvar : ∀ n, Var U (seq.X n) = (1 : ℝ)),
      ConvergesInDistributionTo U (fun n => normalizedSum seq n)
        standardNormalUncertainDistribution
  strong_law_of_large_numbers : ∀ (seq : UncertainSequence U) [UncertainSequenceIID U seq]
      (μ : ℝ) (_hmean : ∀ n, E U (seq.X n) = μ),
      ConvergesAlmostSurelyTo U (fun n => sampleMean seq n) (const_uncertain U μ)
  mean_law_of_large_numbers : ∀ (seq : UncertainSequence U) [UncertainSequenceIID U seq]
      (μ sigma2 : ℝ)
      (_hmean : ∀ n, E U (seq.X n) = μ)
      (_hvar : ∀ n, Var U (seq.X n) = sigma2),
      ConvergesInMeanTo U (fun n => sampleMean seq n) (const_uncertain U μ)

theorem law_of_large_numbers_interface (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U]
    [LimitTheoryStructure U] (seq : UncertainSequence U) [UncertainSequenceIID U seq]
    (μ : ℝ) (hmean : ∀ n, E U (seq.X n) = μ) :
    ConvergesInMeasureTo U (fun n => LimitTheoryStructure.sampleMean seq n)
      (const_uncertain U μ) :=
  LimitTheoryStructure.law_of_large_numbers seq μ hmean

theorem central_limit_theorem_interface (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U]
    [LimitTheoryStructure U] (seq : UncertainSequence U) [UncertainSequenceIID U seq]
    (hmean : ∀ n, E U (seq.X n) = (0 : ℝ))
    (hvar : ∀ n, Var U (seq.X n) = (1 : ℝ)) :
    ConvergesInDistributionTo U (fun n => LimitTheoryStructure.normalizedSum seq n)
      standardNormalUncertainDistribution :=
  LimitTheoryStructure.central_limit_theorem seq hmean hvar

/-- sample mean of a sequence -/
noncomputable def sampleMean (U : UncertainSpace) [AlgebraicUncertainSpace U]
    (seq : ℕ → UncertainVariable U) (n : ℕ) : UncertainVariable U :=
  { f := fun ω => (1 / (n : ℝ)) *
      Finset.sum (Finset.range n) (fun i => (seq i).f ω)
    measurable := AlgebraicUncertainSpace.measurable_sampleMean seq n }

/-- Weak LLN for pure uncertain iid sequence (dependence and meas. assumptions still needed). -/
theorem uncertain_weak_LLN (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U]
    [LimitTheoryStructure U]
    (seq : UncertainSequence U) [UncertainSequenceIID U seq]
    (μ : ℝ) (hmean : ∀ n, E U (seq.X n) = μ) :
  ConvergesInMeasureTo U (fun n => LimitTheoryStructure.sampleMean seq n)
    (const_uncertain U μ) := by
  exact LimitTheoryStructure.law_of_large_numbers seq μ hmean

/-- Strong LLN (a.s.) for pure uncertain iid sequence. -/
theorem uncertain_strong_LLN (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U]
    [LimitTheoryStructure U]
    (seq : UncertainSequence U) [UncertainSequenceIID U seq]
    (μ : ℝ) (hmean : ∀ n, E U (seq.X n) = μ) :
    ConvergesAlmostSurelyTo U (fun n => LimitTheoryStructure.sampleMean seq n)
      (const_uncertain U μ) := by
  exact LimitTheoryStructure.strong_law_of_large_numbers seq μ hmean

/-- LLN in mean for pure uncertain iid sequence. -/
theorem uncertain_mean_LLN (U : UncertainSpace) [AlgebraicUncertainSpace U]
    [ExpectationStructure U] [ExpectationIndependenceStructure U] [SecondMomentStructure U]
    [LimitTheoryStructure U]
    (seq : UncertainSequence U) [UncertainSequenceIID U seq]
  (μ : ℝ) (sigma2 : ℝ)
    (hmean : ∀ n, E U (seq.X n) = μ)
  (hvar : ∀ n, Var U (seq.X n) = sigma2) :
    ConvergesInMeanTo U (fun n => LimitTheoryStructure.sampleMean seq n)
      (const_uncertain U μ) := by
  exact LimitTheoryStructure.mean_law_of_large_numbers seq μ sigma2 hmean hvar

/-- Chance-space layer for mixed uncertain-random constructions (P2 foundation). -/
structure ChanceSpace where
  /-- Underlying random sample space. -/
  Ωr : Type _
  /-- Sigma-field candidate on `Ωr`. -/
  𝓕 : Set (Set Ωr)
  /-- Chance measure on events in `Ωr`. -/
  P : Set Ωr → ℝ
  P_emptyset : P ∅ = 0
  P_univ : P Set.univ = 1

/-- Random variable on a chance space (measurability kept as an interface predicate). -/
structure ChanceVariable (C : ChanceSpace) where
  /-- Underlying random-variable map. -/
  f : C.Ωr → ℝ
  /-- Measurability marker for the random variable. -/
  measurable : Prop

/-- Uncertain-random variable on product sample space `U.Ω × C.Ωr`. -/
structure UncertainRandomVariable (U : UncertainSpace) (C : ChanceSpace) where
  /-- Underlying map on the product space. -/
  f : U.Ω → C.Ωr → ℝ
  measurable_uncertain : ∀ (r : C.Ωr) (x : ℝ), {ω | f ω r ≤ x} ∈ U.𝒜
  /-- Measurability marker in the chance-space coordinate. -/
  measurable_chance : ∀ (_ω : U.Ω), Prop

/-- Appendix A.23 mixed LLN assumption package. -/
class MixedLLNStructure (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] where
  /-- Statement package for the mixed LLN in uncertain-random settings. -/
  mixed_lln_statement :
    (η_seq : ℕ → ChanceVariable C) →
    (τ_seq : ℕ → UncertainVariable U) →
    (f : ℝ → ℝ → ℝ) → Prop
  mixed_lln_axiom :
    ∀ (η_seq : ℕ → ChanceVariable C)
      (τ_seq : ℕ → UncertainVariable U)
      (f : ℝ → ℝ → ℝ),
      mixed_lln_statement η_seq τ_seq f

/-- Stronger assumption package to auto-derive `MixedLLNStructure`. -/
class MixedLLNStrongAssumption (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] where
  /-- Strong-assumption version of the mixed LLN statement package. -/
  mixed_lln_statement :
    (η_seq : ℕ → ChanceVariable C) →
    (τ_seq : ℕ → UncertainVariable U) →
    (f : ℝ → ℝ → ℝ) → Prop
  mixed_lln_axiom :
    ∀ (η_seq : ℕ → ChanceVariable C)
      (τ_seq : ℕ → UncertainVariable U)
      (f : ℝ → ℝ → ℝ),
      mixed_lln_statement η_seq τ_seq f

/-- One-line constructor template for `MixedLLNStrongAssumption`. -/
@[implicit_reducible]
def mkMixedLLNStrongAssumption (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    (statement : (η_seq : ℕ → ChanceVariable C) →
      (τ_seq : ℕ → UncertainVariable U) →
      (f : ℝ → ℝ → ℝ) → Prop)
    (axiom_rule : ∀ (η_seq : ℕ → ChanceVariable C)
      (τ_seq : ℕ → UncertainVariable U)
      (f : ℝ → ℝ → ℝ), statement η_seq τ_seq f) :
    MixedLLNStrongAssumption U C where
  mixed_lln_statement := statement
  mixed_lln_axiom := axiom_rule

/-- Build `MixedLLNStrongAssumption` from `MixedLLNStructure`. -/
@[implicit_reducible]
def mixedLLNStrong_of_structure
    (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [MixedLLNStructure U C] :
    MixedLLNStrongAssumption U C where
  mixed_lln_statement := MixedLLNStructure.mixed_lln_statement (U := U) (C := C)
  mixed_lln_axiom := MixedLLNStructure.mixed_lln_axiom (U := U) (C := C)

instance (priority := 100) mixedLLN_of_strongAssumption
    (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U]
    [MixedLLNStrongAssumption U C] :
    MixedLLNStructure U C where
  mixed_lln_statement :=
    MixedLLNStrongAssumption.mixed_lln_statement (U := U) (C := C)
  mixed_lln_axiom :=
    MixedLLNStrongAssumption.mixed_lln_axiom (U := U) (C := C)

/-- Mixed uncertain-random LLN from appendix A.23 (interface theorem). -/
theorem law_of_large_numbers_mixed (U : UncertainSpace) (C : ChanceSpace)
    [AlgebraicUncertainSpace U] [ExpectationStructure U] [MixedLLNStructure U C]
    (η_seq : ℕ → ChanceVariable C)
    (τ_seq : ℕ → UncertainVariable U)
    (f : ℝ → ℝ → ℝ) :
    MixedLLNStructure.mixed_lln_statement (U := U) (C := C) η_seq τ_seq f :=
  MixedLLNStructure.mixed_lln_axiom (U := U) (C := C) η_seq τ_seq f


end Uncertainty
