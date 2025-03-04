/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Divisors on subsets of normed fields

This file defines divisors, a standard book-keeping tool in complex analysis
used to keep track of pole/vanishing orders of meromorphic objects, typically
functions or differential forms. It provides supporting API and establishes
divisors as an instance of a lattice ordered commutative group.

Throughout the present file, `𝕜` denotes a nontrivially normed field, and `U` a
subset of `𝕜`.

## TODOs

- Constructions: The divisor of a meromorphic function, behavior under product
  of meromorphic functions, behavior under addition, behavior under restriction
- Construction: The divisor of a rational polynomial
-/

open Filter Metric Real Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A divisor on `U` is a function `𝕜 → ℤ` whose support is discrete within `U` and
entirely contained within `U`.  The theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that this is equivalent to
the textbook definition, which requires the support of `f` to be locally finite
within `U`.
-/

/-- A divisor on `U` is a triple specified below. -/
structure DivisorOn (U : Set 𝕜) where
  /-- A function `𝕜 → ℤ` -/
  toFun : 𝕜 → ℤ
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support ⊆ U
  /-- A proof the the support is discrete within `U` -/
  supportDiscreteWithinDomain' : toFun =ᶠ[codiscreteWithin U] 0

/-- A divisor is a divisor on `⊤ : Set 𝕜`. -/
def Divisor (𝕜 : Type*) [NontriviallyNormedField 𝕜] := DivisorOn (⊤ : Set 𝕜)

/-- The condition `supportDiscreteWithinU` in a divisor is equivalent to saying
that the support is locally finite near every point of `U`. -/
theorem supportDiscreteWithin_iff_locallyFiniteWithin {f : 𝕜 → ℤ} (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : 𝕜 → ℤ) x}) := by
    ext x
    simp only [Function.mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

namespace DivisorOn

/-- Divisors are `FunLike`: the coercion from divisors to functions is injective. -/
instance : FunLike (DivisorOn U) 𝕜 ℤ where
  coe D := D.toFun
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

/-- This allows writing `D.support` instead of `Function.support D` -/
abbrev support (D : DivisorOn U)  := Function.support D

lemma supportWithinDomain (D : DivisorOn U) : D.support ⊆ U := D.supportWithinDomain'

lemma supportDiscreteWithinDomain (D : DivisorOn U) : D =ᶠ[codiscreteWithin U] 0 :=
  D.supportDiscreteWithinDomain'

/-- Helper lemma for the `ext` tactic: two divisors are equal if their
associated functions agree. -/
@[ext]
theorem ext {D₁ D₂ : DivisorOn U} (h : ∀ a, D₁ a = D₂ a) : D₁ = D₂ := DFunLike.ext _ _ h

/-!
## Elementary properties of the support
-/

/-- The support of a divisor is discrete. -/
theorem discreteSupport (D : DivisorOn U) : DiscreteTopology D.support := by
  have : Function.support D = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  convert discreteTopology_of_codiscreteWithin (D.supportDiscreteWithinDomain)

/-- If `U` is closed, the the support of a divisor on `U` is also closed. -/
theorem closedSupport (D : DivisorOn U) (hU : IsClosed U) :
    IsClosed D.support := by
  convert closed_compl_of_codiscreteWithin D.supportDiscreteWithinDomain hU
  ext x
  constructor
  · intro hx
    simp_all [D.supportWithinDomain hx]
  · intro hx
    simp_all

/-- If `U` is closed, the the support of a divisor on `U` is finite. -/
theorem finiteSupport (D : DivisorOn U) (hU : IsCompact U) :
    Set.Finite D.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

/-!
## Lattice ordered group structure

This section equips divisors on `U` with the standard structure of a lattice
ordered group, where addition, comparison, min and max of divisors are defined
pointwise.
-/

/-- Divisors have a zero -/
instance : Zero (DivisorOn U) where
  zero := ⟨fun _ ↦ 0, by simp, Eq.eventuallyEq rfl⟩

/-- Helper lemma for the `simp` tactic: the function of the zero-divisor is the
zero function. -/
@[simp]
theorem zero_fun : ((0 : DivisorOn U) : 𝕜 → ℤ) = 0 := rfl

/-- Divisors can be added -/
instance : Add (DivisorOn U) where
  add D₁ D₂ := {
    toFun := D₁ + D₂
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        Function.nmem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportDiscreteWithinDomain' := D₁.supportDiscreteWithinDomain.add
      D₂.supportDiscreteWithinDomain
  }

/-- Helper lemma for the `simp` tactic: the function of the sum of two divisors
is the sum of the associated functions. -/
@[simp]
lemma coe_add {D₁ D₂ : DivisorOn U} : (↑(D₁ + D₂) : 𝕜 → ℤ) = (D₁ : 𝕜 → ℤ) + (D₂ : 𝕜 → ℤ) := rfl

/-- Divisors have a negative -/
instance : Neg (DivisorOn U) where
  neg D := {
    toFun := -D
    supportWithinDomain' := by
      intro x hx
      rw [Function.support_neg', Function.mem_support, ne_eq] at hx
      exact D.supportWithinDomain hx
    supportDiscreteWithinDomain' := D.supportDiscreteWithinDomain.neg
  }

/-- Helper lemma for the `simp` tactic: the function of the negative divisor
is the negative of the associated function. -/
@[simp]
lemma neg_fun {D : DivisorOn U} : (↑(-D) : 𝕜 → ℤ) = -(D: 𝕜 → ℤ) := rfl

/-- Divisors have scalar multiplication with natural numbers -/
instance : SMul ℕ (DivisorOn U) where
  smul n D := {
    toFun := fun z ↦ n * D z
    supportWithinDomain' := by
      intro x hx
      simp at hx
      exact D.supportWithinDomain hx.2
    supportDiscreteWithinDomain' := by
      filter_upwards [D.supportDiscreteWithinDomain]
      intro x hx
      simp [hx]
  }

/-- Helper lemma for the `simp` tactic: the function of a scalar product
(natural number)·divisor is the scalar product of the natural number with the
associated function of the divisor. -/
@[simp]
lemma nsmul_fun {D : DivisorOn U} {n : ℕ} : (↑(n • D) : 𝕜 → ℤ) = n • (D : 𝕜 → ℤ) := rfl

/-- Divisors have scalar multiplication with integers -/
instance : SMul ℤ (DivisorOn U) where
  smul n D := {
    toFun := fun z ↦ n * D z
    supportWithinDomain' := by
      intro x hx
      simp at hx
      exact D.supportWithinDomain hx.2
    supportDiscreteWithinDomain' := by
      filter_upwards [D.supportDiscreteWithinDomain]
      intro _ hx
      simp [hx]
  }

/-- Helper lemma for the `simp` tactic: the function of a scalar product
(integer)·divisor is the scalar product of the integer with the associated
function of the divisor. -/
@[simp]
lemma zsmul_fun {D : DivisorOn U} {n : ℤ} : (↑(n • D) : 𝕜 → ℤ) = n • (D : 𝕜 → ℤ) := rfl

/-- Divisors have a partial ordering by pointwise comparison of the associated
functions. -/
instance : LE (DivisorOn U) where
  le := fun D₁ D₂ ↦ (D₁ : 𝕜 → ℤ) ≤ D₂

/-- Helper lemma for the `simp` tactic: a divisor is smaller than another one
if the same relation holds with the associated functions. -/
@[simp]
lemma le_def {D₁ D₂ : DivisorOn U} : D₁ ≤ D₂ ↔ (D₁ : 𝕜 → ℤ) ≤ (D₂ : 𝕜 → ℤ) := ⟨(·),(·)⟩

/-- Divisors form an ordered commutative group -/
instance : OrderedAddCommGroup (DivisorOn U) where
  add := (· + · )
  add_assoc := fun _ _ _ ↦ by ext; simp [add_assoc]
  zero := 0
  zero_add := fun _ ↦ by ext; simp
  add_zero := fun _ ↦ by ext; simp
  nsmul := (· • ·)
  neg := (- ·)
  zsmul := (· • ·)
  neg_add_cancel := fun _ ↦ by ext; simp

  add_comm := fun _ _ ↦ by ext; simp [add_comm]
  nsmul_zero := fun _ ↦ by ext; simp
  nsmul_succ := fun _ _ ↦ by ext; simp [add_one_mul]
  zsmul_zero' := fun _ ↦ by ext; simp
  zsmul_succ' := fun _ _ ↦ by ext; simp [add_one_mul]
  zsmul_neg' := fun _ _ ↦ by ext; simp; apply negSucc_zsmul
  le := (· ≤ ·)
  le_refl := by tauto
  le_trans := fun D₁ D₂ D₃ h₁₂ h₂₃ ↦ by simp only [le_def] at h₁₂ h₂₃; exact h₁₂.trans h₂₃
  le_antisymm := fun _ _ h₁₂ h₂₁ ↦ by ext x; exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  add_le_add_left := fun _ _ _ _ ↦ by simpa

/-- Divisors have a partial ordering by pointwise comparison of the associated
functions. -/
instance : LT (DivisorOn U) where
  lt := fun D₁ D₂ ↦ D₁.toFun < D₂.toFun

/-- Helper lemma for the `simp` tactic: a divisor is smaller than another one
if the same relation holds with the associated functions. -/
@[simp]
lemma lt_fun {D₁ D₂ : DivisorOn U} : D₁ < D₂ ↔ (D₁ : 𝕜 → ℤ) < (D₂ : 𝕜 → ℤ) := ⟨(·),(·)⟩

/-- Divisors have a max. -/
instance : Max (DivisorOn U) where
  max D₁ D₂ := {
    toFun := fun z ↦ max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        Function.nmem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportDiscreteWithinDomain' := by
      filter_upwards [D₁.supportDiscreteWithinDomain, D₂.supportDiscreteWithinDomain]
      intro _ h₁ h₂
      simp [h₁, h₂]
  }

/-- Helper lemma for the `simp` tactic: the function associated with the max of
two divisors is the pointwise max of the associated functions. -/
@[simp]
lemma max_fun {D₁ D₂ : DivisorOn U} {x : 𝕜} : max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

/-- Divisors have a min. -/
instance : Min (DivisorOn U) where
  min D₁ D₂ := {
    toFun := fun z ↦ min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        Function.nmem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportDiscreteWithinDomain' := by
      filter_upwards [D₁.supportDiscreteWithinDomain, D₂.supportDiscreteWithinDomain]
      intro _ h₁ h₂
      simp [h₁, h₂]
  }

/-- Helper lemma for the `simp` tactic: the function associated with the max of
two divisors is the pointwise max of the associated functions. -/
@[simp]
lemma min_fun {D₁ D₂ : DivisorOn U} {x : 𝕜} : min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

/-- Divisors form a lattice. -/
instance : Lattice (DivisorOn U) where
  le := (· ≤ ·)
  le_refl := by simp
  le_trans := by exact fun D₁ D₂ D₃ h₁₂ h₂₃ x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm := by
    intro D₁ D₂ h₁₂ h₂₁
    ext x
    exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  sup := (max · ·)
  le_sup_left := fun D₁ D₂ x ↦ by simp
  le_sup_right := fun D₁ D₂ x ↦ by simp
  sup_le := fun D₁ D₂ D₃ h₁₃ h₂₃ x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := (min · ·)
  inf_le_left := fun D₁ D₂ x ↦ by simp
  inf_le_right := fun D₁ D₂ x ↦ by simp
  le_inf := fun D₁ D₂ D₃ h₁₃ h₂₃ x ↦ by simp [h₁₃ x, h₂₃ x]

/-!
## Restriction
-/

/-- If `V` is a subset of `U`, then a divisor on `U` restricts to a divisor in `V` by
setting its values to zero outside of `V`. -/
noncomputable def restrict {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    DivisorOn V where
  toFun := by
    classical
    exact fun z ↦ if hz : z ∈ V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, Function.mem_support, ne_eq, ite_eq_right_iff,
      Classical.not_imp] at hx
    exact hx.1
  supportDiscreteWithinDomain' := by
    apply Filter.codiscreteWithin.mono h
    filter_upwards [D.supportDiscreteWithinDomain]
    intro x hx
    simp [hx]

open Classical in
lemma restrict_apply {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) (z : 𝕜) :
    (D.restrict h) z = if z ∈ V then D z else 0 := rfl

/-- Helper lemma for the `simp` tactic: restricting a divisor from `U` to a
subset `V` does not change its values on `V`. -/
@[simp]
lemma restrict_eqOn {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff]

/-- Helper lemma for the `simp` tactic: restricting a divisor from `U` to a
subset `V` makes it zero outside of `V`. -/
@[simp]
lemma restrict_eqOn_compl {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff, hx]

/-- Restriction as an order-preserving morphism -/
noncomputable def restrict_orderHom {V : Set 𝕜} (h : V ⊆ U) : DivisorOn U →o DivisorOn V where
  toFun := fun D ↦ D.restrict h
  monotone' := by
    intro D₁ D₂ h₁₂ x
    simp only [restrict_apply]
    split
    · apply h₁₂
    · exact le_rfl

/-- Helper lemma for the `simp` tactic: `restrict_orderHom` restricts divisors. -/
@[simp]
lemma restrict_orderHom_fun {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    restrict_orderHom h D = D.restrict h := by rfl

/-- Restriction as a group morphism -/
noncomputable def restrict_groupHom {V : Set 𝕜} (h : V ⊆ U) : DivisorOn U →+ DivisorOn V where
  toFun := fun D ↦ D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]

/-- Helper lemma for the `simp` tactic: `restrict_groupHom` restricts divisors. -/
@[simp]
lemma restrict_groupHom_fun {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    restrict_groupHom h D = D.restrict h := by rfl

/-- Restriction as a lattice morphism -/
noncomputable def restrict_latticeHom {V : Set 𝕜} (h : V ⊆ U) :
    LatticeHom (DivisorOn U) (DivisorOn V) where
  toFun := fun D ↦ D.restrict h
  map_sup' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [DivisorOn.restrict_apply, hx]
  map_inf' := by
    intro D₁ D₂
    ext x
    by_cases hx : x ∈ V
    <;> simp [DivisorOn.restrict_apply, hx]

/-- Helper lemma for the `simp` tactic: `restrict_latticeHom` restricts divisors. -/
@[simp]
lemma restrict_latticeHom_fun {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    restrict_latticeHom h D = D.restrict h := by rfl

/-!
## Derived invariants
-/

/-- The degree of a divisor on U is the sum of its values, or 0 if the support is infinite. -/
noncomputable def deg (D : DivisorOn U) : ℤ := ∑ᶠ z, D z

end DivisorOn

/-- The counting function for a divisor -/
noncomputable def Divisor.counting (D : Divisor 𝕜) : ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z

/-- The logarithmic counting function for a divisor -/
noncomputable def Divisor.logCounting (D : Divisor 𝕜) : ℝ → ℝ :=
  fun r ↦ ∑ᶠ z, D.restrict (by tauto : closedBall (0 : 𝕜) |r| ⊆ ⊤) z * (log r - log ‖z‖)
