/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

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

@[ext]
lemma ext {D₁ D₂ : DivisorOn U} (h : ∀ a, D₁ a = D₂ a) : D₁ = D₂ := DFunLike.ext _ _ h

lemma coe_injective : Function.Injective (· : DivisorOn U → 𝕜 → ℤ) := DFunLike.coe_injective

/-!
## Elementary properties of the support
-/

/-- Simplifier lemma: A divisor on `U` evaluates to zero outside of `U`. -/
@[simp]
lemma apply_eq_zero_of_not_mem {z : 𝕜} (D : DivisorOn U) (hz : z ∉ U) :
    D z = 0 := Function.nmem_support.mp fun a ↦ hz (D.supportWithinDomain a)

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
  convert isClosed_sdiff_of_codiscreteWithin D.supportDiscreteWithinDomain hU
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

variable (U) in
/-- Divisors form an additive subgroup of functions 𝕜 → ℤ -/
protected def addSubgroup : AddSubgroup (𝕜 → ℤ) where
  carrier := {f | f.support ⊆ U ∧ f =ᶠ[codiscreteWithin U] 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    refine ⟨?_, hf.2.add hg.2⟩
    intro x hx
    contrapose! hx
    simp [Function.nmem_support.1 fun a ↦ hx (hf.1 a),
      Function.nmem_support.1 fun a ↦ hx (hg.1 a)]
  neg_mem' {f} hf := ⟨fun x hx ↦ hf.1 <| by simpa using hx, hf.2.neg⟩

protected lemma memAddSubgroup (D : DivisorOn U) :
    (D : 𝕜 → ℤ) ∈ DivisorOn.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportDiscreteWithinDomain⟩

/-- Assign a divisor to a function in the subgroup -/
@[simps]
def mk_of_mem (f : 𝕜 → ℤ) (hf : f ∈ DivisorOn.addSubgroup U) : DivisorOn U :=
  ⟨f, hf.1, hf.2⟩

instance : Zero (DivisorOn U) where
  zero := mk_of_mem 0 <| zero_mem _

instance : Add (DivisorOn U) where
  add D₁ D₂ := mk_of_mem (D₁ + D₂) <| add_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance : Neg (DivisorOn U) where
  neg D := mk_of_mem (-D) <| neg_mem D.memAddSubgroup

instance : Sub (DivisorOn U) where
  sub D₁ D₂ := mk_of_mem (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance : SMul ℕ (DivisorOn U) where
  smul n D := mk_of_mem (n • D) <| nsmul_mem D.memAddSubgroup n

instance : SMul ℤ (DivisorOn U) where
  smul n D := mk_of_mem (n • D) <| zsmul_mem D.memAddSubgroup n

@[simp] lemma coe_zero : ((0 : DivisorOn U) : 𝕜 → ℤ) = 0 := rfl
@[simp] lemma coe_add (D₁ D₂ : DivisorOn U) : (↑(D₁ + D₂) : 𝕜 → ℤ) = D₁ + D₂ := rfl
@[simp] lemma coe_neg (D : DivisorOn U) : (↑(-D) : 𝕜 → ℤ) = -(D : 𝕜 → ℤ) := rfl
@[simp] lemma coe_sub (D₁ D₂ : DivisorOn U) : (↑(D₁ - D₂) : 𝕜 → ℤ) = D₁ - D₂ := rfl
@[simp] lemma coe_nsmul (D : DivisorOn U) (n : ℕ) : (↑(n • D) : 𝕜 → ℤ) = n • (D : 𝕜 → ℤ) := rfl
@[simp] lemma coe_zsmul (D : DivisorOn U) (n : ℤ) : (↑(n • D) : 𝕜 → ℤ) = n • (D : 𝕜 → ℤ) := rfl

instance : AddCommGroup (DivisorOn U) :=
  Function.Injective.addCommGroup (M₁ := DivisorOn U) (M₂ := 𝕜 → ℤ)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance : LE (DivisorOn U) where
  le := fun D₁ D₂ ↦ (D₁ : 𝕜 → ℤ) ≤ D₂

lemma le_def {D₁ D₂ : DivisorOn U} : D₁ ≤ D₂ ↔ (D₁ : 𝕜 → ℤ) ≤ (D₂ : 𝕜 → ℤ) := ⟨(·),(·)⟩

instance : LT (DivisorOn U) where
  lt := fun D₁ D₂ ↦ (D₁ : 𝕜 → ℤ) < D₂

lemma lt_def {D₁ D₂ : DivisorOn U} : D₁ < D₂ ↔ (D₁ : 𝕜 → ℤ) < (D₂ : 𝕜 → ℤ) := ⟨(·),(·)⟩

instance : Max (DivisorOn U) where
  max D₁ D₂ :=
  { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        Function.nmem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportDiscreteWithinDomain' := by
      filter_upwards [D₁.supportDiscreteWithinDomain, D₂.supportDiscreteWithinDomain]
      intro _ h₁ h₂
      simp [h₁, h₂] }

@[simp]
lemma max_apply {D₁ D₂ : DivisorOn U} {x : 𝕜} : max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

instance : Min (DivisorOn U) where
  min D₁ D₂ :=
  { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [Function.nmem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        Function.nmem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportDiscreteWithinDomain' := by
      filter_upwards [D₁.supportDiscreteWithinDomain, D₂.supportDiscreteWithinDomain]
      intro _ h₁ h₂
      simp [h₁, h₂] }

@[simp]
lemma min_def {D₁ D₂ : DivisorOn U} {x : 𝕜} : min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

instance : Lattice (DivisorOn U) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact Int.le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x ↦ by simp
  le_sup_right D₁ D₂ := fun x ↦ by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := min
  inf_le_left D₁ D₂ := fun x ↦ by simp
  inf_le_right D₁ D₂ := fun x ↦ by simp
  le_inf D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]

/-- Divisors form an ordered commutative group -/
instance : OrderedAddCommGroup (DivisorOn U) where
  __ := inferInstanceAs (AddCommGroup (DivisorOn U))
  __ := inferInstanceAs (Lattice (DivisorOn U))
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]

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

lemma restrict_eqOn {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff]

lemma restrict_eqOn_compl {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff, hx]

/-- Restriction as a group morphism -/
noncomputable def restrictMonoidHom {V : Set 𝕜} (h : V ⊆ U) : DivisorOn U →+ DivisorOn V where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]

@[simp]
lemma restrictMonoidHom_apply {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    restrictMonoidHom h D = D.restrict h := by rfl

/-- Restriction as a lattice morphism -/
noncomputable def restrictLatticeHom {V : Set 𝕜} (h : V ⊆ U) :
    LatticeHom (DivisorOn U) (DivisorOn V) where
  toFun D := D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [DivisorOn.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [DivisorOn.restrict_apply, hx]

@[simp]
lemma restrictLatticeHom_apply {V : Set 𝕜} (D : DivisorOn U) (h : V ⊆ U) :
    restrictLatticeHom h D = D.restrict h := by rfl

end DivisorOn
