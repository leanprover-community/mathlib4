/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Divisors on subsets of normed fields

This file defines divisors, a standard book-keeping tool in complex analysis
used to keep track of pole/vanishing orders of meromorphic objects, typically
functions or differential forms. It provides supporting API and establishes
divisors as an instance of a lattice ordered commutative group.

Throughout the present file, `X` denotes a nontrivially normed field, and `U` a
subset of `X`.

## TODOs

- Constructions: The divisor of a meromorphic function, behavior under product
  of meromorphic functions, behavior under addition, behavior under restriction
- Construction: The divisor of a rational polynomial
-/

open Filter Metric Real Set Topology

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A divisor on `U` is a function `X → Y` whose support is discrete within `U` and
entirely contained within `U`.  The theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that this is equivalent to
the textbook definition, which requires the support of `f` to be locally finite
within `U`.
-/

variable (U Y) in
/-- A divisor on `U` is a triple specified below. -/
structure Function.discretesuppWithin [Zero Y] where
  /-- A function `X → Y` -/
  toFun : X → Y
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support ⊆ U
  /-- A proof the the support is discrete within `U` -/
  supportDiscreteWithinDomain' : toFun =ᶠ[codiscreteWithin U] 0

variable (X Y) in
/-- A divisor is a divisor on `⊤ : Set X`. -/
def Function.discretesupp [Zero Y] :=
  Function.discretesuppWithin (⊤ : Set X) Y

/-- The condition `supportDiscreteWithinU` in a divisor is equivalent to saying
that the support is locally finite near every point of `U`. -/
theorem supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X → Y}
    (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : X → Y) x}) := by
    ext x
    simp only [Function.mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

namespace Function.discretesuppWithin

/-- Divisors are `FunLike`: the coercion from divisors to functions is injective. -/
instance [Zero Y] : FunLike (Function.discretesuppWithin U Y) X Y where
  coe D := D.toFun
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

/-- This allows writing `D.support` instead of `Function.support D` -/
abbrev support [Zero Y] (D : Function.discretesuppWithin U Y) := Function.support D

lemma supportWithinDomain [Zero Y] (D : Function.discretesuppWithin U Y) :
    D.support ⊆ U := D.supportWithinDomain'

lemma supportDiscreteWithinDomain [Zero Y] (D : Function.discretesuppWithin U Y) :
    D =ᶠ[codiscreteWithin U] 0 := D.supportDiscreteWithinDomain'

@[ext]
lemma ext [Zero Y] {D₁ D₂ : Function.discretesuppWithin U Y} (h : ∀ a, D₁ a = D₂ a) :
    D₁ = D₂ := DFunLike.ext _ _ h

lemma coe_injective [Zero Y] :
    Function.Injective (· : Function.discretesuppWithin U Y → X → Y) := DFunLike.coe_injective

/-!
## Elementary properties of the support
-/

/-- Simplifier lemma: A divisor on `U` evaluates to zero outside of `U`. -/
@[simp]
lemma apply_eq_zero_of_not_mem [Zero Y] {z : X} (D : Function.discretesuppWithin U Y) (hz : z ∉ U) :
    D z = 0 := Function.nmem_support.mp fun a ↦ hz (D.supportWithinDomain a)

/-- The support of a divisor is discrete. -/
theorem discreteSupport [Zero Y] (D : Function.discretesuppWithin U Y) :
    DiscreteTopology D.support := by
  have : Function.support D = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  convert discreteTopology_of_codiscreteWithin (D.supportDiscreteWithinDomain)

/-- If `U` is closed, the the support of a divisor on `U` is also closed. -/
theorem closedSupport [Zero Y] (D : Function.discretesuppWithin U Y) (hU : IsClosed U) :
    IsClosed D.support := by
  convert isClosed_sdiff_of_codiscreteWithin D.supportDiscreteWithinDomain hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

/-- If `U` is closed, the the support of a divisor on `U` is finite. -/
theorem finiteSupport [T2Space X] [Zero Y] (D : Function.discretesuppWithin U Y)
    (hU : IsCompact U) :
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
/-- Divisors form an additive subgroup of functions X → Y -/
protected def addSubgroup [AddCommGroup Y] : AddSubgroup (X → Y) where
  carrier := {f | f.support ⊆ U ∧ f =ᶠ[codiscreteWithin U] 0}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    constructor
    · intro x hx
      contrapose! hx
      simp [Function.nmem_support.1 fun a ↦ hx (hf.1 a),
        Function.nmem_support.1 fun a ↦ hx (hg.1 a)]
    · filter_upwards [hf.2.add hg.2] with a ha
      simp [ha]
  neg_mem' {f} hf := by
    have : -f =ᶠ[codiscreteWithin U] 0 := by simpa using hf.2.neg
    simp_all

protected lemma memAddSubgroup  [AddCommGroup Y] (D : Function.discretesuppWithin U Y) :
    (D : X → Y) ∈ Function.discretesuppWithin.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportDiscreteWithinDomain⟩

/-- Assign a divisor to a function in the subgroup -/
@[simps]
def mk_of_mem [AddCommGroup Y] (f : X → Y) (hf : f ∈ Function.discretesuppWithin.addSubgroup U) :
    Function.discretesuppWithin U Y := ⟨f, hf.1, hf.2⟩

instance [AddCommGroup Y] : Zero (Function.discretesuppWithin U Y) where
  zero := mk_of_mem 0 <| zero_mem _

instance [AddCommGroup Y]: Add (Function.discretesuppWithin U Y) where
  add D₁ D₂ := mk_of_mem (D₁ + D₂) <| add_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance [AddCommGroup Y] : Neg (Function.discretesuppWithin U Y) where
  neg D := mk_of_mem (-D) <| neg_mem D.memAddSubgroup

instance [AddCommGroup Y] : Sub (Function.discretesuppWithin U Y) where
  sub D₁ D₂ := mk_of_mem (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance [AddCommGroup Y] : SMul ℕ (Function.discretesuppWithin U Y) where
  smul n D := mk_of_mem (n • D) <| nsmul_mem D.memAddSubgroup n

instance [AddCommGroup Y] : SMul ℤ (Function.discretesuppWithin U Y) where
  smul n D := mk_of_mem (n • D) <| zsmul_mem D.memAddSubgroup n

@[simp] lemma coe_zero [AddCommGroup Y] :
    ((0 : Function.discretesuppWithin U Y) : X → Y) = 0 := rfl
@[simp] lemma coe_add [AddCommGroup Y] (D₁ D₂ : Function.discretesuppWithin U Y) :
    (↑(D₁ + D₂) : X → Y) = D₁ + D₂ := rfl
@[simp] lemma coe_neg [AddCommGroup Y] (D : Function.discretesuppWithin U Y) :
    (↑(-D) : X → Y) = -(D : X → Y) := rfl
@[simp] lemma coe_sub [AddCommGroup Y] (D₁ D₂ : Function.discretesuppWithin U Y) :
    (↑(D₁ - D₂) : X → Y) = D₁ - D₂ := rfl
@[simp] lemma coe_nsmul [AddCommGroup Y] (D : Function.discretesuppWithin U Y) (n : ℕ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl
@[simp] lemma coe_zsmul [AddCommGroup Y] (D : Function.discretesuppWithin U Y) (n : ℤ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl

instance [AddCommGroup Y] : AddCommGroup (Function.discretesuppWithin U Y) :=
  Function.Injective.addCommGroup (M₁ := Function.discretesuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance [LE Y] [Zero Y] : LE (Function.discretesuppWithin U Y) where
  le := fun D₁ D₂ ↦ (D₁ : X → Y) ≤ D₂

lemma le_def [LE Y] [Zero Y] {D₁ D₂ : Function.discretesuppWithin U Y} :
    D₁ ≤ D₂ ↔ (D₁ : X → Y) ≤ (D₂ : X → Y) := ⟨(·),(·)⟩

instance [Preorder Y] [Zero Y] : LT (Function.discretesuppWithin U Y) where
  lt := fun D₁ D₂ ↦ (D₁ : X → Y) < D₂

lemma lt_def [Preorder Y] [Zero Y] {D₁ D₂ : Function.discretesuppWithin U Y} :
    D₁ < D₂ ↔ (D₁ : X → Y) < (D₂ : X → Y) := ⟨(·),(·)⟩

instance [Lattice Y] [Zero Y] : Max (Function.discretesuppWithin U Y) where
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
lemma max_apply [Lattice Y] [Zero Y] {D₁ D₂ : Function.discretesuppWithin U Y} {x : X} :
    max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

instance [Lattice Y] [Zero Y] : Min (Function.discretesuppWithin U Y) where
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
lemma min_apply [Lattice Y] [Zero Y] {D₁ D₂ : Function.discretesuppWithin U Y} {x : X} :
    min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

instance  [Lattice Y] [Zero Y] : Lattice (Function.discretesuppWithin U Y) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x ↦ (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x ↦ by simp
  le_sup_right D₁ D₂ := fun x ↦ by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]
  inf := min
  inf_le_left D₁ D₂ := fun x ↦ by simp
  inf_le_right D₁ D₂ := fun x ↦ by simp
  le_inf D₁ D₂ D₃ h₁₃ h₂₃ := fun x ↦ by simp [h₁₃ x, h₂₃ x]

/-- Divisors form an ordered commutative group -/
instance  [LinearOrderedAddCommGroup Y] :
    OrderedAddCommGroup (Function.discretesuppWithin U Y) where
  __ := inferInstanceAs (AddCommGroup (Function.discretesuppWithin U Y))
  __ := inferInstanceAs (Lattice (Function.discretesuppWithin U Y))
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]

/-!
## Restriction
-/

/-- If `V` is a subset of `U`, then a divisor on `U` restricts to a divisor in `V` by
setting its values to zero outside of `V`. -/
noncomputable def restrict [Zero Y] {V : Set X} (D : Function.discretesuppWithin U Y) (h : V ⊆ U) :
    Function.discretesuppWithin V Y where
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
lemma restrict_apply [Zero Y] {V : Set X} (D : Function.discretesuppWithin U Y) (h : V ⊆ U)
    (z : X) :
    (D.restrict h) z = if z ∈ V then D z else 0 := rfl

lemma restrict_eqOn [Zero Y] {V : Set X} (D : Function.discretesuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff]

lemma restrict_eqOn_compl [Zero Y] {V : Set X} (D : Function.discretesuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all [restrict_apply, dite_eq_ite, ite_eq_left_iff, hx]

/-- Restriction as a group morphism -/
noncomputable def restrictMonoidHom [AddCommGroup Y] {V : Set X} (h : V ⊆ U) :
    Function.discretesuppWithin U Y →+ Function.discretesuppWithin V Y where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]

@[simp]
lemma restrictMonoidHom_apply [AddCommGroup Y] {V : Set X} (D : Function.discretesuppWithin U Y)
    (h : V ⊆ U) :
    restrictMonoidHom h D = D.restrict h := by rfl

/-- Restriction as a lattice morphism -/
noncomputable def restrictLatticeHom [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V ⊆ U) :
    LatticeHom (Function.discretesuppWithin U Y) (Function.discretesuppWithin V Y) where
  toFun D := D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [Function.discretesuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [Function.discretesuppWithin.restrict_apply, hx]

@[simp]
lemma restrictLatticeHom_apply [AddCommGroup Y] [Lattice Y] {V : Set X}
    (D : Function.discretesuppWithin U Y) (h : V ⊆ U) :
    restrictLatticeHom h D = D.restrict h := by rfl

end Function.discretesuppWithin
