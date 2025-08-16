/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Order.Pi
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.DiscreteSubset

/-!
# Type of functions with locally finite support

This file defines functions with locally finite support, provides supporting API. For suitable
targets, it establishes functions with locally finite support as an instance of a lattice ordered
commutative group.

Throughout the present file, `X` denotes a topologically space and `U` a subset of `X`.
-/

open Filter Function Set Topology

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A function with locally finite support within `U` is a function `X → Y` whose support is locally
finite within `U` and entirely contained in `U`.  For T1-spaces, the theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that the first condition is equivalent to the
condition that the support `f` is discrete within `U`.
-/

variable (U Y) in
/-- A function with locally finite support within `U` is a triple as specified below. -/
structure Function.locallyFinsuppWithin [Zero Y] where
  /-- A function `X → Y` -/
  toFun : X → Y
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support ⊆ U
  /-- A proof the the support is locally finite within `U` -/
  supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)

variable (X Y) in
/--
A function with locally finite support is a function with locally finite support within
`⊤ : Set X`.
-/
def Function.locallyFinsupp [Zero Y] := locallyFinsuppWithin (⊤ : Set X) Y

/--
For T1 spaces, the condition `supportLocallyFiniteWithinDomain'` is equivalent to saying that the
support is codiscrete within `U`.
-/
theorem supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X → Y}
    (h : f.support ⊆ U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support) := by
  have : f.support = (U \ {x | f x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, mem_diff, mem_setOf_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq, Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin, this]

lemma supportLocallyFiniteWithin_top_iff [Zero Y] (f : X → Y) :
    (∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)) ↔
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) := by
  have lem {α : Type u_1} (s t : Set α) : (s ∩ t) = {i : s | ↑i ∈ t} := by aesop
  constructor
  all_goals intro h z
            obtain ⟨t, ht⟩ := h z
            use t
            refine ⟨ht.1, ?_⟩
            have ans := ht.2
  · simp only [top_eq_univ, lem t f.support, mem_support, ne_eq, Subtype.coe_image,
              mem_setOf_eq, exists_prop, singleton_inter_nonempty] at ans ⊢
    have : {x | x ∈ t ∧ ¬f x = 0} =
            Subtype.val '' {i : { x // ¬f x = 0 } | ↑i ∈ t} := by aesop
    rw [this] at ans
    convert ans
    apply Equiv.set_finite_iff
    exact BijOn.equiv (Subtype.val) (InjOn.bijOn_image injOn_subtype_val)
  · simp only [singleton_inter_nonempty] at ans ⊢
    have : {i : f.support | ↑i ∈ t} = t ∩ f.support := by aesop
    rw [← this]
    exact Finite.image Subtype.val ans

lemma supportLocallyFiniteWithin_top_inter_compact_finite {W : Set X}
   [Zero Y] {f : X → Y} (hf : ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support))
   (hW : IsCompact W) : (W ∩ f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    ((supportLocallyFiniteWithin_top_iff f).mp hf) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

namespace Function.locallyFinsuppWithin

/--
Functions with locally finite support within `U` are `FunLike`: the coercion to functions is
injective.
-/
instance [Zero Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  coe D := D.toFun
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

/-- This allows writing `D.support` instead of `Function.support D` -/
abbrev support [Zero Y] (D : locallyFinsuppWithin U Y) := Function.support D

lemma supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    D.support ⊆ U := D.supportWithinDomain'

lemma supportLocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ D.support) := D.supportLocallyFiniteWithinDomain'

@[ext]
lemma ext [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : ∀ a, D₁ a = D₂ a) :
    D₁ = D₂ := DFunLike.ext _ _ h

lemma coe_injective [Zero Y] :
    Injective (· : locallyFinsuppWithin U Y → X → Y) := DFunLike.coe_injective

/-!
## Elementary properties of the support
-/

/--
Simplifier lemma: Functions with locally finite support within `U` evaluate to zero outside of `U`.
-/
@[simp]
lemma apply_eq_zero_of_notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y)
    (hz : z ∉ U) :
    D z = 0 := notMem_support.mp fun a ↦ hz (D.supportWithinDomain a)

@[deprecated (since := "2025-05-23")] alias apply_eq_zero_of_not_mem := apply_eq_zero_of_notMem

/--
On a T1 space, the support of a function with locally finite support within `U` is discrete within
`U`.
-/
theorem eq_zero_codiscreteWithin [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    D =ᶠ[Filter.codiscreteWithin U] 0 := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : D.support = (U \ {x | D x = (0 : X → Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_diff, Set.mem_setOf_eq, iff_and_self]
    exact (support_subset_iff.1 D.supportWithinDomain) x
  rw [← this]
  exact D.supportLocallyFiniteWithinDomain

/--
On a T1 space, the support of a functions with locally finite support within `U` is discrete.
-/
theorem discreteSupport [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    DiscreteTopology D.support := by
  have : D.support = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  rw [this]
  apply discreteTopology_of_codiscreteWithin
  apply (supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
  exact D.supportLocallyFiniteWithinDomain

/--
If `X` is T1 and if `U` is closed, then the support of support of a function with locally finite
support within `U` is also closed.
-/
theorem closedSupport [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsClosed U) :
    IsClosed D.support := by
  convert isClosed_sdiff_of_codiscreteWithin ((supportDiscreteWithin_iff_locallyFiniteWithin
    D.supportWithinDomain).2 D.supportLocallyFiniteWithinDomain) hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

/--
If `X` is T2 and if `U` is compact, then the support of a function with locally finite support
within `U` is finite.
-/
theorem finiteSupport [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsCompact U) :
    Set.Finite D.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

/-!
## Lattice ordered group structure

If `X` is a suitable instance, this section equips functions with locally finite support within `U`
with the standard structure of a lattice ordered group, where addition, comparison, min and max are
defined pointwise.
-/

variable (U) in
/--
Functions with locally finite support within `U` form an additive subgroup of functions X → Y.
-/
protected def addSubgroup [AddCommGroup Y] : AddSubgroup (X → Y) where
  carrier := {f | f.support ⊆ U ∧ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_setOf_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      true_and]
    exact fun _ _ ↦ ⟨⊤, univ_mem⟩
  add_mem' {f g} hf hg := by
    constructor
    · intro x hx
      contrapose! hx
      simp [notMem_support.1 fun a ↦ hx (hf.1 a), notMem_support.1 fun a ↦ hx (hg.1 a)]
    · intro z hz
      obtain ⟨t₁, ht₁⟩ := hf.2 z hz
      obtain ⟨t₂, ht₂⟩ := hg.2 z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ f.support) ∪ (t₂ ∩ g.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [support_subset_iff, ne_eq, mem_setOf_eq,
        mem_inter_iff, mem_support, Pi.add_apply, mem_union, true_and]
      by_contra hCon
      push_neg at hCon
      simp_all
  neg_mem' {f} hf := by
    simp_all

protected lemma memAddSubgroup [AddCommGroup Y] (D : locallyFinsuppWithin U Y) :
    (D : X → Y) ∈ locallyFinsuppWithin.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
def mk_of_mem [AddCommGroup Y] (f : X → Y) (hf : f ∈ locallyFinsuppWithin.addSubgroup U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

instance [AddCommGroup Y] : Zero (locallyFinsuppWithin U Y) where
  zero := mk_of_mem 0 <| zero_mem _

instance [AddCommGroup Y] : Add (locallyFinsuppWithin U Y) where
  add D₁ D₂ := mk_of_mem (D₁ + D₂) <| add_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance [AddCommGroup Y] : Neg (locallyFinsuppWithin U Y) where
  neg D := mk_of_mem (-D) <| neg_mem D.memAddSubgroup

instance [AddCommGroup Y] : Sub (locallyFinsuppWithin U Y) where
  sub D₁ D₂ := mk_of_mem (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance [AddCommGroup Y] : SMul ℕ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem (n • D) <| nsmul_mem D.memAddSubgroup n

instance [AddCommGroup Y] : SMul ℤ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem (n • D) <| zsmul_mem D.memAddSubgroup n

@[simp] lemma coe_zero [AddCommGroup Y] :
    ((0 : locallyFinsuppWithin U Y) : X → Y) = 0 := rfl
@[simp] lemma coe_add [AddCommGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ + D₂) : X → Y) = D₁ + D₂ := rfl
@[simp] lemma coe_neg [AddCommGroup Y] (D : locallyFinsuppWithin U Y) :
    (↑(-D) : X → Y) = -(D : X → Y) := rfl
@[simp] lemma coe_sub [AddCommGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ - D₂) : X → Y) = D₁ - D₂ := rfl
@[simp] lemma coe_nsmul [AddCommGroup Y] (D : locallyFinsuppWithin U Y) (n : ℕ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl
@[simp] lemma coe_zsmul [AddCommGroup Y] (D : locallyFinsuppWithin U Y) (n : ℤ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl

instance [AddCommGroup Y] : AddCommGroup (locallyFinsuppWithin U Y) :=
  Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance [LE Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  le := fun D₁ D₂ ↦ (D₁ : X → Y) ≤ D₂

lemma le_def [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ ≤ D₂ ↔ (D₁ : X → Y) ≤ (D₂ : X → Y) := ⟨(·),(·)⟩

instance [Preorder Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  lt := fun D₁ D₂ ↦ (D₁ : X → Y) < D₂

lemma lt_def [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ < D₂ ↔ (D₁ : X → Y) < (D₂ : X → Y) := ⟨(·),(·)⟩

instance [SemilatticeSup Y] [Zero Y] : Max (locallyFinsuppWithin U Y) where
  max D₁ D₂ :=
  { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ D₁.support) ∪ (t₂ ∩ D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra hCon
      push_neg at hCon
      simp_all }

@[simp]
lemma max_apply [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

instance [SemilatticeInf Y] [Zero Y] : Min (locallyFinsuppWithin U Y) where
  min D₁ D₂ :=
  { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a ↦ hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a ↦ hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ D₁.support) ∪ (t₂ ∩ D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra hCon
      push_neg at hCon
      simp_all }

@[simp]
lemma min_apply [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

instance [Lattice Y] [Zero Y] : Lattice (locallyFinsuppWithin U Y) where
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

/--
Functions with locally finite support within `U` form an ordered commutative group.
-/
instance [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y] :
    IsOrderedAddMonoid (locallyFinsuppWithin U Y) where
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]

/-!
## Restriction
-/

/--
If `V` is a subset of `U`, then functions with locally finite support within `U` restrict to
functions with locally finite support within `V`, by setting their values to zero outside of `V`.
-/
noncomputable def restrict [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    locallyFinsuppWithin V Y where
  toFun := by
    classical
    exact fun z ↦ if hz : z ∈ V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    exact hx.1
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supportLocallyFiniteWithinDomain z (h hz)
    use t, ht.1
    apply Set.Finite.subset (s := t ∩ D.support) ht.2
    intro _ _
    simp_all

open Classical in
lemma restrict_apply [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) (z : X) :
    (D.restrict h) z = if z ∈ V then D z else 0 := rfl

lemma restrict_eqOn [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply]

lemma restrict_eqOn_compl [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all

/-- Restriction as a group morphism -/
noncomputable def restrictMonoidHom [AddCommGroup Y] {V : Set X} (h : V ⊆ U) :
    locallyFinsuppWithin U Y →+ locallyFinsuppWithin V Y where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [restrict_apply, hx]

@[simp]
lemma restrictMonoidHom_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y)
    (h : V ⊆ U) :
    restrictMonoidHom h D = D.restrict h := by rfl

/-- Restriction as a lattice morphism -/
noncomputable def restrictLatticeHom [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V ⊆ U) :
    LatticeHom (locallyFinsuppWithin U Y) (locallyFinsuppWithin V Y) where
  toFun D := D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x ∈ V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]

@[simp]
lemma restrictLatticeHom_apply [AddCommGroup Y] [Lattice Y] {V : Set X}
    (D : locallyFinsuppWithin U Y) (h : V ⊆ U) :
    restrictLatticeHom h D = D.restrict h := by rfl

end Function.locallyFinsuppWithin
