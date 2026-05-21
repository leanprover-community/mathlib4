/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.Peel

/-!
# Type of functions with locally finite support

This file defines functions with locally finite support, provides supporting API. For suitable
targets, it establishes functions with locally finite support as an instance of a lattice ordered
commutative group.

Throughout the present file, `X` denotes a topologically space and `U` a subset of `X`.
-/

@[expose] public section

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
  /-- A proof that the support is locally finite within `U` -/
  supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)

variable (X Y) in
/--
A function with locally finite support is a function with locally finite support within
`⊤ : Set X`.
-/
abbrev Function.locallyFinsupp [Zero Y] := locallyFinsuppWithin (Set.univ : Set X) Y

/--
Function with locally finite support have a zero.
-/
instance [Zero Y] : Zero (locallyFinsuppWithin U Y) where
  zero :=
    { toFun := fun _ ↦ 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' z hz := by
        simp_rw [support_fun_zero, inter_empty, finite_empty, and_true]
        use Set.univ, univ_mem }

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

/--
A function `f : X → Y` has locally finite support if for every `z : X`, there is a
neighbourhood `t` around `z` such that `t ∩ f.support` is finite.
-/
def LocallyFiniteSupport [Zero Y] (f : X → Y) : Prop :=
  ∀ z : X, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)

lemma LocallyFiniteSupport.iff_locallyFinite_support [Zero Y] (f : X → Y) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) ↔ LocallyFiniteSupport f := by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t ∩ f.support = {i : f.support | ↑i ∈ t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i ∈ t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]

lemma LocallyFiniteSupport.locallyFinite_support [Zero Y] (f : X → Y) (h : LocallyFiniteSupport f) :
    LocallyFinite (fun s : f.support ↦ ({s.val} : Set X)) :=
  (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h

lemma LocallyFiniteSupport.finite_inter_support_of_isCompact {W : Set X}
   [Zero Y] {f : X → Y} (h : LocallyFiniteSupport f)
   (hW : IsCompact W) : (W ∩ f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} ∩ t).Nonempty} = (t ∩ s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

lemma Function.locallyFinsupp.locallyFiniteSupport [Zero Y] (f : locallyFinsupp X Y) :
    LocallyFiniteSupport f.toFun :=
  (f.supportLocallyFiniteWithinDomain' · (by trivial))

namespace Function.locallyFinsuppWithin

/--
Functions with locally finite support within `U` are `FunLike`: the coercion to functions is
injective.
-/
instance [Zero Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  coe D := D.toFun
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ ↦ by simp

@[simp]
lemma toFun_eq_coe [Zero Y] (c : locallyFinsuppWithin U Y) : c.toFun = ⇑c := rfl

@[simp]
lemma coe_mk [Zero Y] (f : X → Y) (h : f.support ⊆ U)
    (h' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)) :
    ⇑(Function.locallyFinsuppWithin.mk f h h') = f := rfl

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
## Singleton Indicators as Functions with Locally Finite Support
-/

/--
Is analogy to `Finsupp.single`, this definition presents the indicator function
of a single point as a function with locally finite support.
-/
noncomputable def single [DecidableEq X] [Zero Y] (x : X) (y : Y) : locallyFinsupp X Y where
  toFun := Pi.single x y
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, univ_mem, by simpa using (finite_singleton x).subset Pi.support_single_subset⟩

/--
Simplifier lemma: `single x y` takes the value `y` at `x` and is zero otherwise.
-/
@[simp] lemma single_apply [DecidableEq X] [Zero Y] {x₁ x₂ : X} {y : Y} :
    single x₁ y x₂ = if x₂ = x₁ then y else 0 := by
  classical
  simp_rw [DFunLike.coe, single, Pi.single_apply]

/--
Simplifier lemma: `single x 0` is zero.
-/
@[simp] lemma single_zero [DecidableEq X] [Zero Y] {x : X} :
    single x (0 : Y) = 0 := by aesop

/--
Simplifier lemma: coercion of `single x y` to a function.
-/
@[simp] lemma coe_single [DecidableEq X] [Zero Y] {x : X} {y : Y} :
    (single x y : X → Y) = Pi.single x y := by
  ext
  simp [Pi.single_apply]

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
On a T1 space, the support of a function with locally finite support within `U` is discrete.
-/
theorem discreteSupport [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    IsDiscrete D.support := by
  have : D.support = {x | D x = 0}ᶜ ∩ U := by
    ext x
    constructor
    · exact fun hx ↦ ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff, mem_compl_iff, mem_setOf_eq] at hx
      tauto
  rw [this]
  apply isDiscrete_of_codiscreteWithin
  rw [compl_compl]
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
Functions with locally finite support within `U` form an additive submonoid of functions `X → Y`.
-/
protected def addSubmonoid [AddMonoid Y] : AddSubmonoid (X → Y) where
  carrier := {f | f.support ⊆ U ∧ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_setOf_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      true_and]
    exact fun _ _ ↦ ⟨⊤, univ_mem⟩
  add_mem' {f g} hf hg := by
    constructor
    · intro x hx
      contrapose hx
      simp [notMem_support.1 fun a ↦ hx (hf.1 a), notMem_support.1 fun a ↦ hx (hg.1 a)]
    · intro z hz
      obtain ⟨t₁, ht₁⟩ := hf.2 z hz
      obtain ⟨t₂, ht₂⟩ := hg.2 z hz
      use t₁ ∩ t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ ∩ f.support) ∪ (t₂ ∩ g.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [support_subset_iff, ne_eq, mem_setOf_eq,
        mem_inter_iff, mem_support, Pi.add_apply, mem_union, true_and]
      by_contra! hCon
      simp_all

protected lemma memAddSubmonoid [AddMonoid Y] (D : locallyFinsuppWithin U Y) :
    (D : X → Y) ∈ locallyFinsuppWithin.addSubmonoid U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

variable (U) in
/--
Functions with locally finite support within `U` form an additive subgroup of functions `X → Y`.
-/
protected def addSubgroup [AddGroup Y] : AddSubgroup (X → Y) where
  carrier := {f | f.support ⊆ U ∧ ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ f.support)}
  __ := locallyFinsuppWithin.addSubmonoid U
  neg_mem' {f} hf := by simp_all

protected lemma memAddSubgroup [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (D : X → Y) ∈ locallyFinsuppWithin.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
def mk_of_mem_addSubmonoid [AddMonoid Y] (f : X → Y)
    (hf : f ∈ locallyFinsuppWithin.addSubmonoid U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

instance [AddMonoid Y] : Zero (locallyFinsuppWithin U Y) where
  zero := mk_of_mem_addSubmonoid 0 <| zero_mem _

instance [AddMonoid Y] : Add (locallyFinsuppWithin U Y) where
  add D₁ D₂ := mk_of_mem_addSubmonoid (D₁ + D₂) <| add_mem D₁.memAddSubmonoid D₂.memAddSubmonoid

instance [AddMonoid Y] : SMul ℕ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem_addSubmonoid (n • D) <| nsmul_mem D.memAddSubmonoid n

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
def mk_of_mem_addSubgroup [AddGroup Y] (f : X → Y) (hf : f ∈ locallyFinsuppWithin.addSubgroup U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

@[deprecated (since := "2026-03-06")] alias mk_of_mem := mk_of_mem_addSubgroup

instance [AddGroup Y] : Neg (locallyFinsuppWithin U Y) where
  neg D := mk_of_mem_addSubgroup (-D) <| neg_mem D.memAddSubgroup

instance [AddGroup Y] : Sub (locallyFinsuppWithin U Y) where
  sub D₁ D₂ := mk_of_mem_addSubgroup (D₁ - D₂) <| sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

instance [AddGroup Y] : SMul ℤ (locallyFinsuppWithin U Y) where
  smul n D := mk_of_mem_addSubgroup (n • D) <| zsmul_mem D.memAddSubgroup n

@[simp] lemma coe_zero [AddMonoid Y] :
    ((0 : locallyFinsuppWithin U Y) : X → Y) = 0 := rfl
@[simp] lemma coe_add [AddMonoid Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ + D₂) : X → Y) = D₁ + D₂ := rfl
@[simp] lemma coe_neg [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (↑(-D) : X → Y) = -(D : X → Y) := rfl
@[simp] lemma coe_sub [AddGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ - D₂) : X → Y) = D₁ - D₂ := rfl
@[simp] lemma coe_nsmul [AddMonoid Y] (D : locallyFinsuppWithin U Y) (n : ℕ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl
@[simp] lemma coe_zsmul [AddGroup Y] (D : locallyFinsuppWithin U Y) (n : ℤ) :
    (↑(n • D) : X → Y) = n • (D : X → Y) := rfl

instance [AddMonoid Y] : AddMonoid (locallyFinsuppWithin U Y) :=
  Injective.addMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_nsmul

instance [AddCommMonoid Y] : AddCommMonoid (locallyFinsuppWithin U Y) :=
  Injective.addCommMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_nsmul

@[simp] lemma coe_sum [AddCommMonoid Y] {ι : Type*} {s : Finset ι}
    {F : ι → locallyFinsuppWithin U Y} :
    (↑(∑ n ∈ s, F n) : X → Y) = ∑ n ∈ s, (F n : X → Y) := by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all

@[simp] lemma coe_finsum {ι : Type*} {F : ι → locallyFinsuppWithin U ℤ} :
    (↑(∑ᶠ i, F i) : X → ℤ) = ∑ᶠ i, (F i : X → ℤ) := by
  have : F.support = (fun i ↦ (F i : X → ℤ)).support := by
    simp [Set.ext_iff, DFunLike.ext_iff, funext_iff]
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i ↦ (F i : X → ℤ)).support.Finite := by simp_all
    simp_all [finsum_eq_sum _ h₂]
  · simp_all [finsum_of_infinite_support]

instance [AddGroup Y] : AddGroup (locallyFinsuppWithin U Y) :=
  Injective.addGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance [AddCommGroup Y] : AddCommGroup (locallyFinsuppWithin U Y) :=
  Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X → Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance [LE Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  le := fun D₁ D₂ ↦ (D₁ : X → Y) ≤ D₂

lemma le_def [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ ≤ D₂ ↔ (D₁ : X → Y) ≤ (D₂ : X → Y) := ⟨(·),(·)⟩

lemma single_nonneg [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 ≤ single x y ↔ 0 ≤ y := by
  simp only [le_def, coe_single]
  apply Pi.single_nonneg

instance [Preorder Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  lt := fun D₁ D₂ ↦ (D₁ : X → Y) < D₂

lemma lt_def [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ < D₂ ↔ (D₁ : X → Y) < (D₂ : X → Y) := ⟨(·),(·)⟩

lemma single_pos [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 < single x y ↔ 0 < y := by
  rw [lt_def, coe_single]
  exact Pi.single_pos

@[simp] lemma single_pos_nat_one [DecidableEq X] {x : X} :
    0 < single x 1 := single_pos.2 Nat.one_pos

@[simp] lemma single_pos_int_one [DecidableEq X] {x : X} :
    0 < single x (1 : ℤ) := single_pos.2 Int.one_pos

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
      by_contra! hCon
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
      by_contra! hCon
      simp_all }

@[simp]
lemma min_apply [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

section Lattice
variable [Lattice Y]

instance [Zero Y] : Lattice (locallyFinsuppWithin U Y) where
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

variable [AddCommGroup Y]

@[simp] lemma posPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁺ x = (a x)⁺ := rfl
@[simp] lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁻ x = (a x)⁻ := rfl

end Lattice

section LinearOrder
variable [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

/--
Functions with locally finite support within `U` form an ordered commutative group.
-/
instance : IsOrderedAddMonoid (locallyFinsuppWithin U Y) where
  add_le_add_left := fun _ _ _ _ ↦ by simpa [le_def]

/--
The positive part of a sum is less than or equal to the sum of the positive parts.
-/
theorem posPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁺ ≤ f₁⁺ + f₂⁺ := by
  repeat rw [posPart_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

/--
The negative part of a sum is less than or equal to the sum of the negative parts.
-/
theorem negPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁻ ≤ f₁⁻ + f₂⁻ := by
  repeat rw [negPart_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_comm, add_le_add]
  · simp [add_nonneg]

/--
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
theorem nsmul_posPart (n : ℕ) (f : locallyFinsuppWithin U Y) : (n • f)⁺ = n • f⁺ := by
  ext x
  simp only [posPart, max_apply, coe_nsmul, Pi.smul_apply, coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
theorem nsmul_negPart (n : ℕ) (f : locallyFinsuppWithin U Y) : (n • f)⁻ = n • f⁻ := by
  ext x
  simp only [negPart, max_apply, coe_neg, coe_nsmul, Pi.neg_apply, Pi.smul_apply, coe_zero,
    Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Every positive function with locally finite supports dominates a singleton indicator.
-/
lemma exists_single_le_pos [DecidableEq X] {D : locallyFinsupp X ℤ} (h : 0 < D) :
    ∃ e, single e 1 ≤ D := by
  obtain ⟨z, hz⟩ : ∃ z, D z ≠ 0 := by simpa [D.ext_iff] using (ne_of_lt h).symm
  refine ⟨z, fun e ↦ ?_⟩
  obtain (rfl | he) := eq_or_ne e z
  · simpa [single_apply] using Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_apply] using h.le e

end LinearOrder

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

/--
Restriction of the zero function is the zero function.
-/
@[simp] lemma restrict_zero [Zero Y] {U V : Set X} (hV : V ⊆ U) :
    restrict (0 : Function.locallyFinsuppWithin U Y) hV = 0 := by
  ext
  rw [restrict_apply]
  aesop

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

/--
Present a function with with finite support as a finsum of singleton indicator functions.
-/
@[simp] lemma sum_apply_smul_single_eq_self [DecidableEq X] [AddCommMonoid Y] {U : Set X}
    {F : Function.locallyFinsuppWithin U Y} (h : F.support.Finite) :
    ∑ᶠ x, ((single x (F x)).restrict (subset_univ U)) = F := by
  have : (fun x ↦ (single x (F x)).restrict (subset_univ U)).support ⊆ h.toFinset := by
    intro
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp [restrict_apply]
  by_cases hz : z ∈ F.support
  · aesop
  · aesop

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
/--
Restriction commutes with taking positive parts.
-/
lemma restrict_posPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

/--
Restriction commutes with taking negative parts.
-/
lemma restrict_negPart {V : Set X} (D : locallyFinsuppWithin U ℤ) (h : V ⊆ U) :
    D⁻.restrict h = (D.restrict h)⁻ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

end Function.locallyFinsuppWithin
