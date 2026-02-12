/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.ModularLattice
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Nontriviality
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.Attr.Core

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
* `IsAtom a` indicates that the only element below `a` is `⊥`.
* `IsCoatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
* `IsAtomic` indicates that every element other than `⊥` is above an atom.
* `IsCoatomic` indicates that every element other than `⊤` is below a coatom.
* `IsAtomistic` indicates that every element is the `sSup` of a set of atoms.
* `IsCoatomistic` indicates that every element is the `sInf` of a set of coatoms.
* `IsStronglyAtomic` indicates that for all `a < b`, there is some `x` with `a ⋖ x ≤ b`.
* `IsStronglyCoatomic` indicates that for all `a < b`, there is some `x` with `a ≤ x ⋖ b`.

### Simple Lattices
* `IsSimpleOrder` indicates that an order has only two unique elements, `⊥` and `⊤`.
* `IsSimpleOrder.boundedOrder`
* `IsSimpleOrder.distribLattice`
* Given an instance of `IsSimpleOrder`, we provide the following definitions. These are not
  made global instances as they contain data :
  * `IsSimpleOrder.booleanAlgebra`
  * `IsSimpleOrder.completeLattice`
  * `IsSimpleOrder.completeBooleanAlgebra`

## Main results
* `isAtom_dual_iff_isCoatom` and `isCoatom_dual_iff_isAtom` express the (definitional) duality
  of `IsAtom` and `IsCoatom`.
* `isSimpleOrder_iff_isAtom_top` and `isSimpleOrder_iff_isCoatom_bot` express the
  connection between atoms, coatoms, and simple lattices
* `IsCompl.isAtom_iff_isCoatom` and `IsCompl.isCoatom_if_isAtom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
* `isAtomic_iff_isCoatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/

@[expose] public section

open Order

variable {ι : Sort*} {α β : Type*}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/-- An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

theorem isAtom_iff_le_of_ge : IsAtom a ↔ a ≠ ⊥ ∧ ∀ b ≠ ⊥, b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_ge]

lemma IsAtom.ne_bot (ha : IsAtom a) : a ≠ ⊥ := ha.1

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]

lemma IsAtom.bot_lt (h : IsAtom a) : ⊥ < a :=
  h.lt_iff.mpr rfl

lemma IsAtom.le_iff_eq (ha : IsAtom a) (hb : b ≠ ⊥) : b ≤ a ↔ b = a :=
  ha.le_iff.trans <| or_iff_right hb

lemma IsAtom.ne_iff_eq_bot (ha : IsAtom a) (hba : b ≤ a) : b ≠ a ↔ b = ⊥ where
  mp := (ha.le_iff.1 hba).resolve_right
  mpr := by rintro rfl; exact ha.ne_bot.symm

lemma IsAtom.ne_bot_iff_eq (ha : IsAtom a) (hba : b ≤ a) : b ≠ ⊥ ↔ b = a :=
  (ha.ne_iff_eq_bot hba).not_right.symm

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff

@[simp]
theorem bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff

end PartialOrder

section Frame
variable [Frame α] {f : ι → α} {s : Set α} {a : α}

protected lemma IsAtom.le_iSup (ha : IsAtom a) : a ≤ iSup f ↔ ∃ i, a ≤ f i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  change (a ≤ ⨆ i, f i) → _
  refine fun h => of_not_not fun ha' => ?_
  push_neg at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
    disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 <| of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl

protected lemma IsAtom.le_sSup (ha : IsAtom a) : a ≤ sSup s ↔ ∃ b ∈ s, a ≤ b := by
  simp [sSup_eq_iSup', ha.le_iSup]

end Frame
end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/-- A coatom of an `OrderTop` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤

attribute [to_dual existing] IsAtom
to_dual_insert_cast IsAtom := by grind
to_dual_insert_cast IsCoatom := by grind

attribute [to_dual] IsAtom.ne_bot
attribute [to_dual] IsAtom.lt_iff
attribute [to_dual] IsAtom.bot_lt
alias IsCoatom.lt_top := IsCoatom.top_lt

@[simp]
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a := by
  simp [IsCoatom, IsAtom, OrderDual.forall, OrderDual.toDual_lt_toDual]

@[simp]
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a := by
  simp [IsAtom, IsCoatom, OrderDual.forall, OrderDual.toDual_lt_toDual]

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, a.prop.trans hba.le⟩ hba)⟩

theorem isCoatom_iff_ge_of_le : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ b ≠ ⊤, a ≤ b → b ≤ a :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊤), Classical.not_imp, lt_iff_le_not_ge]

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a := by
  rw [le_iff_lt_or_eq, h.lt_iff, or_congr_right eq_comm]

lemma IsCoatom.ne_iff_eq_top (ha : IsCoatom a) (hab : a ≤ b) : b ≠ a ↔ b = ⊤ where
  mp := (ha.le_iff.1 hab).resolve_right
  mpr := by rintro rfl; exact ha.ne_top.symm

-- Register dual pairs for tactic-proof theorems, then auto-generate their dependents
attribute [to_dual existing] IsAtom.le_iff
attribute [to_dual existing] IsAtom.ne_iff_eq_bot
attribute [to_dual] IsAtom.le_iff_eq
attribute [to_dual] IsAtom.ne_bot_iff_eq
attribute [to_dual] IsAtom.Iic_eq

@[simp]
theorem covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a := by
  simp only [CovBy, lt_top_iff_ne_top, IsCoatom, not_not]

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff

namespace SetLike

variable {A B : Type*} [PartialOrder A] [SetLike A B] [IsConcreteLE A B]

theorem isAtom_iff [OrderBot A] {K : A} :
    IsAtom K ↔ K ≠ ⊥ ∧ ∀ H g, H ≤ K → g ∉ H → g ∈ K → H = ⊥ := by
  simp_rw [IsAtom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]

theorem isCoatom_iff [OrderTop A] {K : A} :
    IsCoatom K ↔ K ≠ ⊤ ∧ ∀ H g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ := by
  simp_rw [IsCoatom, lt_iff_le_not_ge, SetLike.not_le_iff_exists,
    and_comm (a := _ ≤ _), and_imp, exists_imp, ← and_imp, and_comm]

theorem covBy_iff {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ K → g ∈ H → H = L := by
  refine and_congr_right fun _ ↦ forall_congr' fun H ↦ ?_
  contrapose!
  rw [lt_iff_le_not_ge, lt_iff_le_and_ne, and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, and_comm, implies_true]

/-- Dual variant of `SetLike.covBy_iff` -/
theorem covBy_iff' {K L : A} :
    K ⋖ L ↔ K < L ∧ ∀ H g, K ≤ H → H ≤ L → g ∉ H → g ∈ L → H = K := by
  refine and_congr_right fun _ ↦ forall_congr' fun H ↦ not_iff_not.mp ?_
  push_neg
  rw [lt_iff_le_and_ne, lt_iff_le_not_ge, and_and_and_comm]
  simp_rw [exists_and_left, and_assoc, and_congr_right_iff, ← and_assoc, and_comm, exists_and_left,
    SetLike.not_le_iff_exists, ne_comm, implies_true]

end SetLike

end PartialOrder

section Coframe
variable [Coframe α] {f : ι → α} {s : Set α} {a : α}

protected lemma IsCoatom.iInf_le (ha : IsCoatom a) : iInf f ≤ a ↔ ∃ i, f i ≤ a := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans (iInf_le _ _) hi⟩
  refine fun h => of_not_not fun ha' => ?_
  push_neg at ha'
  have key : (⨅ i, f i) ⊔ a = ⊤ := by
    rw [iInf_sup_eq]
    refine eq_top_iff.mpr (le_iInf fun i => ?_)
    rcases (ha.le_iff (x := f i ⊔ a)).mp le_sup_right with htop | heq
    · exact htop ▸ le_rfl
    · exact absurd (heq ▸ le_sup_left : f i ≤ a) (ha' i)
  exact ha.1 (eq_top_iff.mpr (key ▸ sup_le h le_rfl))

protected lemma IsCoatom.sInf_le (ha : IsCoatom a) : sInf s ≤ a ↔ ∃ b ∈ s, b ≤ a := by
  simp [sInf_eq_iInf', ha.iInf_le]

end Coframe
end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b := by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using Set.ordConnected_Ici

@[simp]
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b := by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) ?_).symm
  simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using Set.ordConnected_Iic

theorem covBy_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp

theorem covBy_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp

end PartialOrder

section SemilatticeInf
variable [SemilatticeInf α] [OrderBot α] {a b : α}

lemma IsAtom.not_disjoint_iff_le (ha : IsAtom a) : ¬ Disjoint a b ↔ a ≤ b := by
  rw [disjoint_iff, ← inf_eq_left]; exact ha.ne_bot_iff_eq inf_le_left

lemma IsAtom.not_le_iff_disjoint (ha : IsAtom a) : ¬ a ≤ b ↔ Disjoint a b :=
  ha.not_disjoint_iff_le.not_right.symm

lemma IsAtom.disjoint_of_ne (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) : Disjoint a b := by
  simp [← ha.not_le_iff_disjoint, hb.le_iff, hab, ha.ne_bot]

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [OrderTop α] {a b : α}

lemma IsCoatom.not_codisjoint_iff_le (ha : IsCoatom a) : ¬ Codisjoint a b ↔ b ≤ a := by
  rw [codisjoint_iff, ← sup_eq_left]; exact ha.ne_top_iff_eq le_sup_left

lemma IsCoatom.not_le_iff_codisjoint (ha : IsCoatom a) : ¬ b ≤ a ↔ Codisjoint a b :=
  ha.not_codisjoint_iff_le.not_right.symm

lemma IsCoatom.codisjoint_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a ≠ b) :
    Codisjoint a b := by
  simp [← ha.not_le_iff_codisjoint, hb.le_iff, hab, ha.ne_top]

theorem IsCoatom.sup_eq_top_of_ne (ha : IsCoatom a) (hb : IsCoatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
  codisjoint_iff.1 <| ha.codisjoint_of_ne hb hab

end SemilatticeSup

end Atoms

section Atomic

variable [PartialOrder α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
class IsAtomic [OrderBot α] : Prop where
  /-- Every element other than `⊥` has an atom below it. -/
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
class IsCoatomic [OrderTop α] : Prop where
  /-- Every element other than `⊤` has an atom above it. -/
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

lemma IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [IsAtomic α] : ∃ a : α, IsAtom a :=
  have ⟨b, hb⟩ := exists_ne (⊥ : α)
  have ⟨a, ha⟩ := (eq_bot_or_exists_atom_le b).resolve_left hb
  ⟨a, ha.1⟩

lemma IsCoatomic.exists_coatom [OrderTop α] [Nontrivial α] [IsCoatomic α] : ∃ a : α, IsCoatom a :=
  have ⟨b, hb⟩ := exists_ne (⊤ : α)
  have ⟨a, ha⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb
  ⟨a, ha.1⟩

variable {α}

@[simp]
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α := by
  constructor
  · intro h
    exact ⟨fun b => by
      rcases h.eq_top_or_exists_le_coatom (OrderDual.toDual b) with hb | ⟨a, ha, hle⟩
      · left; exact OrderDual.toDual_inj.mp hb
      · right; exact ⟨OrderDual.ofDual a, isCoatom_dual_iff_isAtom.mp ha, hle⟩⟩
  · intro h
    exact ⟨fun b => by
      rcases h.eq_bot_or_exists_atom_le (OrderDual.ofDual b) with hb | ⟨a, ha, hle⟩
      · left; exact OrderDual.ofDual_inj.mp hb
      · right; exact ⟨OrderDual.toDual a, isCoatom_dual_iff_isAtom.mpr ha, hle⟩⟩

@[simp]
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α := by
  constructor
  · intro h
    exact ⟨fun b => by
      rcases h.eq_bot_or_exists_atom_le (OrderDual.toDual b) with hb | ⟨a, ha, hle⟩
      · left; exact OrderDual.toDual_inj.mp hb
      · right; exact ⟨OrderDual.ofDual a, isAtom_dual_iff_isCoatom.mp ha, hle⟩⟩
  · intro h
    exact ⟨fun b => by
      rcases h.eq_top_or_exists_le_coatom (OrderDual.ofDual b) with hb | ⟨a, ha, hle⟩
      · left; exact OrderDual.ofDual_inj.mp hb
      · right; exact ⟨OrderDual.toDual a, isAtom_dual_iff_isCoatom.mpr ha, hle⟩⟩

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

instance _root_.OrderDual.instIsCoatomic : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›

instance Set.Iic.isAtomic {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

instance _root_.OrderDual.instIsAtomic : IsAtomic αᵒᵈ :=
  isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›

instance Set.Ici.isCoatomic {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩

end IsCoatomic

theorem isAtomic_iff_forall_isAtomic_Iic [OrderBot α] :
    IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩

theorem isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  ⟨fun _ _ => IsCoatomic.Set.Ici.isCoatomic, fun h =>
    ⟨fun x =>
      ((@eq_top_or_exists_le_coatom _ _ _ (h x)) (⊥ : Set.Ici x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsCoatom.of_isCoatom_coe_Ici)⟩⟩

section StronglyAtomic

variable {α : Type*} {a b : α} [Preorder α]

/-- An order is strongly atomic if every nontrivial interval `[a, b]`
contains an element covering `a`. -/
@[mk_iff]
class IsStronglyAtomic (α : Type*) [Preorder α] : Prop where
  exists_covBy_le_of_lt : ∀ (a b : α), a < b → ∃ x, a ⋖ x ∧ x ≤ b

theorem exists_covBy_le_of_lt [IsStronglyAtomic α] (h : a < b) : ∃ x, a ⋖ x ∧ x ≤ b :=
  IsStronglyAtomic.exists_covBy_le_of_lt a b h

alias LT.lt.exists_covby_le := exists_covBy_le_of_lt

/-- An order is strongly coatomic if every nontrivial interval `[a, b]`
contains an element covered by `b`. -/
@[mk_iff]
class IsStronglyCoatomic (α : Type*) [Preorder α] : Prop where
  (exists_le_covBy_of_lt : ∀ (a b : α), a < b → ∃ x, a ≤ x ∧ x ⋖ b)

theorem exists_le_covBy_of_lt [IsStronglyCoatomic α] (h : a < b) : ∃ x, a ≤ x ∧ x ⋖ b :=
  IsStronglyCoatomic.exists_le_covBy_of_lt a b h

alias LT.lt.exists_le_covby := exists_le_covBy_of_lt

theorem isStronglyAtomic_dual_iff_is_stronglyCoatomic :
    IsStronglyAtomic αᵒᵈ ↔ IsStronglyCoatomic α := by
  simpa [isStronglyAtomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyCoatomic_iff] using forall_comm

@[simp] theorem isStronglyCoatomic_dual_iff_is_stronglyAtomic :
    IsStronglyCoatomic αᵒᵈ ↔ IsStronglyAtomic α := by
  simpa [isStronglyCoatomic_iff, OrderDual.exists, OrderDual.forall,
    OrderDual.toDual_le_toDual, and_comm, isStronglyAtomic_iff] using forall_comm

instance OrderDual.instIsStronglyCoatomic [IsStronglyAtomic α] : IsStronglyCoatomic αᵒᵈ := by
  rwa [isStronglyCoatomic_dual_iff_is_stronglyAtomic]

instance [IsStronglyCoatomic α] : IsStronglyAtomic αᵒᵈ := by
  rwa [isStronglyAtomic_dual_iff_is_stronglyCoatomic]

instance IsStronglyAtomic.isAtomic (α : Type*) [PartialOrder α] [OrderBot α] [IsStronglyAtomic α] :
    IsAtomic α where
  eq_bot_or_exists_atom_le a := by
    rw [or_iff_not_imp_left, ← Ne, ← bot_lt_iff_ne_bot]
    refine fun hlt ↦ ?_
    obtain ⟨x, hx, hxa⟩ := hlt.exists_covby_le
    exact ⟨x, bot_covBy_iff.1 hx, hxa⟩

instance IsStronglyCoatomic.toIsCoatomic (α : Type*) [PartialOrder α] [OrderTop α]
    [IsStronglyCoatomic α] : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 <| IsStronglyAtomic.isAtomic (α := αᵒᵈ)

theorem Set.OrdConnected.isStronglyAtomic [IsStronglyAtomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyAtomic s where
  exists_covBy_le_of_lt := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_covby_le
    exact ⟨⟨x, h.out' hc hd ⟨hcx.le, hxd⟩⟩,
      ⟨by simpa using hcx.lt, fun y hy hy' ↦ hcx.2 (by simpa using hy) (by simpa using hy')⟩, hxd⟩

theorem Set.OrdConnected.isStronglyCoatomic [IsStronglyCoatomic α] {s : Set α}
    (h : Set.OrdConnected s) : IsStronglyCoatomic s where
  exists_le_covBy_of_lt := by
    rintro ⟨c, hc⟩ ⟨d, hd⟩ hcd
    obtain ⟨x, hcx, hxd⟩ := (Subtype.mk_lt_mk.1 hcd).exists_le_covby
    exact ⟨⟨x, h.out' hc hd ⟨hcx, hxd.le⟩⟩,
      hcx, ⟨by simpa using hxd.lt, fun y hy hy' ↦ hxd.2 (by simpa using hy) (by simpa using hy')⟩⟩

instance [IsStronglyAtomic α] {s : Set α} [Set.OrdConnected s] : IsStronglyAtomic s :=
  Set.OrdConnected.isStronglyAtomic <| by assumption

instance [IsStronglyCoatomic α] {s : Set α} [h : Set.OrdConnected s] : IsStronglyCoatomic s :=
  Set.OrdConnected.isStronglyCoatomic <| by assumption

instance SuccOrder.toIsStronglyAtomic [SuccOrder α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a _ hab :=
    ⟨SuccOrder.succ a, Order.covBy_succ_of_not_isMax fun ha ↦ ha.not_lt hab,
      SuccOrder.succ_le_of_lt hab⟩

instance [PredOrder α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end StronglyAtomic

section WellFounded

theorem IsStronglyAtomic.of_wellFounded_lt (h : WellFounded ((· < ·) : α → α → Prop)) :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    refine ⟨WellFounded.min h (Set.Ioc a b) ⟨b, hab,rfl.le⟩, ?_⟩
    have hmem := (WellFounded.min_mem h (Set.Ioc a b) ⟨b, hab,rfl.le⟩)
    exact ⟨⟨hmem.1,fun c hac hlt ↦ WellFounded.not_lt_min h
      (Set.Ioc a b) ⟨b, hab,rfl.le⟩ ⟨hac, hlt.le.trans hmem.2⟩ hlt ⟩, hmem.2⟩

theorem IsStronglyCoatomic.of_wellFounded_gt (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsStronglyCoatomic α where
  exists_le_covBy_of_lt a b hab := by
    refine ⟨WellFounded.min h (Set.Ico a b) ⟨a, rfl.le, hab⟩, ?_⟩
    have hmem := WellFounded.min_mem h (Set.Ico a b) ⟨a, rfl.le, hab⟩
    exact ⟨hmem.1, ⟨hmem.2, fun c hlt hcb ↦ WellFounded.not_lt_min h
      (Set.Ico a b) ⟨a, rfl.le, hab⟩ ⟨hmem.1.trans hlt.le, hcb⟩ hlt⟩⟩

instance [WellFoundedLT α] : IsStronglyAtomic α :=
  IsStronglyAtomic.of_wellFounded_lt wellFounded_lt

instance [WellFoundedGT α] : IsStronglyCoatomic α :=
    IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt

theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  (IsStronglyAtomic.of_wellFounded_lt h).isAtomic

theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  (IsStronglyCoatomic.of_wellFounded_gt h).toIsCoatomic

end WellFounded

namespace BooleanAlgebra

theorem le_iff_atom_le_imp {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x ≤ y ↔ ∀ a, IsAtom a → a ≤ x → a ≤ y := by
  refine ⟨fun h a _ => (le_trans · h), fun h => ?_⟩
  have : x ⊓ yᶜ = ⊥ := of_not_not fun hbot =>
    have ⟨a, ha, hle⟩ := (eq_bot_or_exists_atom_le _).resolve_left hbot
    have ⟨hx, hy'⟩ := le_inf_iff.1 hle
    have hy := h a ha hx
    have : a ≤ y ⊓ yᶜ := le_inf_iff.2 ⟨hy, hy'⟩
    ha.1 (by simpa using this)
  exact (eq_compl_iff_isCompl.1 (by simp)).inf_right_eq_bot_iff.1 this

theorem eq_iff_atom_le_iff {α} [BooleanAlgebra α] [IsAtomic α] {x y : α} :
    x = y ↔ ∀ a, IsAtom a → (a ≤ x ↔ a ≤ y) := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

end BooleanAlgebra

namespace CompleteBooleanAlgebra

/-- Every atomic complete Boolean algebra is completely atomic.

This is not made an instance to avoid typeclass loops. -/
-- See note [reducible non-instances]
abbrev toCompleteAtomicBooleanAlgebra {α} [CompleteBooleanAlgebra α] [IsAtomic α] :
    CompleteAtomicBooleanAlgebra α where
  __ := ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, ha.le_iSup, Classical.skolem]

end CompleteBooleanAlgebra

end Atomic

section Atomistic

variable (α) [PartialOrder α]

/-- A lattice is atomistic iff every element is a `sSup` of a set of atoms. -/
@[mk_iff]
class IsAtomistic [OrderBot α] : Prop where
  /-- Every element is a `sSup` of a set of atoms. -/
  isLUB_atoms : ∀ b : α, ∃ s : Set α, IsLUB s b ∧ ∀ a, a ∈ s → IsAtom a

/-- A lattice is coatomistic iff every element is an `sInf` of a set of coatoms. -/
@[mk_iff]
class IsCoatomistic [OrderTop α] : Prop where
  /-- Every element is a `sInf` of a set of coatoms. -/
  isGLB_coatoms : ∀ b : α, ∃ s : Set α, IsGLB s b ∧ ∀ a, a ∈ s → IsCoatom a

export IsAtomistic (isLUB_atoms)

export IsCoatomistic (isGLB_coatoms)

variable {α}

@[simp]
theorem isCoatomistic_dual_iff_isAtomistic [OrderBot α] : IsCoatomistic αᵒᵈ ↔ IsAtomistic α := by
  constructor
  · intro h
    exact ⟨fun b => by
      obtain ⟨s, hsb, hs⟩ := h.isGLB_coatoms (OrderDual.toDual b)
      refine ⟨OrderDual.ofDual '' s, ⟨?_, ?_⟩, fun a ⟨x, hx, hxa⟩ => hxa ▸
        isCoatom_dual_iff_isAtom.mp (hs x hx)⟩
      · rintro _ ⟨x, hx, rfl⟩; exact hsb.1 hx
      · intro y hy; exact hsb.2 (fun x hx => hy ⟨x, hx, rfl⟩)⟩
  · intro h
    exact ⟨fun b => by
      obtain ⟨s, hsb, hs⟩ := h.isLUB_atoms (OrderDual.ofDual b)
      refine ⟨OrderDual.toDual '' s, ⟨?_, ?_⟩, fun a ⟨x, hx, hxa⟩ => hxa ▸
        isCoatom_dual_iff_isAtom.mpr (hs x hx)⟩
      · rintro _ ⟨x, hx, rfl⟩; exact hsb.1 hx
      · intro y hy; exact hsb.2 (fun x hx => hy ⟨x, hx, rfl⟩)⟩

@[simp]
theorem isAtomistic_dual_iff_isCoatomistic [OrderTop α] : IsAtomistic αᵒᵈ ↔ IsCoatomistic α := by
  constructor
  · intro h
    exact ⟨fun b => by
      obtain ⟨s, hsb, hs⟩ := h.isLUB_atoms (OrderDual.toDual b)
      refine ⟨OrderDual.ofDual '' s, ⟨?_, ?_⟩, fun a ⟨x, hx, hxa⟩ => hxa ▸
        isAtom_dual_iff_isCoatom.mp (hs x hx)⟩
      · rintro _ ⟨x, hx, rfl⟩; exact hsb.1 hx
      · intro y hy; exact hsb.2 (fun x hx => hy ⟨x, hx, rfl⟩)⟩
  · intro h
    exact ⟨fun b => by
      obtain ⟨s, hsb, hs⟩ := h.isGLB_coatoms (OrderDual.ofDual b)
      refine ⟨OrderDual.toDual '' s, ⟨?_, ?_⟩, fun a ⟨x, hx, hxa⟩ => hxa ▸
        isAtom_dual_iff_isCoatom.mpr (hs x hx)⟩
      · rintro _ ⟨x, hx, rfl⟩; exact hsb.1 hx
      · intro y hy; exact hsb.2 (fun x hx => hy ⟨x, hx, rfl⟩)⟩

namespace IsAtomistic

instance _root_.OrderDual.instIsCoatomistic [OrderBot α] [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h

variable [OrderBot α] [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases isLUB_atoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsAtomistic

section IsAtomistic

variable [OrderBot α] [IsAtomistic α]

theorem isLUB_atoms_le (b : α) : IsLUB { a : α | IsAtom a ∧ a ≤ b } b := by
  rcases isLUB_atoms b with ⟨s, hsb, hs⟩
  exact ⟨fun c hc ↦ hc.2, fun c hc ↦ hsb.2 fun i hi ↦ hc ⟨hs _ hi, hsb.1 hi⟩⟩

theorem isLUB_atoms_top [OrderTop α] : IsLUB { a : α | IsAtom a } ⊤ := by
  simpa using isLUB_atoms_le (⊤ : α)

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun hab _ _ hca ↦ hca.trans hab,
   fun h ↦ (isLUB_atoms_le a).mono (isLUB_atoms_le b) fun _ ⟨h₁, h₂⟩ ↦ ⟨h₁, h _ h₁ h₂⟩⟩

theorem eq_iff_atom_le_iff {a b : α} : a = b ↔ ∀ c, IsAtom c → (c ≤ a ↔ c ≤ b) := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  rw [le_antisymm_iff, le_iff_atom_le_imp, le_iff_atom_le_imp]
  simp_all

end IsAtomistic

namespace IsCoatomistic

variable [OrderTop α]

instance _root_.OrderDual.instIsAtomistic [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases isGLB_coatoms b with ⟨s, hsb, hs⟩
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp_all
    · exact Or.inr ⟨a, hs _ ha, hsb.1 ha⟩⟩

end IsCoatomistic

section CompleteLattice

@[simp]
theorem sSup_atoms_le_eq {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    sSup { a : α | IsAtom a ∧ a ≤ b } = b :=
  (isLUB_atoms_le b).sSup_eq

@[simp]
theorem sSup_atoms_eq_top {α} [CompleteLattice α] [IsAtomistic α] :
    sSup { a : α | IsAtom a } = ⊤ :=
  isLUB_atoms_top.sSup_eq

nonrec lemma CompleteLattice.isAtomistic_iff {α} [CompleteLattice α] :
    IsAtomistic α ↔ ∀ b : α, ∃ s : Set α, b = sSup s ∧ ∀ a ∈ s, IsAtom a := by
  simp_rw [isAtomistic_iff, isLUB_iff_sSup_eq, eq_comm]

lemma eq_sSup_atoms {α} [CompleteLattice α] [IsAtomistic α] (b : α) :
    ∃ s : Set α, b = sSup s ∧ ∀ a ∈ s, IsAtom a :=
  CompleteLattice.isAtomistic_iff.1 ‹_› b

nonrec lemma CompleteLattice.isCoatomistic_iff {α} [CompleteLattice α] :
    IsCoatomistic α ↔ ∀ b : α, ∃ s : Set α, b = sInf s ∧ ∀ a ∈ s, IsCoatom a := by
  simp_rw [isCoatomistic_iff, isGLB_iff_sInf_eq, eq_comm]

lemma eq_sInf_coatoms {α} [CompleteLattice α] [IsCoatomistic α] (b : α) :
    ∃ s : Set α, b = sInf s ∧ ∀ a ∈ s, IsCoatom a :=
  CompleteLattice.isCoatomistic_iff.1 ‹_› b

end CompleteLattice

namespace CompleteAtomicBooleanAlgebra

instance {α} [CompleteAtomicBooleanAlgebra α] : IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b ↦ by
    inhabit α
    refine ⟨{ a | IsAtom a ∧ a ≤ b }, ?_, fun a ha => ha.1⟩
    refine le_antisymm ?_ (sSup_le fun c hc => hc.2)
    have : (⨅ c : α, ⨆ x, b ⊓ cond x c (cᶜ)) = b := by simp [iSup_bool_eq]
    rw [← this]; clear this
    simp_rw [iInf_iSup_eq, iSup_le_iff]; intro g
    if h : (⨅ a, b ⊓ cond (g a) a (aᶜ)) = ⊥ then simp [h] else
    refine le_sSup ⟨⟨h, fun c hc => ?_⟩, le_trans (by rfl) (le_iSup _ g)⟩; clear h
    have := lt_of_lt_of_le hc (le_trans (iInf_le _ c) inf_le_right)
    revert this
    nontriviality α
    cases g c <;> simp

instance {α} [CompleteAtomicBooleanAlgebra α] : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 inferInstance

@[deprecated "Use `IsAtom.le_sSup` instead" (since := "2025-11-24")]
theorem exists_mem_le_of_le_sSup_of_isAtom {α} [CompleteAtomicBooleanAlgebra α] {a}
    (ha : IsAtom a) {s : Set α} (hs : a ≤ sSup s) : ∃ b ∈ s, a ≤ b :=
  (IsAtom.le_sSup ha).mp hs

lemma eq_setOf_le_sSup_and_isAtom {α} [CompleteAtomicBooleanAlgebra α] {S : Set α}
    (hS : ∀ a ∈ S, IsAtom a) : S = {a | a ≤ sSup S ∧ IsAtom a} := by
  ext a
  refine ⟨fun h => ⟨CompleteLattice.le_sSup S a h, hS a h⟩, fun ⟨hale, hatom⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := (IsAtom.le_sSup hatom).mp hale
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

/--
Representation theorem for complete atomic boolean algebras:
For a complete atomic Boolean algebra `α`, `toSetOfIsAtom` is an order isomorphism
between `α` and the set of subsets of its atoms.
-/
def toSetOfIsAtom {α} [CompleteAtomicBooleanAlgebra α] : α ≃o (Set {a : α // IsAtom a}) where
  toFun A := {a | a ≤ A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : ∀ a ∈ Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff, eq_setOf_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm

end CompleteAtomicBooleanAlgebra

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
@[mk_iff]
class IsSimpleOrder (α : Type*) [LE α] [BoundedOrder α] : Prop extends Nontrivial α where
  /-- Every element is either `⊥` or `⊤` -/
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤

export IsSimpleOrder (eq_bot_or_eq_top)

lemma IsSimpleOrder.of_forall_eq_top {α : Type*} [LE α] [BoundedOrder α] [Nontrivial α]
    (h : ∀ a : α, a ≠ ⊥ → a = ⊤) :
    IsSimpleOrder α where
  eq_bot_or_eq_top a := or_iff_not_imp_left.mpr <| h a

theorem isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ := by
  constructor <;> intro i
  · exact
      { eq_bot_or_eq_top := fun a => by
          rcases eq_bot_or_eq_top (OrderDual.ofDual a) with h | h
          · exact Or.inr (OrderDual.ofDual_inj.mp h)
          · exact Or.inl (OrderDual.ofDual_inj.mp h) }
  · exact
      { exists_pair_ne := by
          obtain ⟨a, b, hab⟩ := i.exists_pair_ne
          exact ⟨OrderDual.ofDual a, OrderDual.ofDual b,
            fun h => hab (OrderDual.ofDual_inj.mp h)⟩
        eq_bot_or_eq_top := fun a => by
          rcases i.eq_bot_or_eq_top (OrderDual.toDual a) with h | h
          · exact Or.inr (OrderDual.toDual_inj.mp h)
          · exact Or.inl (OrderDual.toDual_inj.mp h) }

theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first | simpa | simpa using h.symm

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance OrderDual.instIsSimpleOrder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    IsSimpleOrder αᵒᵈ := isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

/-- A simple `BoundedOrder` induces a preorder. This is not an instance to prevent loops. -/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Preorder α where
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp

/-- A simple partial ordered `BoundedOrder` induces a linear order.
This is not an instance to prevent loops. -/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    -- Note from https://github.com/leanprover-community/mathlib4/issues/23976: do we want this inlined or should this be a separate definition?
    toDecidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H))
    toDecidableEq := ‹_› }

theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]
theorem isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤ :=
  ⟨fun h ↦ (eq_bot_or_eq_top a).resolve_left h.1, (· ▸ isAtom_top)⟩

theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top

@[simp]
theorem isCoatom_iff_eq_bot {a : α} : IsCoatom a ↔ a = ⊥ :=
  ⟨fun h ↦ (eq_bot_or_eq_top a).resolve_right h.1, (· ▸ isCoatom_bot)⟩

theorem bot_covBy_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covBy

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)
include h

theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt
end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `BoundedOrder` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder

/-- A lattice that is a `BoundedOrder` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

-- see Note [lower instance priority]
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨isAtom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (by infer_instance)

end BoundedOrder

-- It is important that in this section `IsSimpleOrder` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-- Every simple lattice is isomorphic to `Bool`, regardless of order. -/
@[simps]
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool where
  toFun x := x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]

/-- Every simple lattice over a partial order is order-isomorphic to `Bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, Bool.false_lt_true]
        · simp }

/-- A simple `BoundedOrder` is also a `BooleanAlgebra`. -/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { inferInstanceAs (BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open Classical in
/-- A simple `BoundedOrder` is also complete. -/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    sInf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    le_sSup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_pos h]
    sSup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
      · exact le_top
    sInf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_pos h]
      · exact le_top
    le_sInf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }

open Classical in
/-- A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra }

instance : ComplementedLattice α :=
  letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

end IsSimpleOrder

namespace IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance (priority := 100) : IsAtomistic α where
  isLUB_atoms b := (eq_bot_or_eq_top b).elim (fun h ↦ ⟨∅, by simp [h]⟩) (fun h ↦ ⟨{⊤}, by simp [h]⟩)

instance (priority := 100) : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 (by infer_instance)

@[simp] lemma bot_lt_iff_eq_top {a : α} : ⊥ < a ↔ a = ⊤ :=
  ⟨eq_top_of_lt, fun h ↦ h ▸ bot_lt_top⟩

@[simp] lemma lt_top_iff_eq_bot {a : α} : a < ⊤ ↔ a = ⊥ :=
  ⟨eq_bot_of_lt, fun h ↦ h ▸ bot_lt_top⟩

end IsSimpleOrder

theorem isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩

theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  ⟨fun h => @isCoatom_bot _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊥, ⊤, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le bot_le).imp_left Eq.symm).imp_right (h.2 a) }⟩

namespace Set

theorem isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
  isSimpleOrder_iff_isAtom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

theorem isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  isSimpleOrder_iff_isCoatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

theorem isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b := by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)

theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b := by
  simp only [← covBy_top_iff] at hb ⊢
  exact CovBy.of_image f (htop.symm ▸ hb)

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

theorem isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb

theorem isAtom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (a : α) :
    IsAtom (l a) ↔ IsAtom a := by
  refine ⟨fun hla => ?_, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
  obtain ⟨a', ha', hab'⟩ :=
    (eq_bot_or_exists_atom_le (u (l a))).resolve_left (hbot ▸ fun h => hla.1 (gi.u_injective h))
  have :=
    (hla.le_iff.mp <| (gi.l_u_eq (l a) ▸ gi.gc.monotone_l hab' : l a' ≤ l a)).resolve_left fun h =>
      ha'.1 (hbot ▸ h_atom a' ha' ▸ congr_arg u h)
  have haa' : a = a' :=
    (ha'.le_iff.mp <|
          (gi.gc.le_u_l a).trans_eq (h_atom a' ha' ▸ congr_arg u this.symm)).resolve_left
      (mt (congr_arg l) (gi.gc.l_bot.symm ▸ hla.1))
  exact haa'.symm ▸ ha'

theorem isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]

theorem isCoatom_of_image [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb

theorem isCoatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (h_coatom : ∀ a : α, IsCoatom a → u (l a) = a) (b : β) :
    IsCoatom (u b) ↔ IsCoatom b := by
  refine ⟨fun hb => gi.isCoatom_of_image hb, fun hb => ?_⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
      hb.1 <| (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b ≤ l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

theorem isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨l, gi.l_injective⟩, @GaloisCoinsertion.l_le_l_iff _ _ _ _ _ _ gi⟩ htop hb

theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b : β, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b := by
  have hu_top : u ⊤ = ⊤ := by rw [← htop, gi.u_l_eq]
  refine ⟨fun hub => ?_, fun hb => ?_⟩
  · -- Forward: IsCoatom (u b) → IsCoatom b
    have hb_ne : b ≠ ⊤ := fun h => hub.1 (h ▸ hu_top)
    obtain ⟨c, hc, hbc⟩ := (eq_top_or_exists_le_coatom b).resolve_left hb_ne
    have huc : l (u c) = c := h_coatom c hc
    have hub_le : u b ≤ u c := gi.gc.monotone_u hbc
    rcases hub.le_iff.mp hub_le with htop' | heq
    · exact absurd (huc ▸ congr_arg l htop' ▸ htop : c = ⊤) hc.1
    · have : b = c := le_antisymm hbc (huc ▸ heq ▸ gi.gc.l_u_le b)
      exact this ▸ hc
  · -- Backward: IsCoatom b → IsCoatom (u b)
    exact gi.isCoatom_of_l_top htop ((h_coatom b hb).symm ▸ hb)

theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a := by rw [← gi.isCoatom_iff htop h_coatom, gi.u_l_eq]

theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨l, gi.l_injective⟩, @GaloisCoinsertion.l_le_l_iff _ _ _ _ _ _ gi⟩ gi.gc.l_bot hb

theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a := by
  refine ⟨gi.isAtom_of_image, fun ha => ?_⟩
  have hla : l a ≠ ⊥ := fun h => ha.1 (gi.l_injective (h.trans gi.gc.l_bot.symm))
  obtain ⟨b, hb, hble⟩ := (eq_bot_or_exists_atom_le (l a)).resolve_left hla
  have hub : l (u b) = b := h_atom b hb
  have huba : u b ≤ a := gi.u_l_eq a ▸ gi.gc.monotone_u hble
  have hne : u b ≠ ⊥ := fun h => hb.1 (hub ▸ congr_arg l h ▸ gi.gc.l_bot)
  have heq : u b = a := (ha.le_iff.mp huba).resolve_left hne
  rw [show a = u b from heq.symm, hub]; exact hb

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
    f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) <| (f.symm_apply_apply a).symm ▸ ha⟩

@[simp]
theorem isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  ⟨f.toGaloisCoinsertion.isCoatom_of_l_top (map_top f) , fun ha =>
    f.toGaloisInsertion.isCoatom_of_image <| (f.symm_apply_apply a).symm ▸ ha⟩

theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top, ← f.isAtom_iff ⊤,
    f.map_top]

theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.isSimpleOrder_iff.mpr h

protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]

protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]

end OrderIso
section Lattice

variable [Lattice α]

/-- An upper-modular lattice that is atomistic is strongly atomic.
Not an instance to prevent loops. -/
theorem Lattice.isStronglyAtomic [OrderBot α] [IsUpperModularLattice α] [IsAtomistic α] :
    IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨s, hsb, h⟩ := isLUB_atoms b
    refine by_contra fun hcon ↦ hab.not_ge <| (isLUB_le_iff hsb).2 fun x hx ↦ ?_
    simp_rw [not_exists, and_comm (b := _ ≤ _), not_and] at hcon
    specialize hcon (x ⊔ a) (sup_le (hsb.1 hx) hab.le)
    obtain (hbot | h_inf) := (h x hx).bot_covBy.eq_or_eq (c := x ⊓ a) (by simp) (by simp)
    · exact False.elim <| hcon <|
        (hbot ▸ IsUpperModularLattice.covBy_sup_of_inf_covBy) (h x hx).bot_covBy
    rwa [inf_eq_left] at h_inf

/-- A lower-modular lattice that is coatomistic is strongly coatomic.
Not an instance to prevent loops. -/
theorem Lattice.isStronglyCoatomic [OrderTop α] [IsLowerModularLattice α]
    [IsCoatomistic α] : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]
  exact Lattice.isStronglyAtomic

end Lattice

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)
include hc

theorem isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b :=
  Set.isSimpleOrder_Iic_iff_isAtom.symm.trans <|
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom

theorem isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b :=
  hc.symm.isAtom_iff_isCoatom.symm

end IsCompl

variable [ComplementedLattice α]

theorem isCoatomic_of_isAtomic_of_complementedLattice_of_isModular [IsAtomic α] :
    IsCoatomic α :=
  ⟨fun x => by
    rcases exists_isCompl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_isCompl (xy.symm.IicOrderIsoIci ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici ?_, xb⟩
      rw [← hb.isAtom_iff_isCoatom, OrderIso.isAtom_iff]
      apply ha.Iic⟩

theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun _ => isCoatomic_of_isAtomic_of_complementedLattice_of_isModular,
   fun _ => isAtomic_of_isCoatomic_of_complementedLattice_of_isModular⟩

/-- A complemented modular atomic lattice is strongly atomic.
Not an instance to prevent loops. -/
theorem ComplementedLattice.isStronglyAtomic [IsAtomic α] : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨⟨a', ha'b : a' ≤ b⟩, ha'⟩ := exists_isCompl (α := Set.Iic b) ⟨a, hab.le⟩
    obtain (rfl | ⟨d, hd⟩) := eq_bot_or_exists_atom_le a'
    · obtain rfl : a = b := by simpa [codisjoint_bot, ← Subtype.coe_inj] using ha'.codisjoint
      exact False.elim <| hab.ne rfl
    refine ⟨d ⊔ a, IsUpperModularLattice.covBy_sup_of_inf_covBy ?_, sup_le (hd.2.trans ha'b) hab.le⟩
    convert hd.1.bot_covBy
    rw [← le_bot_iff, ← show a ⊓ a' = ⊥ by simpa using Subtype.coe_inj.2 ha'.inf_eq_bot, inf_comm]
    exact inf_le_inf_left _ hd.2

/-- A complemented modular coatomic lattice is strongly coatomic.
Not an instance to prevent loops. -/
theorem ComplementedLattice.isStronglyCoatomic [IsCoatomic α] : IsStronglyCoatomic α :=
  isStronglyAtomic_dual_iff_is_stronglyCoatomic.1 <| ComplementedLattice.isStronglyAtomic

/-- A complemented modular atomic lattice is strongly coatomic.
Not an instance to prevent loops. -/
theorem ComplementedLattice.isStronglyAtomic' [h : IsAtomic α] : IsStronglyCoatomic α := by
  rw [isAtomic_iff_isCoatomic] at h
  exact isStronglyCoatomic

/-- A complemented modular coatomic lattice is strongly atomic.
Not an instance to prevent loops. -/
theorem ComplementedLattice.isStronglyCoatomic' [h : IsCoatomic α] : IsStronglyAtomic α := by
  rw [← isAtomic_iff_isCoatomic] at h
  exact isStronglyAtomic

end IsModularLattice

namespace «Prop»

instance : IsSimpleOrder Prop where
  eq_bot_or_eq_top p := by simp [em']

theorem isAtom_iff {p : Prop} : IsAtom p ↔ p := by simp

theorem isCoatom_iff {p : Prop} : IsCoatom p ↔ ¬ p := by simp

end «Prop»

namespace Pi

universe u
variable {ι : Type*} {π : ι → Type u}

protected theorem eq_bot_iff [∀ i, Bot (π i)] {f : ∀ i, π i} : f = ⊥ ↔ ∀ i, f i = ⊥ :=
  funext_iff

theorem isAtom_iff {f : ∀ i, π i} [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] :
    IsAtom f ↔ ∃ i, IsAtom (f i) ∧ ∀ j, j ≠ i → f j = ⊥ := by
  simp only [← bot_covBy_iff, Pi.covBy_iff, bot_apply, eq_comm]

theorem isAtom_single {i : ι} [DecidableEq ι] [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)]
    {a : π i} (h : IsAtom a) : IsAtom (Function.update (⊥ : ∀ i, π i) i a) :=
  isAtom_iff.2 ⟨i, by simpa, fun _ hji => Function.update_of_ne hji ..⟩

theorem isAtom_iff_eq_single [DecidableEq ι] [∀ i, PartialOrder (π i)]
    [∀ i, OrderBot (π i)] {f : ∀ i, π i} :
    IsAtom f ↔ ∃ i a, IsAtom a ∧ f = Function.update ⊥ i a := by
  simp [← bot_covBy_iff, covBy_iff_exists_right_eq]

instance isAtomic [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] [∀ i, IsAtomic (π i)] :
    IsAtomic (∀ i, π i) where
  eq_bot_or_exists_atom_le b := or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : ∃ i, b i ≠ ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    by classical exact ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩

instance isCoatomic [∀ i, PartialOrder (π i)] [∀ i, OrderTop (π i)] [∀ i, IsCoatomic (π i)] :
    IsCoatomic (∀ i, π i) where
  eq_top_or_exists_le_coatom b := by
    by_cases h : b = ⊤
    · exact Or.inl h
    · right
      have ⟨i, hi⟩ : ∃ i, b i ≠ ⊤ := by
        by_contra! hall
        exact h (funext fun j => hall j)
      obtain ⟨a, ha, hab⟩ := (eq_top_or_exists_le_coatom (b i)).resolve_left hi
      classical
      refine ⟨Function.update ⊤ i a, ?_, ?_⟩
      · constructor
        · intro htop
          exact ha.1 (by simpa using congr_fun htop i)
        · intro g hg
          have hle := hg.le
          have hne := hg.ne
          have hgi : a < g i := by
            refine lt_of_le_of_ne (by simpa using hle i) ?_
            intro heq
            exact hne (funext fun j => by
              by_cases hji : j = i
              · subst hji; simpa using heq
              · exact le_antisymm (hle j) (by simp [Function.update_of_ne hji]))
          funext j
          by_cases hji : j = i
          · subst hji; simpa using ha.2 _ hgi
          · exact le_antisymm le_top (by simpa [Function.update_of_ne hji] using hle j)
      · intro j
        by_cases hji : j = i
        · subst hji; simpa
        · simp [Function.update_of_ne hji]

instance isAtomistic [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] [∀ i, IsAtomistic (π i)] :
    IsAtomistic (∀ i, π i) where
  isLUB_atoms s := by
    classical
    refine ⟨{f | IsAtom f ∧ f ≤ s}, ?_, by simp +contextual⟩
    rw [isLUB_pi]
    intro i
    simp_rw [isAtom_iff_eq_single]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨⟨_, _, _, rfl⟩, hs⟩, rfl⟩
      exact hs i
    · refine fun j hj ↦ (isLUB_atoms_le (s i)).2 fun x ⟨hx₁, hx₂⟩ ↦ ?_
      exact hj ⟨Function.update ⊥ i x, ⟨⟨_, x, hx₁, rfl⟩, by simp [update_le_iff, hx₂]⟩, by simp⟩

instance isCoatomistic [∀ i, CompleteLattice (π i)] [∀ i, IsCoatomistic (π i)] :
    IsCoatomistic (∀ i, π i) where
  isGLB_coatoms s := by
    classical
    refine ⟨{f | IsCoatom f ∧ s ≤ f}, ?_, by simp +contextual⟩
    rw [isGLB_pi]
    intro i
    refine ⟨fun _ ⟨f, ⟨_, hs⟩, hfi⟩ => hfi ▸ hs i, fun j hj => ?_⟩
    obtain ⟨t, ht, hta⟩ := isGLB_coatoms (s i)
    exact ht.2 fun x hx => hj ⟨Function.update ⊤ i x,
      ⟨⟨fun htop => (hta x hx).1 (by simpa using congr_fun htop i),
        fun g hg => by
          have hle := hg.le
          have hne := hg.ne
          funext j
          by_cases hji : j = i
          · rw [hji]
            have hxi : x ≤ g i := by simpa using hle i
            have hxne : x ≠ g i := by
              intro h; exact hne (funext fun k => by
                by_cases hki : k = i
                · rw [hki]; simpa using h
                · exact le_antisymm (hle k) (by simp [Function.update_of_ne hki]))
            exact (hta x hx).2 _ (lt_of_le_of_ne hxi hxne)
          · exact le_antisymm le_top
              (by simpa [Function.update_of_ne hji] using hle j)⟩,
        Pi.le_def.2 fun j => by
          by_cases hji : j = i
          · subst hji; simpa using ht.1 hx
          · simp [Function.update_of_ne hji]⟩,
      by simp⟩

end Pi

section BooleanAlgebra
variable [BooleanAlgebra α] {a b : α}

@[simp] lemma isAtom_compl : IsAtom aᶜ ↔ IsCoatom a := isCompl_compl.symm.isAtom_iff_isCoatom
@[simp] lemma isCoatom_compl : IsCoatom aᶜ ↔ IsAtom a := isCompl_compl.symm.isCoatom_iff_isAtom

protected alias ⟨IsAtom.of_compl, IsCoatom.compl⟩ := isAtom_compl
protected alias ⟨IsCoatom.of_compl, IsAtom.compl⟩ := isCoatom_compl

end BooleanAlgebra

namespace Set

theorem isAtom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩

theorem isAtom_iff {s : Set α} : IsAtom s ↔ ∃ x, s = {x} := by
  refine
    ⟨?_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [isAtom_iff_le_of_ge, bot_eq_empty, ← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩

theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  rw [isCompl_compl.isCoatom_iff_isAtom, isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]

theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

instance : IsAtomistic (Set α) := inferInstance

instance : IsCoatomistic (Set α) := inferInstance

end Set
