/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Nontriviality

#align_import order.atoms from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

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

set_option autoImplicit true


variable {α β : Type*}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/-- An atom of an `OrderBot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
#align is_atom IsAtom

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩
#align is_atom.Iic IsAtom.Iic

theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩
#align is_atom.of_is_atom_coe_Iic IsAtom.of_isAtom_coe_Iic

theorem isAtom_iff_le_of_ge : IsAtom a ↔ a ≠ ⊥ ∧ ∀ b ≠ ⊥, b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by
      simp only [Ne, @not_imp_comm (b = ⊥), Classical.not_imp, lt_iff_le_not_le]
#align is_atom_iff isAtom_iff_le_of_ge

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩
#align is_atom.lt_iff IsAtom.lt_iff

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]
#align is_atom.le_iff IsAtom.le_iff

lemma IsAtom.le_iff_eq (ha : IsAtom a) (hb : b ≠ ⊥) : b ≤ a ↔ b = a :=
  ha.le_iff.trans <| or_iff_right hb

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff
#align is_atom.Iic_eq IsAtom.Iic_eq

@[simp]
theorem bot_covBy_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [CovBy, bot_lt_iff_ne_bot, IsAtom, not_imp_not]
#align bot_covby_iff bot_covBy_iff

alias ⟨CovBy.is_atom, IsAtom.bot_covBy⟩ := bot_covBy_iff
#align covby.is_atom CovBy.is_atom
#align is_atom.bot_covby IsAtom.bot_covBy

end PartialOrder

theorem atom_le_iSup [Order.Frame α] (ha : IsAtom a) {f : ι → α} :
    a ≤ iSup f ↔ ∃ i, a ≤ f i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_trans hi (le_iSup _ _)⟩
  show (a ≤ ⨆ i, f i) → _
  refine fun h => of_not_not fun ha' => ?_
  push_neg at ha'
  have ha'' : Disjoint a (⨆ i, f i) :=
    disjoint_iSup_iff.2 fun i => fun x hxa hxf => le_bot_iff.2 <| of_not_not fun hx =>
      have hxa : x < a := (le_iff_eq_or_lt.1 hxa).resolve_left (by rintro rfl; exact ha' _ hxf)
      hx (ha.2 _ hxa)
  obtain rfl := le_bot_iff.1 (ha'' le_rfl h)
  exact ha.1 rfl

end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/-- A coatom of an `OrderTop` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤
#align is_coatom IsCoatom

@[simp]
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl
#align is_coatom_dual_iff_is_atom isCoatom_dual_iff_isAtom

@[simp]
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl
#align is_atom_dual_iff_is_coatom isAtom_dual_iff_isCoatom

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom
#align is_atom.dual IsAtom.dual

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom
#align is_coatom.dual IsCoatom.dual

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax
#align is_coatom.Ici IsCoatom.Ici

theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha
#align is_coatom.of_is_coatom_coe_Ici IsCoatom.of_isCoatom_coe_Ici

theorem isCoatom_iff_ge_of_le : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ b ≠ ⊤, a ≤ b → b ≤ a :=
  isAtom_iff_le_of_ge (α := αᵒᵈ)
#align is_coatom_iff isCoatom_iff_ge_of_le

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff
#align is_coatom.lt_iff IsCoatom.lt_iff

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff
#align is_coatom.le_iff IsCoatom.le_iff

lemma IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b ≠ ⊤) : a ≤ b ↔ b = a := ha.dual.le_iff_eq hb

theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq
#align is_coatom.Ici_eq IsCoatom.Ici_eq

@[simp]
theorem covBy_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covBy_toDual_iff.symm.trans bot_covBy_iff
#align covby_top_iff covBy_top_iff

alias ⟨CovBy.isCoatom, IsCoatom.covBy_top⟩ := covBy_top_iff
#align covby.is_coatom CovBy.isCoatom
#align is_coatom.covby_top IsCoatom.covBy_top

end PartialOrder

theorem iInf_le_coatom [Order.Coframe α] (ha : IsCoatom a) {f : ι → α} :
    iInf f ≤ a ↔ ∃ i, f i ≤ a :=
  atom_le_iSup (α := αᵒᵈ) ha

end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b := by
  rw [← bot_covBy_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) ?_).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Ici
#align set.Ici.is_atom_iff Set.Ici.isAtom_iff

@[simp]
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b := by
  rw [← covBy_top_iff]
  refine (Set.OrdConnected.apply_covBy_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) ?_).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Iic
#align set.Iic.is_coatom_iff Set.Iic.isCoatom_iff

theorem covBy_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp
#align covby_iff_atom_Ici covBy_iff_atom_Ici

theorem covBy_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp
#align covby_iff_coatom_Iic covBy_iff_coatom_Iic

end PartialOrder

section Pairwise

theorem IsAtom.inf_eq_bot_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : a ⊓ b = ⊥ :=
  hab.not_le_or_not_le.elim (ha.lt_iff.1 ∘ inf_lt_left.2) (hb.lt_iff.1 ∘ inf_lt_right.2)
#align is_atom.inf_eq_bot_of_ne IsAtom.inf_eq_bot_of_ne

theorem IsAtom.disjoint_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : Disjoint a b :=
  disjoint_iff.mpr (IsAtom.inf_eq_bot_of_ne ha hb hab)
#align is_atom.disjoint_of_ne IsAtom.disjoint_of_ne

theorem IsCoatom.sup_eq_top_of_ne [SemilatticeSup α] [OrderTop α] {a b : α} (ha : IsCoatom a)
    (hb : IsCoatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
  ha.dual.inf_eq_bot_of_ne hb.dual hab
#align is_coatom.sup_eq_top_of_ne IsCoatom.sup_eq_top_of_ne

end Pairwise

end Atoms

section Atomic

variable [PartialOrder α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
class IsAtomic [OrderBot α] : Prop where
  /-- Every element other than `⊥` has an atom below it. -/
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b
#align is_atomic IsAtomic
#align is_atomic_iff isAtomic_iff

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
class IsCoatomic [OrderTop α] : Prop where
  /-- Every element other than `⊤` has an atom above it. -/
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a
#align is_coatomic IsCoatomic
#align is_coatomic_iff isCoatomic_iff

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
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩
#align is_coatomic_dual_iff_is_atomic isCoatomic_dual_iff_isAtomic

@[simp]
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩
#align is_atomic_dual_iff_is_coatomic isAtomic_dual_iff_isCoatomic

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

instance _root_.OrderDual.instIsCoatomic : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›
#align is_atomic.is_coatomic_dual OrderDual.instIsCoatomic

instance Set.Iic.isAtomic {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩
#align is_atomic.set.Iic.is_atomic IsAtomic.Set.Iic.isAtomic

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

instance _root_.OrderDual.instIsAtomic : IsAtomic αᵒᵈ :=
  isAtomic_dual_iff_isCoatomic.2 ‹IsCoatomic α›
#align is_coatomic.is_coatomic OrderDual.instIsAtomic

instance Set.Ici.isCoatomic {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.Ici (le_trans hy hay), hay⟩⟩
#align is_coatomic.set.Ici.is_coatomic IsCoatomic.Set.Ici.isCoatomic

end IsCoatomic

theorem isAtomic_iff_forall_isAtomic_Iic [OrderBot α] :
    IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.Iic.isAtomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' (↑) fun ⟨_, _⟩ => And.imp_left IsAtom.of_isAtom_coe_Iic)⟩⟩
#align is_atomic_iff_forall_is_atomic_Iic isAtomic_iff_forall_isAtomic_Iic

theorem isCoatomic_iff_forall_isCoatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  isAtomic_dual_iff_isCoatomic.symm.trans <|
    isAtomic_iff_forall_isAtomic_Iic.trans <|
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl
#align is_coatomic_iff_forall_is_coatomic_Ici isCoatomic_iff_forall_isCoatomic_Ici

section WellFounded

theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  ⟨fun a =>
    or_iff_not_imp_left.2 fun ha =>
      let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩
      ⟨b, ⟨hb.1, fun c => not_imp_not.1 fun hc hl => hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩
#align is_atomic_of_order_bot_well_founded_lt isAtomic_of_orderBot_wellFounded_lt

theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)
#align is_coatomic_of_order_top_gt_well_founded isCoatomic_of_orderTop_gt_wellFounded

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

-- See note [reducible non-instances]
abbrev toCompleteAtomicBooleanAlgebra {α} [CompleteBooleanAlgebra α] [IsAtomic α] :
    CompleteAtomicBooleanAlgebra α where
  __ := ‹CompleteBooleanAlgebra α›
  iInf_iSup_eq f := BooleanAlgebra.eq_iff_atom_le_iff.2 fun a ha => by
    simp only [le_iInf_iff, atom_le_iSup ha]
    rw [Classical.skolem]

end CompleteBooleanAlgebra

end Atomic

section Atomistic

variable (α) [CompleteLattice α]

/-- A lattice is atomistic iff every element is a `sSup` of a set of atoms. -/
class IsAtomistic : Prop where
  /-- Every element is a `sSup` of a set of atoms. -/
  eq_sSup_atoms : ∀ b : α, ∃ s : Set α, b = sSup s ∧ ∀ a, a ∈ s → IsAtom a
#align is_atomistic IsAtomistic
#align is_atomistic.eq_Sup_atoms IsAtomistic.eq_sSup_atoms

/-- A lattice is coatomistic iff every element is an `sInf` of a set of coatoms. -/
class IsCoatomistic : Prop where
  /-- Every element is a `sInf` of a set of coatoms. -/
  eq_sInf_coatoms : ∀ b : α, ∃ s : Set α, b = sInf s ∧ ∀ a, a ∈ s → IsCoatom a
#align is_coatomistic IsCoatomistic
#align is_coatomistic.eq_Inf_coatoms IsCoatomistic.eq_sInf_coatoms

export IsAtomistic (eq_sSup_atoms)

export IsCoatomistic (eq_sInf_coatoms)

variable {α}

@[simp]
theorem isCoatomistic_dual_iff_isAtomistic : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_sInf_coatoms⟩, fun h => ⟨fun b => by apply h.eq_sSup_atoms⟩⟩
#align is_coatomistic_dual_iff_is_atomistic isCoatomistic_dual_iff_isAtomistic

@[simp]
theorem isAtomistic_dual_iff_isCoatomistic : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_sSup_atoms⟩, fun h => ⟨fun b => by apply h.eq_sInf_coatoms⟩⟩
#align is_atomistic_dual_iff_is_coatomistic isAtomistic_dual_iff_isCoatomistic

namespace IsAtomistic

instance _root_.OrderDual.instIsCoatomistic [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h
#align is_atomistic.is_coatomistic_dual OrderDual.instIsCoatomistic

variable [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases eq_sSup_atoms b with ⟨s, rfl, hs⟩
    rcases s.eq_empty_or_nonempty with h | h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.choose_spec, le_sSup h.choose_spec⟩⟩

end IsAtomistic

section IsAtomistic

variable [IsAtomistic α]

@[simp]
theorem sSup_atoms_le_eq (b : α) : sSup { a : α | IsAtom a ∧ a ≤ b } = b := by
  rcases eq_sSup_atoms b with ⟨s, rfl, hs⟩
  exact le_antisymm (sSup_le fun _ => And.right) (sSup_le_sSup fun a ha => ⟨hs a ha, le_sSup ha⟩)
#align Sup_atoms_le_eq sSup_atoms_le_eq

@[simp]
theorem sSup_atoms_eq_top : sSup { a : α | IsAtom a } = ⊤ := by
  refine Eq.trans (congr rfl (Set.ext fun x => ?_)) (sSup_atoms_le_eq ⊤)
  exact (and_iff_left le_top).symm
#align Sup_atoms_eq_top sSup_atoms_eq_top

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c _ ca => le_trans ca ab, fun h => by
    rw [← sSup_atoms_le_eq a, ← sSup_atoms_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
#align le_iff_atom_le_imp le_iff_atom_le_imp

theorem eq_iff_atom_le_iff {a b : α} : a = b ↔ ∀ c, IsAtom c → (c ≤ a ↔ c ≤ b) := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

end IsAtomistic

namespace IsCoatomistic

instance _root_.OrderDual.instIsAtomistic [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h
#align is_coatomistic.is_atomistic_dual OrderDual.instIsAtomistic

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases eq_sInf_coatoms b with ⟨s, rfl, hs⟩
    rcases s.eq_empty_or_nonempty with h | h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.choose_spec, sInf_le h.choose_spec⟩⟩

end IsCoatomistic

namespace CompleteAtomicBooleanAlgebra

instance {α} [CompleteAtomicBooleanAlgebra α] : IsAtomistic α where
  eq_sSup_atoms b := by
    inhabit α
    refine ⟨{ a | IsAtom a ∧ a ≤ b }, ?_, fun a ha => ha.1⟩
    refine le_antisymm ?_ (sSup_le fun c hc => hc.2)
    have : (⨅ c : α, ⨆ x, b ⊓ cond x c (cᶜ)) = b := by simp [iSup_bool_eq, iInf_const]
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

end CompleteAtomicBooleanAlgebra

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
class IsSimpleOrder (α : Type*) [LE α] [BoundedOrder α] extends Nontrivial α : Prop where
  /-- Every element is either `⊥` or `⊤` -/
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤
#align is_simple_order IsSimpleOrder

export IsSimpleOrder (eq_bot_or_eq_top)

theorem isSimpleOrder_iff_isSimpleOrder_orderDual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ := by
  constructor <;> intro i <;> haveI := i
  · exact
      { exists_pair_ne := @exists_pair_ne α _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  · exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }
#align is_simple_order_iff_is_simple_order_order_dual isSimpleOrder_iff_isSimpleOrder_orderDual

theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first |simpa|simpa using h.symm
#align is_simple_order.bot_ne_top IsSimpleOrder.bot_ne_top

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance OrderDual.instIsSimpleOrder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    IsSimpleOrder αᵒᵈ := isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

/-- A simple `BoundedOrder` induces a preorder. This is not an instance to prevent loops. -/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Preorder α where
  le := (· ≤ ·)
  le_refl a := by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
  le_trans a b c := by
    rcases eq_bot_or_eq_top a with (rfl | rfl)
    · simp
    · rcases eq_bot_or_eq_top b with (rfl | rfl)
      · rcases eq_bot_or_eq_top c with (rfl | rfl) <;> simp
      · simp
#align is_simple_order.preorder IsSimpleOrder.preorder

/-- A simple partial ordered `BoundedOrder` induces a linear order.
This is not an instance to prevent loops. -/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  { (inferInstance : PartialOrder α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    decidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H)) }
#align is_simple_order.linear_order IsSimpleOrder.linearOrder

@[simp]
theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩
#align is_atom_top isAtom_top

@[simp]
theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top
#align is_coatom_bot isCoatom_bot

theorem bot_covBy_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covBy
#align bot_covby_top bot_covBy_top

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)

theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top
#align is_simple_order.eq_bot_of_lt IsSimpleOrder.eq_bot_of_lt

theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot
#align is_simple_order.eq_top_of_lt IsSimpleOrder.eq_top_of_lt

alias _root_.LT.lt.eq_bot := eq_bot_of_lt
alias _root_.LT.lt.eq_top := eq_top_of_lt
@[deprecated (since := "2024-05-29")] alias LT.lt.eq_bot := _root_.LT.lt.eq_bot
@[deprecated (since := "2024-05-29")] alias LT.lt.eq_top := _root_.LT.lt.eq_top

end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `BoundedOrder` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder
#align is_simple_order.lattice IsSimpleOrder.lattice

/-- A lattice that is a `BoundedOrder` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.distrib_lattice IsSimpleOrder.distribLattice

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
#align is_simple_order.equiv_bool IsSimpleOrder.equivBool
#align is_simple_order.equiv_bool_symm_apply IsSimpleOrder.equivBool_symm_apply
#align is_simple_order.equiv_bool_apply IsSimpleOrder.equivBool_apply

/-- Every simple lattice over a partial order is order-isomorphic to `Bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [bot_ne_top]
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, bot_ne_top, Bool.false_lt_true]
        · simp [bot_ne_top] }
#align is_simple_order.order_iso_bool IsSimpleOrder.orderIsoBool

/-- A simple `BoundedOrder` is also a `BooleanAlgebra`. -/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { inferInstanceAs (BoundedOrder α), IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top, SDiff.sdiff, compl]
    inf_compl_le_bot := fun x => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.boolean_algebra IsSimpleOrder.booleanAlgebra

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open scoped Classical

/-- A simple `BoundedOrder` is also complete. -/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder α) with
    sSup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    sInf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    le_sSup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · dsimp; rw [if_pos h]
    sSup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · dsimp; rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
      · exact le_top
    sInf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · dsimp; rw [if_pos h]
      · exact le_top
    le_sInf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · dsimp; rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }
#align is_simple_order.complete_lattice IsSimpleOrder.completeLattice

/-- A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { __ := IsSimpleOrder.completeLattice
    __ := IsSimpleOrder.booleanAlgebra
    iInf_sup_le_sup_sInf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp [bot_sup_eq, ← sInf_eq_iInf]
      · simp only [top_le_iff, top_sup_eq, iInf_top, le_sInf_iff, le_refl]
    inf_sSup_le_iSup_inf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [le_bot_iff, sSup_eq_bot, bot_inf_eq, iSup_bot, le_refl]
      · simp only [top_inf_eq, ← sSup_eq_iSup]
        exact le_rfl }
#align is_simple_order.complete_boolean_algebra IsSimpleOrder.completeBooleanAlgebra

instance : ComplementedLattice α :=
  letI := IsSimpleOrder.completeBooleanAlgebra (α := α); inferInstance

end IsSimpleOrder

namespace IsSimpleOrder

variable [CompleteLattice α] [IsSimpleOrder α]

--set_option default_priority 100
-- Porting note: not supported, done for each instance individually

instance (priority := 100) : IsAtomistic α :=
  ⟨fun b =>
    (eq_bot_or_eq_top b).elim
      (fun h => ⟨∅, ⟨h.trans sSup_empty.symm, fun _ ha => False.elim (Set.not_mem_empty _ ha)⟩⟩)
      fun h =>
      ⟨{⊤}, h.trans sSup_singleton.symm, fun _ ha =>
        (Set.mem_singleton_iff.1 ha).symm ▸ isAtom_top⟩⟩

instance : IsCoatomistic α :=
  isAtomistic_dual_iff_isCoatomistic.1 (by infer_instance)

end IsSimpleOrder

theorem isSimpleOrder_iff_isAtom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @isAtom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩
#align is_simple_order_iff_is_atom_top isSimpleOrder_iff_isAtom_top

theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top
#align is_simple_order_iff_is_coatom_bot isSimpleOrder_iff_isCoatom_bot

namespace Set

theorem isSimpleOrder_Iic_iff_isAtom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
  isSimpleOrder_iff_isAtom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Iic_iff_is_atom Set.isSimpleOrder_Iic_iff_isAtom

theorem isSimpleOrder_Ici_iff_isCoatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  isSimpleOrder_iff_isCoatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, _⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Ici_iff_is_coatom Set.isSimpleOrder_Ici_iff_isCoatom

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

theorem isAtom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b := by
  simp only [← bot_covBy_iff] at hb ⊢
  exact CovBy.of_image f (hbot.symm ▸ hb)
#align order_embedding.is_atom_of_map_bot_of_image OrderEmbedding.isAtom_of_map_bot_of_image

theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.isAtom_of_map_bot_of_image htop hb
#align order_embedding.is_coatom_of_map_top_of_image OrderEmbedding.isCoatom_of_map_top_of_image

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

theorem isAtom_of_u_bot [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.isAtom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb
#align galois_insertion.is_atom_of_u_bot GaloisInsertion.isAtom_of_u_bot

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
#align galois_insertion.is_atom_iff GaloisInsertion.isAtom_iff

theorem isAtom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.isAtom_iff hbot h_atom, gi.l_u_eq]
#align galois_insertion.is_atom_iff' GaloisInsertion.isAtom_iff'

theorem isCoatom_of_image [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.isCoatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb
#align galois_insertion.is_coatom_of_image GaloisInsertion.isCoatom_of_image

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
#align galois_insertion.is_coatom_iff GaloisInsertion.isCoatom_iff

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

theorem isCoatom_of_l_top [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.isAtom_of_u_bot hbot hb.dual
#align galois_coinsertion.is_coatom_of_l_top GaloisCoinsertion.isCoatom_of_l_top

theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.isAtom_iff htop h_coatom b
#align galois_coinsertion.is_coatom_iff GaloisCoinsertion.isCoatom_iff

theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.isAtom_iff' htop h_coatom a
#align galois_coinsertion.is_coatom_iff' GaloisCoinsertion.isCoatom_iff'

theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.isCoatom_of_image hb.dual
#align galois_coinsertion.is_atom_of_image GaloisCoinsertion.isAtom_of_image

theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.isCoatom_iff h_atom a
#align galois_coinsertion.is_atom_iff GaloisCoinsertion.isAtom_iff

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem isAtom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.isAtom_of_image, fun ha =>
    f.toGaloisInsertion.isAtom_of_u_bot (map_bot f.symm) <| (f.symm_apply_apply a).symm ▸ ha⟩
#align order_iso.is_atom_iff OrderIso.isAtom_iff

@[simp]
theorem isCoatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.isAtom_iff a
#align order_iso.is_coatom_iff OrderIso.isCoatom_iff

theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top, ← f.isAtom_iff ⊤,
    f.map_top]
#align order_iso.is_simple_order_iff OrderIso.isSimpleOrder_iff

theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.isSimpleOrder_iff.mpr h
#align order_iso.is_simple_order OrderIso.isSimpleOrder

protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  simp only [isAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]
#align order_iso.is_atomic_iff OrderIso.isAtomic_iff

protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]
#align order_iso.is_coatomic_iff OrderIso.isCoatomic_iff

end OrderIso

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)

theorem isAtom_iff_isCoatom : IsAtom a ↔ IsCoatom b :=
  Set.isSimpleOrder_Iic_iff_isAtom.symm.trans <|
    hc.IicOrderIsoIci.isSimpleOrder_iff.trans Set.isSimpleOrder_Ici_iff_isCoatom
#align is_compl.is_atom_iff_is_coatom IsCompl.isAtom_iff_isCoatom

theorem isCoatom_iff_isAtom : IsCoatom a ↔ IsAtom b :=
  hc.symm.isAtom_iff_isCoatom.symm
#align is_compl.is_coatom_iff_is_atom IsCompl.isCoatom_iff_isAtom

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
#align is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular
#align is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular isAtomic_of_isCoatomic_of_complementedLattice_of_isModular

theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @isCoatomic_of_isAtomic_of_complementedLattice_of_isModular _ _ _ _ _ h, fun h =>
    @isAtomic_of_isCoatomic_of_complementedLattice_of_isModular _ _ _ _ _ h⟩
#align is_atomic_iff_is_coatomic isAtomic_iff_isCoatomic

end IsModularLattice

namespace «Prop»

@[simp] theorem isAtom_iff {p : Prop} : IsAtom p ↔ p := by
  simp [IsAtom, show ⊥ = False from rfl, fun q r : Prop => show q < r ↔ _ ∧ _ from .rfl]

@[simp] theorem isCoatom_iff {p : Prop} : IsCoatom p ↔ ¬ p := by
  simp [IsCoatom, show ⊤ = True from rfl, fun q r : Prop => show q < r ↔ _ ∧ _ from .rfl]; tauto

instance : IsSimpleOrder Prop where
  eq_bot_or_eq_top p := by simp [em']

end «Prop»

namespace Pi

variable {π : ι → Type u}

protected theorem eq_bot_iff [∀ i, Bot (π i)] {f : ∀ i, π i} : f = ⊥ ↔ ∀ i, f i = ⊥ :=
  ⟨(· ▸ by simp), fun h => funext fun i => by simp [h]⟩

theorem isAtom_iff {f : ∀ i, π i} [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] :
    IsAtom f ↔ ∃ i, IsAtom (f i) ∧ ∀ j, j ≠ i → f j = ⊥ := by
  classical
  constructor
  case mpr =>
    rintro ⟨i, ⟨hfi, hlt⟩, hbot⟩
    refine ⟨fun h => hfi ((Pi.eq_bot_iff.1 h) _), fun g hgf => Pi.eq_bot_iff.2 fun j => ?_⟩
    have ⟨hgf, k, hgfk⟩ := Pi.lt_def.1 hgf
    obtain rfl : i = k := of_not_not fun hki => by rw [hbot _ (Ne.symm hki)] at hgfk; simp at hgfk
    if hij : j = i then subst hij; refine hlt _ hgfk else
    exact eq_bot_iff.2 <| le_trans (hgf _) (eq_bot_iff.1 (hbot _ hij))
  case mp =>
    rintro ⟨hbot, h⟩
    have ⟨i, hbot⟩ : ∃ i, f i ≠ ⊥ := by rw [ne_eq, Pi.eq_bot_iff, not_forall] at hbot; exact hbot
    refine ⟨i, ⟨hbot, ?c⟩, ?d⟩
    case c =>
      intro b hb
      have := h (Function.update ⊥ i b)
      simp only [lt_def, le_def, ge_iff_le, Pi.eq_bot_iff, and_imp, forall_exists_index] at this
      simpa using this
        (fun j => by by_cases h : j = i; { subst h; simpa using le_of_lt hb }; simp [h])
        i (by simpa using hb) i
    case d =>
      intro j hj
      have := h (Function.update ⊥ j (f j))
      simp only [lt_def, le_def, ge_iff_le, Pi.eq_bot_iff, and_imp, forall_exists_index] at this
      simpa using this (fun k => by by_cases h : k = j; { subst h; simp }; simp [h]) i
        (by rwa [Function.update_noteq (Ne.symm hj), bot_apply, bot_lt_iff_ne_bot]) j

theorem isAtom_single [DecidableEq ι] [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] {a : π i}
    (h : IsAtom a) : IsAtom (Function.update (⊥ : ∀ i, π i) i a) :=
  isAtom_iff.2 ⟨i, by simpa, fun j hji => Function.update_noteq hji _ _⟩

theorem isAtom_iff_eq_single [DecidableEq ι] [∀ i, PartialOrder (π i)]
    [∀ i, OrderBot (π i)] {f : ∀ i, π i} :
    IsAtom f ↔ ∃ i a, IsAtom a ∧ f = Function.update ⊥ i a := by
  constructor
  case mp =>
    intro h
    have ⟨i, h, hbot⟩ := isAtom_iff.1 h
    refine ⟨_, _, h, funext fun j => if hij : j = i then hij ▸ by simp else ?_⟩
    rw [Function.update_noteq hij, hbot _ hij, bot_apply]
  case mpr =>
    rintro ⟨i, a, h, rfl⟩
    exact isAtom_single h

instance isAtomic [∀ i, PartialOrder (π i)] [∀ i, OrderBot (π i)] [∀ i, IsAtomic (π i)] :
    IsAtomic (∀ i, π i) where
  eq_bot_or_exists_atom_le b := or_iff_not_imp_left.2 fun h =>
    have ⟨i, hi⟩ : ∃ i, b i ≠ ⊥ := not_forall.1 (h.imp Pi.eq_bot_iff.2)
    have ⟨a, ha, hab⟩ := (eq_bot_or_exists_atom_le (b i)).resolve_left hi
    have : DecidableEq ι := open scoped Classical in inferInstance
    ⟨Function.update ⊥ i a, isAtom_single ha, update_le_iff.2 ⟨hab, by simp⟩⟩

instance isCoatomic [∀ i, PartialOrder (π i)] [∀ i, OrderTop (π i)] [∀ i, IsCoatomic (π i)] :
    IsCoatomic (∀ i, π i) :=
  isAtomic_dual_iff_isCoatomic.1 <|
    show IsAtomic (∀ i, (π i)ᵒᵈ) from inferInstance

instance isAtomistic [∀ i, CompleteLattice (π i)] [∀ i, IsAtomistic (π i)] :
    IsAtomistic (∀ i, π i) where
  eq_sSup_atoms s := by
    classical
    refine ⟨{ f | IsAtom f ∧ f ≤ s }, ?_, by simp; tauto⟩
    ext i
    rw [← sSup_atoms_le_eq (s i)]
    simp_rw [isAtom_iff_eq_single]
    refine le_antisymm ?le ?ge
    case le =>
      refine sSup_le fun a ⟨ha, hle⟩ => ?_
      refine le_sSup ⟨⟨_, ⟨_, _, ha, rfl⟩, fun j => ?_⟩, by simp⟩
      if hij : j = i then subst hij; simpa else simp [hij]
    case ge =>
      refine sSup_le ?_
      rintro _ ⟨⟨_, ⟨j, a, ha, rfl⟩, hle⟩, rfl⟩
      if hij : i = j then ?_ else simp [Function.update_noteq hij]
      subst hij; simp only [Function.update_same]
      exact le_sSup ⟨ha, by simpa using hle i⟩

instance isCoatomistic [∀ i, CompleteLattice (π i)] [∀ i, IsCoatomistic (π i)] :
    IsCoatomistic (∀ i, π i) :=
  isAtomistic_dual_iff_isCoatomistic.1 <|
    show IsAtomistic (∀ i, (π i)ᵒᵈ) from inferInstance

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
#align set.is_atom_singleton Set.isAtom_singleton

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
#align set.is_atom_iff Set.isAtom_iff

theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  rw [isCompl_compl.isCoatom_iff_isAtom, isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]
#align set.is_coatom_iff Set.isCoatom_iff

theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩
#align set.is_coatom_singleton_compl Set.isCoatom_singleton_compl

instance : IsAtomistic (Set α) where
  eq_sSup_atoms s :=
    ⟨(fun x => {x}) '' s, by rw [sSup_eq_sUnion, sUnion_image, biUnion_of_singleton],
      by { rintro _ ⟨x, _, rfl⟩
           exact isAtom_singleton x }⟩

instance : IsCoatomistic (Set α) where
  eq_sInf_coatoms s :=
    ⟨(fun x => {x}ᶜ) '' sᶜ,
      by { rw [sInf_eq_sInter, sInter_image, ← compl_iUnion₂, biUnion_of_singleton, compl_compl] },
      by { rintro _ ⟨x, _, rfl⟩
           exact isCoatom_singleton_compl x }⟩

end Set
