/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
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

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, _⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩

theorem IsAtom.of_isAtom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.prop⟩ hba)⟩

theorem isAtom_iff {a : α} : IsAtom a ↔ a ≠ ⊥ ∧ ∀ (b) (_ : b ≠ ⊥), b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by simp only [Ne.def, @not_imp_comm (b = ⊥), not_imp, lt_iff_le_not_le]

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun _ => h.le_iff

@[simp]
theorem bot_covby_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [Covby, bot_lt_iff_ne_bot, IsAtom, not_imp_not]

alias ⟨Covby.is_atom, IsAtom.bot_covby⟩ := bot_covby_iff

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

@[simp]
theorem isCoatom_dual_iff_isAtom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl

@[simp]
theorem isAtom_dual_iff_isCoatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl

alias ⟨_, IsAtom.dual⟩ := isCoatom_dual_iff_isAtom

alias ⟨_, IsCoatom.dual⟩ := isAtom_dual_iff_isCoatom

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.Iic hax

theorem IsCoatom.of_isCoatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_isAtom_coe_Iic αᵒᵈ _ _ x a ha

theorem isCoatom_iff {a : α} : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ (b) (_ : b ≠ ⊤), a ≤ b → b ≤ a :=
  @isAtom_iff αᵒᵈ _ _ _

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderTop α] {a b x : α}

theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff

theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq

@[simp]
theorem covby_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  toDual_covby_toDual_iff.symm.trans bot_covby_iff

alias ⟨Covby.is_coatom, IsCoatom.covby_top⟩ := covby_top_iff

end PartialOrder

theorem iInf_le_coatom [Order.Coframe α] (ha : IsCoatom a) {f : ι → α} :
    iInf f ≤ a ↔ ∃ i, f i ≤ a :=
  atom_le_iSup (α := αᵒᵈ) ha

end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
theorem Set.Ici.isAtom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b := by
  rw [← bot_covby_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Ici

@[simp]
theorem Set.Iic.isCoatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b := by
  rw [← covby_top_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ordConnected_Iic

theorem covby_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp

theorem covby_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp

end PartialOrder

section Pairwise

theorem IsAtom.inf_eq_bot_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : a ⊓ b = ⊥ :=
  hab.not_le_or_not_le.elim (ha.lt_iff.1 ∘ inf_lt_left.2) (hb.lt_iff.1 ∘ inf_lt_right.2)

theorem IsAtom.disjoint_of_ne [SemilatticeInf α] [OrderBot α] {a b : α} (ha : IsAtom a)
    (hb : IsAtom b) (hab : a ≠ b) : Disjoint a b :=
  disjoint_iff.mpr (IsAtom.inf_eq_bot_of_ne ha hb hab)

theorem IsCoatom.sup_eq_top_of_ne [SemilatticeSup α] [OrderTop α] {a b : α} (ha : IsCoatom a)
    (hb : IsCoatom b) (hab : a ≠ b) : a ⊔ b = ⊤ :=
  ha.dual.inf_eq_bot_of_ne hb.dual hab

end Pairwise

end Atoms

section Atomic

variable [PartialOrder α] (α)

/-- A lattice is atomic iff every element other than `⊥` has an atom below it. -/
@[mk_iff]
class IsAtomic [OrderBot α] : Prop where
  /--Every element other than `⊥` has an atom below it. -/
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
class IsCoatomic [OrderTop α] : Prop where
  /--Every element other than `⊤` has an atom above it. -/
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

variable {α}

@[simp]
theorem isCoatomic_dual_iff_isAtomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩

@[simp]
theorem isAtomic_dual_iff_isCoatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

instance isCoatomic_dual : IsCoatomic αᵒᵈ :=
  isCoatomic_dual_iff_isAtomic.2 ‹IsAtomic α›

instance Set.Iic.isAtomic {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.Iic (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

instance isCoatomic : IsAtomic αᵒᵈ :=
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
  isAtomic_dual_iff_isCoatomic.symm.trans <|
    isAtomic_iff_forall_isAtomic_Iic.trans <|
      forall_congr' fun _ => isCoatomic_dual_iff_isAtomic.symm.trans Iff.rfl

section WellFounded

theorem isAtomic_of_orderBot_wellFounded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  ⟨fun a =>
    or_iff_not_imp_left.2 fun ha =>
      let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩
      ⟨b, ⟨hb.1, fun c => not_imp_not.1 fun hc hl => hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩

theorem isCoatomic_of_orderTop_gt_wellFounded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  isAtomic_dual_iff_isCoatomic.1 (@isAtomic_of_orderBot_wellFounded_lt αᵒᵈ _ _ h)

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
  /--Every element is a `sSup` of a set of atoms. -/
  eq_sSup_atoms : ∀ b : α, ∃ s : Set α, b = sSup s ∧ ∀ a, a ∈ s → IsAtom a

/-- A lattice is coatomistic iff every element is an `sInf` of a set of coatoms. -/
class IsCoatomistic : Prop where
  /--Every element is a `sInf` of a set of coatoms. -/
  eq_sInf_coatoms : ∀ b : α, ∃ s : Set α, b = sInf s ∧ ∀ a, a ∈ s → IsCoatom a

export IsAtomistic (eq_sSup_atoms)

export IsCoatomistic (eq_sInf_coatoms)

variable {α}

@[simp]
theorem isCoatomistic_dual_iff_isAtomistic : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_sInf_coatoms⟩, fun h => ⟨fun b => by apply h.eq_sSup_atoms⟩⟩

@[simp]
theorem isAtomistic_dual_iff_isCoatomistic : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_sSup_atoms⟩, fun h => ⟨fun b => by apply h.eq_sInf_coatoms⟩⟩

namespace IsAtomistic

instance isCoatomistic_dual [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  isCoatomistic_dual_iff_isAtomistic.2 h

variable [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases eq_sSup_atoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.choose_spec, le_sSup h.choose_spec⟩⟩

end IsAtomistic

section IsAtomistic

variable [IsAtomistic α]

@[simp]
theorem sSup_atoms_le_eq (b : α) : sSup { a : α | IsAtom a ∧ a ≤ b } = b := by
  rcases eq_sSup_atoms b with ⟨s, rfl, hs⟩
  exact le_antisymm (sSup_le fun _ => And.right) (sSup_le_sSup fun a ha => ⟨hs a ha, le_sSup ha⟩)

@[simp]
theorem sSup_atoms_eq_top : sSup { a : α | IsAtom a } = ⊤ := by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (sSup_atoms_le_eq ⊤)
  exact (and_iff_left le_top).symm

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c _ ca => le_trans ca ab, fun h => by
    rw [← sSup_atoms_le_eq a, ← sSup_atoms_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

theorem eq_iff_atom_le_iff {a b : α} : a = b ↔ ∀ c, IsAtom c → (c ≤ a ↔ c ≤ b) := by
  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  exact le_antisymm (le_iff_atom_le_imp.2 fun a ha hx => (h a ha).1 hx)
    (le_iff_atom_le_imp.2 fun a ha hy => (h a ha).2 hy)

end IsAtomistic

namespace IsCoatomistic

instance isAtomistic_dual [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  isAtomistic_dual_iff_isCoatomistic.2 h

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases eq_sInf_coatoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
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
    by_cases (⨅ a, b ⊓ cond (g a) a (aᶜ)) = ⊥; case pos => simp [h]
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

theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) := by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first |simpa|simpa using h.symm

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : IsSimpleOrder αᵒᵈ :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.1 (by infer_instance)

/-- A simple `BoundedOrder` induces a preorder. This is not an instance to prevent loops. -/
protected def IsSimpleOrder.preorder {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : Preorder α
    where
  le := (· ≤ ·)
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
    decidableLE := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left
              (eq_bot_or_eq_top a) ha)) H)) }

@[simp]
theorem isAtom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

@[simp]
theorem isCoatom_bot : IsCoatom (⊥ : α) :=
  isAtom_dual_iff_isCoatom.1 isAtom_top

theorem bot_covby_top : (⊥ : α) ⋖ ⊤ :=
  isAtom_top.bot_covby

end IsSimpleOrder

namespace IsSimpleOrder

section Preorder

variable [Preorder α] [BoundedOrder α] [IsSimpleOrder α] {a b : α} (h : a < b)

theorem eq_bot_of_lt : a = ⊥ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right h.ne_top

theorem eq_top_of_lt : b = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left h.ne_bot

alias LT.lt.eq_bot := eq_bot_of_lt

alias LT.lt.eq_top := eq_top_of_lt

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
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool
    where
  toFun x := x = ⊤
  invFun x := x.casesOn ⊥ ⊤
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]

/-- Every simple lattice over a partial order is order-isomorphic to `Bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := @fun a b => by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [bot_ne_top]
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, bot_ne_top, Bool.false_lt_true]
        · simp [bot_ne_top] }

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

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open Classical

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

/-- A simple `BoundedOrder` is also a `CompleteBooleanAlgebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { IsSimpleOrder.completeLattice,
    IsSimpleOrder.booleanAlgebra with
    iInf_sup_le_sup_sInf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [bot_sup_eq, ← sInf_eq_iInf]
        exact le_rfl
      · simp only [top_le_iff, top_sup_eq, iInf_top, le_sInf_iff, le_refl]
    inf_sSup_le_iSup_inf := fun x s => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [le_bot_iff, sSup_eq_bot, bot_inf_eq, iSup_bot, le_refl]
      · simp only [top_inf_eq, ← sSup_eq_iSup]
        exact le_rfl }

end IsSimpleOrder

namespace IsSimpleOrder

variable [CompleteLattice α] [IsSimpleOrder α]

--set_option default_priority 100 --Porting note: not supported, done for each instance individually

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

theorem isSimpleOrder_iff_isCoatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  isSimpleOrder_iff_isSimpleOrder_orderDual.trans isSimpleOrder_iff_isAtom_top

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
  simp only [← bot_covby_iff] at hb ⊢
  exact Covby.of_image f (hbot.symm ▸ hb)

theorem isCoatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.isAtom_of_map_bot_of_image htop hb

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
  refine' ⟨fun hla => _, fun ha => gi.isAtom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
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
  refine' ⟨fun hb => gi.isCoatom_of_image hb, fun hb => _⟩
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
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.isAtom_of_u_bot hbot hb.dual

theorem isCoatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.isAtom_iff htop h_coatom b

theorem isCoatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.isAtom_iff' htop h_coatom a

theorem isAtom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.isCoatom_of_image hb.dual

theorem isAtom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.isCoatom_iff h_atom a

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
  f.dual.isAtom_iff a

theorem isSimpleOrder_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [isSimpleOrder_iff_isAtom_top, isSimpleOrder_iff_isAtom_top, ← f.isAtom_iff ⊤,
    f.map_top]

theorem isSimpleOrder [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.isSimpleOrder_iff.mpr h

protected theorem isAtomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) :
    IsAtomic α ↔ IsAtomic β := by
  simp only [IsAtomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.isAtom_iff]

protected theorem isCoatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← isAtomic_dual_iff_isCoatomic, f.dual.isAtomic_iff]

end OrderIso

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)

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
      refine' ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_isCoatom_coe_Ici _, xb⟩
      rw [← hb.isAtom_iff_isCoatom, OrderIso.isAtom_iff]
      apply ha.Iic⟩

theorem isAtomic_of_isCoatomic_of_complementedLattice_of_isModular [IsCoatomic α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.1 isCoatomic_of_isAtomic_of_complementedLattice_of_isModular

theorem isAtomic_iff_isCoatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @isCoatomic_of_isAtomic_of_complementedLattice_of_isModular _ _ _ _ _ h, fun h =>
    @isAtomic_of_isCoatomic_of_complementedLattice_of_isModular _ _ _ _ _ h⟩

end IsModularLattice

namespace «Prop»

@[simp] theorem isAtom_iff {p : Prop} : IsAtom p ↔ p := by
  simp [IsAtom, show ⊥ = False from rfl, fun q r : Prop => show q < r ↔ _ ∧ _ from .rfl]

@[simp] theorem isCoatom_iff {p : Prop} : IsCoatom p ↔ ¬ p := by
  simp [IsCoatom, show ⊤ = True from rfl, fun q r : Prop => show q < r ↔ _ ∧ _ from .rfl]; tauto

instance : IsSimpleOrder Prop where
  eq_bot_or_eq_top p := by by_cases p <;> simp [h] <;> tauto

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
    by_cases hij : j = i; case pos => subst hij; refine hlt _ hgfk
    refine eq_bot_iff.2 <| le_trans (hgf _) (eq_bot_iff.1 (hbot _ hij))
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
      simpa using this (fun k => by by_cases k = j; { subst h; simp }; simp [h]) i
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
    have : DecidableEq ι := open Classical in inferInstance
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
      refine le_sSup ⟨⟨_, ⟨_, _, ha, rfl⟩, ?_⟩, by simp⟩
      intro j; by_cases hij : j = i
      case pos => subst hij; simpa
      case neg => simp [hij]
    case ge =>
      refine sSup_le ?_
      rintro _ ⟨⟨_, ⟨j, a, ha, rfl⟩, hle⟩, rfl⟩
      by_cases hij : i = j; case neg => simp [Function.update_noteq hij]
      subst hij; simp only [Function.update_same]
      exact le_sSup ⟨ha, by simpa using hle i⟩

instance isCoatomistic [∀ i, CompleteLattice (π i)] [∀ i, IsCoatomistic (π i)] :
    IsCoatomistic (∀ i, π i) :=
  isAtomistic_dual_iff_isCoatomistic.1 <|
    show IsAtomistic (∀ i, (π i)ᵒᵈ) from inferInstance

end Pi

namespace Set

theorem isAtom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun _ hs => ssubset_singleton_iff.mp hs⟩

theorem isAtom_iff (s : Set α) : IsAtom s ↔ ∃ x, s = {x} := by
  refine'
    ⟨_, by
      rintro ⟨x, rfl⟩
      exact isAtom_singleton x⟩
  rw [_root_.isAtom_iff, bot_eq_empty, ← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x, eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩

theorem isCoatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  rw [isCompl_compl.isCoatom_iff_isAtom, isAtom_iff]
  simp_rw [@eq_comm _ s, compl_eq_comm]

theorem isCoatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (isCoatom_iff {x}ᶜ).mpr ⟨x, rfl⟩

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
