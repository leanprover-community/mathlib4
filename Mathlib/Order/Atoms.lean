/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module order.atoms
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.ModularLattice
import Mathlib.Order.WellFounded

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Atomic and Atomistic Lattices
  * `is_atomic` indicates that every element other than `⊥` is above an atom.
  * `is_coatomic` indicates that every element other than `⊤` is below a coatom.
  * `is_atomistic` indicates that every element is the `Sup` of a set of atoms.
  * `is_coatomistic` indicates that every element is the `Inf` of a set of coatoms.

### Simple Lattices
  * `is_simple_order` indicates that an order has only two unique elements, `⊥` and `⊤`.
  * `is_simple_order.bounded_order`
  * `is_simple_order.distrib_lattice`
  * Given an instance of `is_simple_order`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_order.boolean_algebra`
    * `is_simple_order.complete_lattice`
    * `is_simple_order.complete_boolean_algebra`

## Main results
  * `is_atom_dual_iff_is_coatom` and `is_coatom_dual_iff_is_atom` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_order_iff_is_atom_top` and `is_simple_order_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices
  * `is_compl.is_atom_iff_is_coatom` and `is_compl.is_coatom_if_is_atom`: In a modular
  bounded lattice, a complement of an atom is a coatom and vice versa.
  * `is_atomic_iff_is_coatomic`: A modular complemented lattice is atomic iff it is coatomic.

-/


variable {α β : Type _}

section Atoms

section IsAtom

section Preorder

variable [Preorder α] [OrderBot α] {a b x : α}

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def IsAtom (a : α) : Prop :=
  a ≠ ⊥ ∧ ∀ b, b < a → b = ⊥
#align is_atom IsAtom

theorem IsAtom.Iic (ha : IsAtom a) (hax : a ≤ x) : IsAtom (⟨a, hax⟩ : Set.Iic x) :=
  ⟨fun con => ha.1 (Subtype.mk_eq_mk.1 con), fun ⟨b, hb⟩ hba => Subtype.mk_eq_mk.2 (ha.2 b hba)⟩
#align is_atom.Iic IsAtom.Iic

theorem IsAtom.of_is_atom_coe_Iic {a : Set.Iic x} (ha : IsAtom a) : IsAtom (a : α) :=
  ⟨fun con => ha.1 (Subtype.ext con), fun b hba =>
    Subtype.mk_eq_mk.1 (ha.2 ⟨b, hba.le.trans a.Prop⟩ hba)⟩
#align is_atom.of_is_atom_coe_Iic IsAtom.of_is_atom_coe_Iic

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (b «expr ≠ » «expr⊥»()) -/
theorem is_atom_iff {a : α} : IsAtom a ↔ a ≠ ⊥ ∧ ∀ (b) (_ : b ≠ ⊥), b ≤ a → a ≤ b :=
  and_congr Iff.rfl <|
    forall_congr' fun b => by simp only [Ne.def, @not_imp_comm (b = ⊥), not_imp, lt_iff_le_not_le]
#align is_atom_iff is_atom_iff

end Preorder

variable [PartialOrder α] [OrderBot α] {a b x : α}

theorem IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ :=
  ⟨h.2 x, fun hx => hx.symm ▸ h.1.bot_lt⟩
#align is_atom.lt_iff IsAtom.lt_iff

theorem IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by rw [le_iff_lt_or_eq, h.lt_iff]
#align is_atom.le_iff IsAtom.le_iff

theorem IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a} :=
  Set.ext fun x => h.le_iff
#align is_atom.Iic_eq IsAtom.Iic_eq

@[simp]
theorem bot_covby_iff : ⊥ ⋖ a ↔ IsAtom a := by
  simp only [Covby, bot_lt_iff_ne_bot, IsAtom, not_imp_not]
#align bot_covby_iff bot_covby_iff

alias bot_covby_iff ↔ Covby.is_atom IsAtom.bot_covby

end IsAtom

section IsCoatom

section Preorder

variable [Preorder α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def IsCoatom [OrderTop α] (a : α) : Prop :=
  a ≠ ⊤ ∧ ∀ b, a < b → b = ⊤
#align is_coatom IsCoatom

@[simp]
theorem is_coatom_dual_iff_is_atom [OrderBot α] {a : α} :
    IsCoatom (OrderDual.toDual a) ↔ IsAtom a :=
  Iff.rfl
#align is_coatom_dual_iff_is_atom is_coatom_dual_iff_is_atom

@[simp]
theorem is_atom_dual_iff_is_coatom [OrderTop α] {a : α} :
    IsAtom (OrderDual.toDual a) ↔ IsCoatom a :=
  Iff.rfl
#align is_atom_dual_iff_is_coatom is_atom_dual_iff_is_coatom

alias is_coatom_dual_iff_is_atom ↔ _ IsAtom.dual

alias is_atom_dual_iff_is_coatom ↔ _ IsCoatom.dual

variable [OrderTop α] {a x : α}

theorem IsCoatom.Ici (ha : IsCoatom a) (hax : x ≤ a) : IsCoatom (⟨a, hax⟩ : Set.Ici x) :=
  ha.dual.IicCat hax
#align is_coatom.Ici IsCoatom.Ici

theorem IsCoatom.of_is_coatom_coe_Ici {a : Set.Ici x} (ha : IsCoatom a) : IsCoatom (a : α) :=
  @IsAtom.of_is_atom_coe_Iic αᵒᵈ _ _ x a ha
#align is_coatom.of_is_coatom_coe_Ici IsCoatom.of_is_coatom_coe_Ici

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (b «expr ≠ » «expr⊤»()) -/
theorem is_coatom_iff {a : α} : IsCoatom a ↔ a ≠ ⊤ ∧ ∀ (b) (_ : b ≠ ⊤), a ≤ b → b ≤ a :=
  @is_atom_iff αᵒᵈ _ _ _
#align is_coatom_iff is_coatom_iff

end Preorder

variable [PartialOrder α] [OrderTop α] {a b x : α}

theorem IsCoatom.lt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  h.dual.lt_iff
#align is_coatom.lt_iff IsCoatom.lt_iff

theorem IsCoatom.le_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  h.dual.le_iff
#align is_coatom.le_iff IsCoatom.le_iff

theorem IsCoatom.Ici_eq (h : IsCoatom a) : Set.Ici a = {⊤, a} :=
  h.dual.Iic_eq
#align is_coatom.Ici_eq IsCoatom.Ici_eq

@[simp]
theorem covby_top_iff : a ⋖ ⊤ ↔ IsCoatom a :=
  to_dual_covby_to_dual_iff.symm.trans bot_covby_iff
#align covby_top_iff covby_top_iff

alias covby_top_iff ↔ Covby.is_coatom IsCoatom.covby_top

end IsCoatom

section PartialOrder

variable [PartialOrder α] {a b : α}

@[simp]
theorem Set.Ici.is_atom_iff {b : Set.Ici a} : IsAtom b ↔ a ⋖ b :=
  by
  rw [← bot_covby_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => a ≤ c) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ord_connected_Ici
#align set.Ici.is_atom_iff Set.Ici.is_atom_iff

@[simp]
theorem Set.Iic.is_coatom_iff {a : Set.Iic b} : IsCoatom a ↔ ↑a ⋖ b :=
  by
  rw [← covby_top_iff]
  refine' (Set.OrdConnected.apply_covby_apply_iff (OrderEmbedding.subtype fun c => c ≤ b) _).symm
  simpa only [OrderEmbedding.subtype_apply, Subtype.range_coe_subtype] using Set.ord_connected_Iic
#align set.Iic.is_coatom_iff Set.Iic.is_coatom_iff

theorem covby_iff_atom_Ici (h : a ≤ b) : a ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici a) := by simp
#align covby_iff_atom_Ici covby_iff_atom_Ici

theorem covby_iff_coatom_Iic (h : a ≤ b) : a ⋖ b ↔ IsCoatom (⟨a, h⟩ : Set.Iic b) := by simp
#align covby_iff_coatom_Iic covby_iff_coatom_Iic

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
  eq_bot_or_exists_atom_le : ∀ b : α, b = ⊥ ∨ ∃ a : α, IsAtom a ∧ a ≤ b
#align is_atomic IsAtomic

/-- A lattice is coatomic iff every element other than `⊤` has a coatom above it. -/
@[mk_iff]
class IsCoatomic [OrderTop α] : Prop where
  eq_top_or_exists_le_coatom : ∀ b : α, b = ⊤ ∨ ∃ a : α, IsCoatom a ∧ b ≤ a
#align is_coatomic IsCoatomic

export IsAtomic (eq_bot_or_exists_atom_le)

export IsCoatomic (eq_top_or_exists_le_coatom)

variable {α}

@[simp]
theorem is_coatomic_dual_iff_is_atomic [OrderBot α] : IsCoatomic αᵒᵈ ↔ IsAtomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩, fun h =>
    ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩⟩
#align is_coatomic_dual_iff_is_atomic is_coatomic_dual_iff_is_atomic

@[simp]
theorem is_atomic_dual_iff_is_coatomic [OrderTop α] : IsAtomic αᵒᵈ ↔ IsCoatomic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_bot_or_exists_atom_le⟩, fun h =>
    ⟨fun b => by apply h.eq_top_or_exists_le_coatom⟩⟩
#align is_atomic_dual_iff_is_coatomic is_atomic_dual_iff_is_coatomic

namespace IsAtomic

variable [OrderBot α] [IsAtomic α]

instance is_coatomic_dual : IsCoatomic αᵒᵈ :=
  is_coatomic_dual_iff_is_atomic.2 ‹IsAtomic α›
#align is_atomic.is_coatomic_dual IsAtomic.is_coatomic_dual

instance {x : α} : IsAtomic (Set.Iic x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_bot_or_exists_atom_le y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, hay.trans hy⟩, ha.IicCat (hay.trans hy), hay⟩⟩

end IsAtomic

namespace IsCoatomic

variable [OrderTop α] [IsCoatomic α]

instance is_coatomic : IsAtomic αᵒᵈ :=
  is_atomic_dual_iff_is_coatomic.2 ‹IsCoatomic α›
#align is_coatomic.is_coatomic IsCoatomic.is_coatomic

instance {x : α} : IsCoatomic (Set.Ici x) :=
  ⟨fun ⟨y, hy⟩ =>
    (eq_top_or_exists_le_coatom y).imp Subtype.mk_eq_mk.2 fun ⟨a, ha, hay⟩ =>
      ⟨⟨a, le_trans hy hay⟩, ha.IciCat (le_trans hy hay), hay⟩⟩

end IsCoatomic

theorem is_atomic_iff_forall_is_atomic_Iic [OrderBot α] :
    IsAtomic α ↔ ∀ x : α, IsAtomic (Set.Iic x) :=
  ⟨@IsAtomic.Set.IicCat.is_atomic _ _ _, fun h =>
    ⟨fun x =>
      ((@eq_bot_or_exists_atom_le _ _ _ (h x)) (⊤ : Set.Iic x)).imp Subtype.mk_eq_mk.1
        (Exists.imp' coe fun ⟨a, ha⟩ => And.imp_left IsAtom.of_is_atom_coe_Iic)⟩⟩
#align is_atomic_iff_forall_is_atomic_Iic is_atomic_iff_forall_is_atomic_Iic

theorem is_coatomic_iff_forall_is_coatomic_Ici [OrderTop α] :
    IsCoatomic α ↔ ∀ x : α, IsCoatomic (Set.Ici x) :=
  is_atomic_dual_iff_is_coatomic.symm.trans <|
    is_atomic_iff_forall_is_atomic_Iic.trans <|
      forall_congr' fun x => is_coatomic_dual_iff_is_atomic.symm.trans Iff.rfl
#align is_coatomic_iff_forall_is_coatomic_Ici is_coatomic_iff_forall_is_coatomic_Ici

section WellFounded

theorem is_atomic_of_order_bot_well_founded_lt [OrderBot α]
    (h : WellFounded ((· < ·) : α → α → Prop)) : IsAtomic α :=
  ⟨fun a =>
    or_iff_not_imp_left.2 fun ha =>
      let ⟨b, hb, hm⟩ := h.has_min { b | b ≠ ⊥ ∧ b ≤ a } ⟨a, ha, le_rfl⟩
      ⟨b, ⟨hb.1, fun c => not_imp_not.1 fun hc hl => hm c ⟨hc, hl.le.trans hb.2⟩ hl⟩, hb.2⟩⟩
#align is_atomic_of_order_bot_well_founded_lt is_atomic_of_order_bot_well_founded_lt

theorem is_coatomic_of_order_top_gt_well_founded [OrderTop α]
    (h : WellFounded ((· > ·) : α → α → Prop)) : IsCoatomic α :=
  is_atomic_dual_iff_is_coatomic.1 (@is_atomic_of_order_bot_well_founded_lt αᵒᵈ _ _ h)
#align is_coatomic_of_order_top_gt_well_founded is_coatomic_of_order_top_gt_well_founded

end WellFounded

end Atomic

section Atomistic

variable (α) [CompleteLattice α]

/-- A lattice is atomistic iff every element is a `Sup` of a set of atoms. -/
class IsAtomistic : Prop where
  eq_Sup_atoms : ∀ b : α, ∃ s : Set α, b = supₛ s ∧ ∀ a, a ∈ s → IsAtom a
#align is_atomistic IsAtomistic

/-- A lattice is coatomistic iff every element is an `Inf` of a set of coatoms. -/
class IsCoatomistic : Prop where
  eq_Inf_coatoms : ∀ b : α, ∃ s : Set α, b = infₛ s ∧ ∀ a, a ∈ s → IsCoatom a
#align is_coatomistic IsCoatomistic

export IsAtomistic (eq_Sup_atoms)

export IsCoatomistic (eq_Inf_coatoms)

variable {α}

@[simp]
theorem is_coatomistic_dual_iff_is_atomistic : IsCoatomistic αᵒᵈ ↔ IsAtomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_Inf_coatoms⟩, fun h => ⟨fun b => by apply h.eq_Sup_atoms⟩⟩
#align is_coatomistic_dual_iff_is_atomistic is_coatomistic_dual_iff_is_atomistic

@[simp]
theorem is_atomistic_dual_iff_is_coatomistic : IsAtomistic αᵒᵈ ↔ IsCoatomistic α :=
  ⟨fun h => ⟨fun b => by apply h.eq_Sup_atoms⟩, fun h => ⟨fun b => by apply h.eq_Inf_coatoms⟩⟩
#align is_atomistic_dual_iff_is_coatomistic is_atomistic_dual_iff_is_coatomistic

namespace IsAtomistic

instance is_coatomistic_dual [h : IsAtomistic α] : IsCoatomistic αᵒᵈ :=
  is_coatomistic_dual_iff_is_atomistic.2 h
#align is_atomistic.is_coatomistic_dual IsAtomistic.is_coatomistic_dual

variable [IsAtomistic α]

instance (priority := 100) : IsAtomic α :=
  ⟨fun b => by
    rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.some_spec, le_supₛ h.some_spec⟩⟩

end IsAtomistic

section IsAtomistic

variable [IsAtomistic α]

@[simp]
theorem Sup_atoms_le_eq (b : α) : supₛ { a : α | IsAtom a ∧ a ≤ b } = b :=
  by
  rcases eq_Sup_atoms b with ⟨s, rfl, hs⟩
  exact le_antisymm (supₛ_le fun _ => And.right) (supₛ_le_supₛ fun a ha => ⟨hs a ha, le_supₛ ha⟩)
#align Sup_atoms_le_eq Sup_atoms_le_eq

@[simp]
theorem Sup_atoms_eq_top : supₛ { a : α | IsAtom a } = ⊤ :=
  by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (Sup_atoms_le_eq ⊤)
  exact (and_iff_left le_top).symm
#align Sup_atoms_eq_top Sup_atoms_eq_top

theorem le_iff_atom_le_imp {a b : α} : a ≤ b ↔ ∀ c : α, IsAtom c → c ≤ a → c ≤ b :=
  ⟨fun ab c hc ca => le_trans ca ab, fun h =>
    by
    rw [← Sup_atoms_le_eq a, ← Sup_atoms_le_eq b]
    exact supₛ_le_supₛ fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
#align le_iff_atom_le_imp le_iff_atom_le_imp

end IsAtomistic

namespace IsCoatomistic

instance is_atomistic_dual [h : IsCoatomistic α] : IsAtomistic αᵒᵈ :=
  is_atomistic_dual_iff_is_coatomistic.2 h
#align is_coatomistic.is_atomistic_dual IsCoatomistic.is_atomistic_dual

variable [IsCoatomistic α]

instance (priority := 100) : IsCoatomic α :=
  ⟨fun b => by
    rcases eq_Inf_coatoms b with ⟨s, rfl, hs⟩
    cases' s.eq_empty_or_nonempty with h h
    · simp [h]
    · exact Or.intro_right _ ⟨h.some, hs _ h.some_spec, infₛ_le h.some_spec⟩⟩

end IsCoatomistic

end Atomistic

/-- An order is simple iff it has exactly two elements, `⊥` and `⊤`. -/
class IsSimpleOrder (α : Type _) [LE α] [BoundedOrder α] extends Nontrivial α : Prop where
  eq_bot_or_eq_top : ∀ a : α, a = ⊥ ∨ a = ⊤
#align is_simple_order IsSimpleOrder

export IsSimpleOrder (eq_bot_or_eq_top)

theorem is_simple_order_iff_is_simple_order_order_dual [LE α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsSimpleOrder αᵒᵈ :=
  by
  constructor <;> intro i <;> haveI := i
  ·
    exact
      { exists_pair_ne := @exists_pair_ne α _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.ofDual a) : _ ∨ _) }
  ·
    exact
      { exists_pair_ne := @exists_pair_ne αᵒᵈ _
        eq_bot_or_eq_top := fun a => Or.symm (eq_bot_or_eq_top (OrderDual.toDual a)) }
#align is_simple_order_iff_is_simple_order_order_dual is_simple_order_iff_is_simple_order_order_dual

theorem IsSimpleOrder.bot_ne_top [LE α] [BoundedOrder α] [IsSimpleOrder α] : (⊥ : α) ≠ (⊤ : α) :=
  by
  obtain ⟨a, b, h⟩ := exists_pair_ne α
  rcases eq_bot_or_eq_top a with (rfl | rfl) <;> rcases eq_bot_or_eq_top b with (rfl | rfl) <;>
    first |simpa|simpa using h.symm
#align is_simple_order.bot_ne_top IsSimpleOrder.bot_ne_top

section IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

instance {α} [LE α] [BoundedOrder α] [IsSimpleOrder α] : IsSimpleOrder αᵒᵈ :=
  is_simple_order_iff_is_simple_order_order_dual.1 (by infer_instance)

/-- A simple `bounded_order` induces a preorder. This is not an instance to prevent loops. -/
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
#align is_simple_order.preorder IsSimpleOrder.preorder

/-- A simple partial ordered `bounded_order` induces a linear order.
This is not an instance to prevent loops. -/
protected def IsSimpleOrder.linearOrder [DecidableEq α] : LinearOrder α :=
  {
    (inferInstance :
      PartialOrder
        α) with
    le_total := fun a b => by rcases eq_bot_or_eq_top a with (rfl | rfl) <;> simp
    decidableLe := fun a b =>
      if ha : a = ⊥ then isTrue (ha.le.trans bot_le)
      else
        if hb : b = ⊤ then isTrue (le_top.trans hb.ge)
        else
          isFalse fun H =>
            hb (top_unique (le_trans (top_le_iff.mpr (Or.resolve_left (eq_bot_or_eq_top a) ha)) H))
    DecidableEq := by assumption }
#align is_simple_order.linear_order IsSimpleOrder.linearOrder

@[simp]
theorem is_atom_top : IsAtom (⊤ : α) :=
  ⟨top_ne_bot, fun a ha => Or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩
#align is_atom_top is_atom_top

@[simp]
theorem is_coatom_bot : IsCoatom (⊥ : α) :=
  is_atom_dual_iff_is_coatom.1 is_atom_top
#align is_coatom_bot is_coatom_bot

theorem bot_covby_top : (⊥ : α) ⋖ ⊤ :=
  is_atom_top.bot_covby
#align bot_covby_top bot_covby_top

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

alias eq_bot_of_lt ← has_lt.lt.eq_bot

alias eq_top_of_lt ← has_lt.lt.eq_top

end Preorder

section BoundedOrder

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

/-- A simple partial ordered `bounded_order` induces a lattice.
This is not an instance to prevent loops -/
protected def lattice {α} [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] :
    Lattice α :=
  @LinearOrder.toLattice α IsSimpleOrder.linearOrder
#align is_simple_order.lattice IsSimpleOrder.lattice

/-- A lattice that is a `bounded_order` is a distributive lattice.
This is not an instance to prevent loops -/
protected def distribLattice : DistribLattice α :=
  { (inferInstance : Lattice α) with
    le_sup_inf := fun x y z => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.distrib_lattice IsSimpleOrder.distribLattice

-- see Note [lower instance priority]
instance (priority := 100) : IsAtomic α :=
  ⟨fun b => (eq_bot_or_eq_top b).imp_right fun h => ⟨⊤, ⟨is_atom_top, ge_of_eq h⟩⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) : IsCoatomic α :=
  is_atomic_dual_iff_is_coatomic.1 IsSimpleOrder.is_atomic

end BoundedOrder

-- It is important that in this section `is_simple_order` is the last type-class argument.
section DecidableEq

variable [DecidableEq α] [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α]

/-- Every simple lattice is isomorphic to `bool`, regardless of order. -/
@[simps]
def equivBool {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] : α ≃ Bool
    where
  toFun x := x = ⊤
  invFun x := cond x ⊤ ⊥
  left_inv x := by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top]
  right_inv x := by cases x <;> simp [bot_ne_top]
#align is_simple_order.equiv_bool IsSimpleOrder.equivBool

/-- Every simple lattice over a partial order is order-isomorphic to `bool`. -/
def orderIsoBool : α ≃o Bool :=
  { equivBool with
    map_rel_iff' := fun a b =>
      by
      rcases eq_bot_or_eq_top a with (rfl | rfl)
      · simp [bot_ne_top]
      · rcases eq_bot_or_eq_top b with (rfl | rfl)
        · simp [bot_ne_top.symm, bot_ne_top, Bool.false_lt_true]
        · simp [bot_ne_top] }
#align is_simple_order.order_iso_bool IsSimpleOrder.orderIsoBool

/-- A simple `bounded_order` is also a `boolean_algebra`. -/
protected def booleanAlgebra {α} [DecidableEq α] [Lattice α] [BoundedOrder α] [IsSimpleOrder α] :
    BooleanAlgebra α :=
  { show BoundedOrder α by infer_instance,
    IsSimpleOrder.distribLattice with
    compl := fun x => if x = ⊥ then ⊤ else ⊥
    sdiff := fun x y => if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥
    sdiff_eq := fun x y => by
      rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp [bot_ne_top, SDiff.sdiff, compl]
    inf_compl_le_bot := fun x =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp
      · simp only [top_inf_eq]
        split_ifs with h h <;> simp [h]
    top_le_sup_compl := fun x => by rcases eq_bot_or_eq_top x with (rfl | rfl) <;> simp }
#align is_simple_order.boolean_algebra IsSimpleOrder.booleanAlgebra

end DecidableEq

variable [Lattice α] [BoundedOrder α] [IsSimpleOrder α]

open Classical

/-- A simple `bounded_order` is also complete. -/
protected noncomputable def completeLattice : CompleteLattice α :=
  { (inferInstance : Lattice α),
    (inferInstance : BoundedOrder
        α) with
    sup := fun s => if ⊤ ∈ s then ⊤ else ⊥
    inf := fun s => if ⊥ ∈ s then ⊥ else ⊤
    le_Sup := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_pos h]
    Sup_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_neg]
        intro con
        exact bot_ne_top (eq_top_iff.2 (h ⊤ con))
      · exact le_top
    Inf_le := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · rw [if_pos h]
      · exact le_top
    le_Inf := fun s x h => by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · exact bot_le
      · rw [if_neg]
        intro con
        exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) }
#align is_simple_order.complete_lattice IsSimpleOrder.completeLattice

/-- A simple `bounded_order` is also a `complete_boolean_algebra`. -/
protected noncomputable def completeBooleanAlgebra : CompleteBooleanAlgebra α :=
  { IsSimpleOrder.completeLattice,
    IsSimpleOrder.booleanAlgebra with
    infi_sup_le_sup_Inf := fun x s =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [bot_sup_eq, ← infₛ_eq_infᵢ]
        exact le_rfl
      · simp only [top_sup_eq, le_top]
    inf_Sup_le_supr_inf := fun x s =>
      by
      rcases eq_bot_or_eq_top x with (rfl | rfl)
      · simp only [bot_inf_eq, bot_le]
      · simp only [top_inf_eq, ← supₛ_eq_supᵢ]
        exact le_rfl }
#align is_simple_order.complete_boolean_algebra IsSimpleOrder.completeBooleanAlgebra

end IsSimpleOrder

namespace IsSimpleOrder

variable [CompleteLattice α] [IsSimpleOrder α]

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
set_option default_priority 100

instance : IsAtomistic α :=
  ⟨fun b =>
    (eq_bot_or_eq_top b).elim
      (fun h => ⟨∅, ⟨h.trans supₛ_empty.symm, fun a ha => False.elim (Set.not_mem_empty _ ha)⟩⟩)
      fun h =>
      ⟨{⊤}, h.trans supₛ_singleton.symm, fun a ha =>
        (Set.mem_singleton_iff.1 ha).symm ▸ is_atom_top⟩⟩

instance : IsCoatomistic α :=
  is_atomistic_dual_iff_is_coatomistic.1 IsSimpleOrder.is_atomistic

end IsSimpleOrder

theorem is_simple_order_iff_is_atom_top [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsAtom (⊤ : α) :=
  ⟨fun h => @is_atom_top _ _ _ h, fun h =>
    { exists_pair_ne := ⟨⊤, ⊥, h.1⟩
      eq_bot_or_eq_top := fun a => ((eq_or_lt_of_le le_top).imp_right (h.2 a)).symm }⟩
#align is_simple_order_iff_is_atom_top is_simple_order_iff_is_atom_top

theorem is_simple_order_iff_is_coatom_bot [PartialOrder α] [BoundedOrder α] :
    IsSimpleOrder α ↔ IsCoatom (⊥ : α) :=
  is_simple_order_iff_is_simple_order_order_dual.trans is_simple_order_iff_is_atom_top
#align is_simple_order_iff_is_coatom_bot is_simple_order_iff_is_coatom_bot

namespace Set

theorem is_simple_order_Iic_iff_is_atom [PartialOrder α] [OrderBot α] {a : α} :
    IsSimpleOrder (Iic a) ↔ IsAtom a :=
  is_simple_order_iff_is_atom_top.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Iic_iff_is_atom Set.is_simple_order_Iic_iff_is_atom

theorem is_simple_order_Ici_iff_is_coatom [PartialOrder α] [OrderTop α] {a : α} :
    IsSimpleOrder (Ici a) ↔ IsCoatom a :=
  is_simple_order_iff_is_coatom_bot.trans <|
    and_congr (not_congr Subtype.mk_eq_mk)
      ⟨fun h b ab => Subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab), fun h ⟨b, hab⟩ hbotb =>
        Subtype.mk_eq_mk.2 (h b (Subtype.mk_lt_mk.1 hbotb))⟩
#align set.is_simple_order_Ici_iff_is_coatom Set.is_simple_order_Ici_iff_is_coatom

end Set

namespace OrderEmbedding

variable [PartialOrder α] [PartialOrder β]

theorem is_atom_of_map_bot_of_image [OrderBot α] [OrderBot β] (f : β ↪o α) (hbot : f ⊥ = ⊥) {b : β}
    (hb : IsAtom (f b)) : IsAtom b :=
  by
  simp only [← bot_covby_iff] at hb⊢
  exact Covby.of_image f (hbot.symm ▸ hb)
#align order_embedding.is_atom_of_map_bot_of_image OrderEmbedding.is_atom_of_map_bot_of_image

theorem is_coatom_of_map_top_of_image [OrderTop α] [OrderTop β] (f : β ↪o α) (htop : f ⊤ = ⊤)
    {b : β} (hb : IsCoatom (f b)) : IsCoatom b :=
  f.dual.is_atom_of_map_bot_of_image htop hb
#align order_embedding.is_coatom_of_map_top_of_image OrderEmbedding.is_coatom_of_map_top_of_image

end OrderEmbedding

namespace GaloisInsertion

variable [PartialOrder α] [PartialOrder β]

theorem is_atom_of_u_bot [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) {b : β} (hb : IsAtom (u b)) : IsAtom b :=
  OrderEmbedding.is_atom_of_map_bot_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ hbot hb
#align galois_insertion.is_atom_of_u_bot GaloisInsertion.is_atom_of_u_bot

theorem is_atom_iff [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  by
  refine' ⟨fun hla => _, fun ha => gi.is_atom_of_u_bot hbot ((h_atom a ha).symm ▸ ha)⟩
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
#align galois_insertion.is_atom_iff GaloisInsertion.is_atom_iff

theorem is_atom_iff' [OrderBot α] [IsAtomic α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (hbot : u ⊥ = ⊥) (h_atom : ∀ a, IsAtom a → u (l a) = a) (b : β) :
    IsAtom (u b) ↔ IsAtom b := by rw [← gi.is_atom_iff hbot h_atom, gi.l_u_eq]
#align galois_insertion.is_atom_iff' GaloisInsertion.is_atom_iff'

theorem is_coatom_of_image [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) {b : β} (hb : IsCoatom (u b)) : IsCoatom b :=
  OrderEmbedding.is_coatom_of_map_top_of_image
    ⟨⟨u, gi.u_injective⟩, @GaloisInsertion.u_le_u_iff _ _ _ _ _ _ gi⟩ gi.gc.u_top hb
#align galois_insertion.is_coatom_of_image GaloisInsertion.is_coatom_of_image

theorem is_coatom_iff [OrderTop α] [IsCoatomic α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisInsertion l u) (h_coatom : ∀ a : α, IsCoatom a → u (l a) = a) (b : β) :
    IsCoatom (u b) ↔ IsCoatom b :=
  by
  refine' ⟨fun hb => gi.is_coatom_of_image hb, fun hb => _⟩
  obtain ⟨a, ha, hab⟩ :=
    (eq_top_or_exists_le_coatom (u b)).resolve_left fun h =>
      hb.1 <| (gi.gc.u_top ▸ gi.l_u_eq ⊤ : l ⊤ = ⊤) ▸ gi.l_u_eq b ▸ congr_arg l h
  have : l a = b :=
    (hb.le_iff.mp (gi.l_u_eq b ▸ gi.gc.monotone_l hab : b ≤ l a)).resolve_left fun hla =>
      ha.1 (gi.gc.u_top ▸ h_coatom a ha ▸ congr_arg u hla)
  exact this ▸ (h_coatom a ha).symm ▸ ha
#align galois_insertion.is_coatom_iff GaloisInsertion.is_coatom_iff

end GaloisInsertion

namespace GaloisCoinsertion

variable [PartialOrder α] [PartialOrder β]

theorem is_coatom_of_l_top [OrderTop α] [OrderTop β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (hbot : l ⊤ = ⊤) {a : α} (hb : IsCoatom (l a)) : IsCoatom a :=
  gi.dual.is_atom_of_u_bot hbot hb.dual
#align galois_coinsertion.is_coatom_of_l_top GaloisCoinsertion.is_coatom_of_l_top

theorem is_coatom_iff [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (b : β) : IsCoatom (u b) ↔ IsCoatom b :=
  gi.dual.is_atom_iff htop h_coatom b
#align galois_coinsertion.is_coatom_iff GaloisCoinsertion.is_coatom_iff

theorem is_coatom_iff' [OrderTop α] [OrderTop β] [IsCoatomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (htop : l ⊤ = ⊤) (h_coatom : ∀ b, IsCoatom b → l (u b) = b)
    (a : α) : IsCoatom (l a) ↔ IsCoatom a :=
  gi.dual.is_atom_iff' htop h_coatom a
#align galois_coinsertion.is_coatom_iff' GaloisCoinsertion.is_coatom_iff'

theorem is_atom_of_image [OrderBot α] [OrderBot β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) {a : α} (hb : IsAtom (l a)) : IsAtom a :=
  gi.dual.is_coatom_of_image hb.dual
#align galois_coinsertion.is_atom_of_image GaloisCoinsertion.is_atom_of_image

theorem is_atom_iff [OrderBot α] [OrderBot β] [IsAtomic β] {l : α → β} {u : β → α}
    (gi : GaloisCoinsertion l u) (h_atom : ∀ b, IsAtom b → l (u b) = b) (a : α) :
    IsAtom (l a) ↔ IsAtom a :=
  gi.dual.is_coatom_iff h_atom a
#align galois_coinsertion.is_atom_iff GaloisCoinsertion.is_atom_iff

end GaloisCoinsertion

namespace OrderIso

variable [PartialOrder α] [PartialOrder β]

@[simp]
theorem is_atom_iff [OrderBot α] [OrderBot β] (f : α ≃o β) (a : α) : IsAtom (f a) ↔ IsAtom a :=
  ⟨f.toGaloisCoinsertion.is_atom_of_image, fun ha =>
    f.toGaloisInsertion.is_atom_of_u_bot (map_bot f.symm) <| (f.symm_apply_apply a).symm ▸ ha⟩
#align order_iso.is_atom_iff OrderIso.is_atom_iff

@[simp]
theorem is_coatom_iff [OrderTop α] [OrderTop β] (f : α ≃o β) (a : α) :
    IsCoatom (f a) ↔ IsCoatom a :=
  f.dual.is_atom_iff a
#align order_iso.is_coatom_iff OrderIso.is_coatom_iff

theorem is_simple_order_iff [BoundedOrder α] [BoundedOrder β] (f : α ≃o β) :
    IsSimpleOrder α ↔ IsSimpleOrder β := by
  rw [is_simple_order_iff_is_atom_top, is_simple_order_iff_is_atom_top, ← f.is_atom_iff ⊤,
    f.map_top]
#align order_iso.is_simple_order_iff OrderIso.is_simple_order_iff

theorem is_simple_order [BoundedOrder α] [BoundedOrder β] [h : IsSimpleOrder β] (f : α ≃o β) :
    IsSimpleOrder α :=
  f.is_simple_order_iff.mpr h
#align order_iso.is_simple_order OrderIso.is_simple_order

protected theorem is_atomic_iff [OrderBot α] [OrderBot β] (f : α ≃o β) : IsAtomic α ↔ IsAtomic β :=
  by
  simp only [is_atomic_iff, f.surjective.forall, f.surjective.exists, ← map_bot f, f.eq_iff_eq,
    f.le_iff_le, f.is_atom_iff]
#align order_iso.is_atomic_iff OrderIso.is_atomic_iff

protected theorem is_coatomic_iff [OrderTop α] [OrderTop β] (f : α ≃o β) :
    IsCoatomic α ↔ IsCoatomic β := by
  simp only [← is_atomic_dual_iff_is_coatomic, f.dual.is_atomic_iff]
#align order_iso.is_coatomic_iff OrderIso.is_coatomic_iff

end OrderIso

section IsModularLattice

variable [Lattice α] [BoundedOrder α] [IsModularLattice α]

namespace IsCompl

variable {a b : α} (hc : IsCompl a b)

include hc

theorem is_atom_iff_is_coatom : IsAtom a ↔ IsCoatom b :=
  Set.is_simple_order_Iic_iff_is_atom.symm.trans <|
    hc.iicOrderIsoIci.is_simple_order_iff.trans Set.is_simple_order_Ici_iff_is_coatom
#align is_compl.is_atom_iff_is_coatom IsCompl.is_atom_iff_is_coatom

theorem is_coatom_iff_is_atom : IsCoatom a ↔ IsAtom b :=
  hc.symm.is_atom_iff_is_coatom.symm
#align is_compl.is_coatom_iff_is_atom IsCompl.is_coatom_iff_is_atom

end IsCompl

variable [ComplementedLattice α]

theorem is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular [IsAtomic α] :
    IsCoatomic α :=
  ⟨fun x => by
    rcases exists_is_compl x with ⟨y, xy⟩
    apply (eq_bot_or_exists_atom_le y).imp _ _
    · rintro rfl
      exact eq_top_of_isCompl_bot xy
    · rintro ⟨a, ha, ay⟩
      rcases exists_is_compl (xy.symm.Iic_order_iso_Ici ⟨a, ay⟩) with ⟨⟨b, xb⟩, hb⟩
      refine' ⟨↑(⟨b, xb⟩ : Set.Ici x), IsCoatom.of_is_coatom_coe_Ici _, xb⟩
      rw [← hb.is_atom_iff_is_coatom, OrderIso.is_atom_iff]
      apply ha.Iic⟩
#align
  is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular

theorem is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular [IsCoatomic α] :
    IsAtomic α :=
  is_coatomic_dual_iff_is_atomic.1 is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular
#align
  is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular

theorem is_atomic_iff_is_coatomic : IsAtomic α ↔ IsCoatomic α :=
  ⟨fun h => @is_coatomic_of_is_atomic_of_complemented_lattice_of_is_modular _ _ _ _ _ h, fun h =>
    @is_atomic_of_is_coatomic_of_complemented_lattice_of_is_modular _ _ _ _ _ h⟩
#align is_atomic_iff_is_coatomic is_atomic_iff_is_coatomic

end IsModularLattice

namespace Set

theorem is_atom_singleton (x : α) : IsAtom ({x} : Set α) :=
  ⟨singleton_ne_empty _, fun s hs => ssubset_singleton_iff.mp hs⟩
#align set.is_atom_singleton Set.is_atom_singleton

theorem is_atom_iff (s : Set α) : IsAtom s ↔ ∃ x, s = {x} :=
  by
  refine'
    ⟨_, by
      rintro ⟨x, rfl⟩
      exact is_atom_singleton x⟩
  rw [is_atom_iff, bot_eq_empty, ← nonempty_iff_ne_empty]
  rintro ⟨⟨x, hx⟩, hs⟩
  exact
    ⟨x,
      eq_singleton_iff_unique_mem.2
        ⟨hx, fun y hy => (hs {y} (singleton_ne_empty _) (singleton_subset_iff.2 hy) hx).symm⟩⟩
#align set.is_atom_iff Set.is_atom_iff

theorem is_coatom_iff (s : Set α) : IsCoatom s ↔ ∃ x, s = {x}ᶜ := by
  simp_rw [is_compl_compl.is_coatom_iff_is_atom, is_atom_iff, @eq_comm _ s, compl_eq_comm]
#align set.is_coatom_iff Set.is_coatom_iff

theorem is_coatom_singleton_compl (x : α) : IsCoatom ({x}ᶜ : Set α) :=
  (is_coatom_iff ({x}ᶜ)).mpr ⟨x, rfl⟩
#align set.is_coatom_singleton_compl Set.is_coatom_singleton_compl

instance : IsAtomistic (Set α)
    where eq_Sup_atoms s :=
    ⟨(fun x => {x}) '' s, by rw [Sup_eq_sUnion, sUnion_image, bUnion_of_singleton],
      by
      rintro - ⟨x, hx, rfl⟩
      exact is_atom_singleton x⟩

instance : IsCoatomistic (Set α)
    where eq_Inf_coatoms s :=
    ⟨(fun x => {x}ᶜ) '' sᶜ, by
      rw [Inf_eq_sInter, sInter_image, ← compl_Union₂, bUnion_of_singleton, compl_compl],
      by
      rintro - ⟨x, hx, rfl⟩
      exact is_coatom_singleton_compl x⟩

end Set
