/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.BoundedOrder

#align_import order.disjoint from "leanprover-community/mathlib"@"22c4d2ff43714b6ff724b2745ccfdc0f236a4a76"

/-!
# Disjointness and complements

This file defines `Disjoint`, `Codisjoint`, and the `IsCompl` predicate.

## Main declarations

* `Disjoint x y`: two elements of a lattice are disjoint if their `inf` is the bottom element.
* `Codisjoint x y`: two elements of a lattice are codisjoint if their `join` is the top element.
* `IsCompl x y`: In a bounded lattice, predicate for "`x` is a complement of `y`". Note that in a
  non distributive lattice, an element can have several complements.
* `ComplementedLattice α`: Typeclass stating that any element of a lattice has a complement.

-/

open Function

variable {α : Type*}

section Disjoint

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {a b c d : α}

/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.)

Note that we define this without reference to `⊓`, as this allows us to talk about orders where
the infimum is not unique, or where implementing `Inf` would require additional `Decidable`
arguments. -/
def Disjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, x ≤ a → x ≤ b → x ≤ ⊥
#align disjoint Disjoint

theorem disjoint_comm : Disjoint a b ↔ Disjoint b a :=
  forall_congr' fun _ ↦ forall_swap
#align disjoint.comm disjoint_comm

@[symm]
theorem Disjoint.symm ⦃a b : α⦄ : Disjoint a b → Disjoint b a :=
  disjoint_comm.1
#align disjoint.symm Disjoint.symm

theorem symmetric_disjoint : Symmetric (Disjoint : α → α → Prop) :=
  Disjoint.symm
#align symmetric_disjoint symmetric_disjoint

@[simp]
theorem disjoint_bot_left : Disjoint ⊥ a := fun _ hbot _ ↦ hbot
#align disjoint_bot_left disjoint_bot_left

@[simp]
theorem disjoint_bot_right : Disjoint a ⊥ := fun _ _ hbot ↦ hbot
#align disjoint_bot_right disjoint_bot_right

theorem Disjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Disjoint b d → Disjoint a c :=
  fun h _ ha hc ↦ h (ha.trans h₁) (hc.trans h₂)
#align disjoint.mono Disjoint.mono

theorem Disjoint.mono_left (h : a ≤ b) : Disjoint b c → Disjoint a c :=
  Disjoint.mono h le_rfl
#align disjoint.mono_left Disjoint.mono_left

theorem Disjoint.mono_right : b ≤ c → Disjoint a c → Disjoint a b :=
  Disjoint.mono le_rfl
#align disjoint.mono_right Disjoint.mono_right

@[simp]
theorem disjoint_self : Disjoint a a ↔ a = ⊥ :=
  ⟨fun hd ↦ bot_unique <| hd le_rfl le_rfl, fun h _ ha _ ↦ ha.trans_eq h⟩
#align disjoint_self disjoint_self

/- TODO: Rename `Disjoint.eq_bot` to `Disjoint.inf_eq` and `Disjoint.eq_bot_of_self` to
`Disjoint.eq_bot` -/
alias ⟨Disjoint.eq_bot_of_self, _⟩ := disjoint_self
#align disjoint.eq_bot_of_self Disjoint.eq_bot_of_self

theorem Disjoint.ne (ha : a ≠ ⊥) (hab : Disjoint a b) : a ≠ b :=
  fun h ↦ ha <| disjoint_self.1 <| by rwa [← h] at hab
                                      -- 🎉 no goals
#align disjoint.ne Disjoint.ne

theorem Disjoint.eq_bot_of_le (hab : Disjoint a b) (h : a ≤ b) : a = ⊥ :=
  eq_bot_iff.2 <| hab le_rfl h
#align disjoint.eq_bot_of_le Disjoint.eq_bot_of_le

theorem Disjoint.eq_bot_of_ge (hab : Disjoint a b) : b ≤ a → b = ⊥ :=
  hab.symm.eq_bot_of_le
#align disjoint.eq_bot_of_ge Disjoint.eq_bot_of_ge

end PartialOrderBot

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a : α}

@[simp]
theorem disjoint_top : Disjoint a ⊤ ↔ a = ⊥ :=
  ⟨fun h ↦ bot_unique <| h le_rfl le_top, fun h _ ha _ ↦ ha.trans_eq h⟩
#align disjoint_top disjoint_top

@[simp]
theorem top_disjoint : Disjoint ⊤ a ↔ a = ⊥ :=
  ⟨fun h ↦ bot_unique <| h le_top le_rfl, fun h _ _ ha ↦ ha.trans_eq h⟩
#align top_disjoint top_disjoint

end PartialBoundedOrder

section SemilatticeInfBot

variable [SemilatticeInf α] [OrderBot α] {a b c d : α}

theorem disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b ≤ ⊥ :=
  ⟨fun hd ↦ hd inf_le_left inf_le_right, fun h _ ha hb ↦ (le_inf ha hb).trans h⟩
#align disjoint_iff_inf_le disjoint_iff_inf_le

theorem disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥ :=
  disjoint_iff_inf_le.trans le_bot_iff
#align disjoint_iff disjoint_iff

theorem Disjoint.le_bot : Disjoint a b → a ⊓ b ≤ ⊥ :=
  disjoint_iff_inf_le.mp
#align disjoint.le_bot Disjoint.le_bot

theorem Disjoint.eq_bot : Disjoint a b → a ⊓ b = ⊥ :=
  bot_unique ∘ Disjoint.le_bot
#align disjoint.eq_bot Disjoint.eq_bot

theorem disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c) := by
  rw [disjoint_iff_inf_le, disjoint_iff_inf_le, inf_assoc]
  -- 🎉 no goals
#align disjoint_assoc disjoint_assoc

theorem disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b (a ⊓ c) := by
  simp_rw [disjoint_iff_inf_le, inf_left_comm]
  -- 🎉 no goals
#align disjoint_left_comm disjoint_left_comm

theorem disjoint_right_comm : Disjoint (a ⊓ b) c ↔ Disjoint (a ⊓ c) b := by
  simp_rw [disjoint_iff_inf_le, inf_right_comm]
  -- 🎉 no goals
#align disjoint_right_comm disjoint_right_comm

variable (c)

theorem Disjoint.inf_left (h : Disjoint a b) : Disjoint (a ⊓ c) b :=
  h.mono_left inf_le_left
#align disjoint.inf_left Disjoint.inf_left

theorem Disjoint.inf_left' (h : Disjoint a b) : Disjoint (c ⊓ a) b :=
  h.mono_left inf_le_right
#align disjoint.inf_left' Disjoint.inf_left'

theorem Disjoint.inf_right (h : Disjoint a b) : Disjoint a (b ⊓ c) :=
  h.mono_right inf_le_left
#align disjoint.inf_right Disjoint.inf_right

theorem Disjoint.inf_right' (h : Disjoint a b) : Disjoint a (c ⊓ b) :=
  h.mono_right inf_le_right
#align disjoint.inf_right' Disjoint.inf_right'

variable {c}

theorem Disjoint.of_disjoint_inf_of_le (h : Disjoint (a ⊓ b) c) (hle : a ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_left_le hle
#align disjoint.of_disjoint_inf_of_le Disjoint.of_disjoint_inf_of_le

theorem Disjoint.of_disjoint_inf_of_le' (h : Disjoint (a ⊓ b) c) (hle : b ≤ c) : Disjoint a b :=
  disjoint_iff.2 <| h.eq_bot_of_le <| inf_le_of_right_le hle
#align disjoint.of_disjoint_inf_of_le' Disjoint.of_disjoint_inf_of_le'

end SemilatticeInfBot

section DistribLatticeBot

variable [DistribLattice α] [OrderBot α] {a b c : α}

@[simp]
theorem disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c ∧ Disjoint b c := by
  simp only [disjoint_iff, inf_sup_right, sup_eq_bot_iff]
  -- 🎉 no goals
#align disjoint_sup_left disjoint_sup_left

@[simp]
theorem disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a b ∧ Disjoint a c := by
  simp only [disjoint_iff, inf_sup_left, sup_eq_bot_iff]
  -- 🎉 no goals
#align disjoint_sup_right disjoint_sup_right

theorem Disjoint.sup_left (ha : Disjoint a c) (hb : Disjoint b c) : Disjoint (a ⊔ b) c :=
  disjoint_sup_left.2 ⟨ha, hb⟩
#align disjoint.sup_left Disjoint.sup_left

theorem Disjoint.sup_right (hb : Disjoint a b) (hc : Disjoint a c) : Disjoint a (b ⊔ c) :=
  disjoint_sup_right.2 ⟨hb, hc⟩
#align disjoint.sup_right Disjoint.sup_right

theorem Disjoint.left_le_of_le_sup_right (h : a ≤ b ⊔ c) (hd : Disjoint a c) : a ≤ b :=
  le_of_inf_le_sup_le (le_trans hd.le_bot bot_le) <| sup_le h le_sup_right
#align disjoint.left_le_of_le_sup_right Disjoint.left_le_of_le_sup_right

theorem Disjoint.left_le_of_le_sup_left (h : a ≤ c ⊔ b) (hd : Disjoint a c) : a ≤ b :=
  hd.left_le_of_le_sup_right <| by rwa [sup_comm]
                                   -- 🎉 no goals
#align disjoint.left_le_of_le_sup_left Disjoint.left_le_of_le_sup_left

end DistribLatticeBot

end Disjoint

section Codisjoint

section PartialOrderTop

variable [PartialOrder α] [OrderTop α] {a b c d : α}

/-- Two elements of a lattice are codisjoint if their sup is the top element.

Note that we define this without reference to `⊔`, as this allows us to talk about orders where
the supremum is not unique, or where implement `Sup` would require additional `Decidable`
arguments. -/
def Codisjoint (a b : α) : Prop :=
  ∀ ⦃x⦄, a ≤ x → b ≤ x → ⊤ ≤ x
#align codisjoint Codisjoint

theorem Codisjoint_comm : Codisjoint a b ↔ Codisjoint b a :=
  forall_congr' fun _ ↦ forall_swap
#align codisjoint.comm Codisjoint_comm

@[symm]
theorem Codisjoint.symm ⦃a b : α⦄ : Codisjoint a b → Codisjoint b a :=
  Codisjoint_comm.1
#align codisjoint.symm Codisjoint.symm

theorem symmetric_codisjoint : Symmetric (Codisjoint : α → α → Prop) :=
  Codisjoint.symm
#align symmetric_codisjoint symmetric_codisjoint

@[simp]
theorem codisjoint_top_left : Codisjoint ⊤ a := fun _ htop _ ↦ htop
#align codisjoint_top_left codisjoint_top_left

@[simp]
theorem codisjoint_top_right : Codisjoint a ⊤ := fun _ _ htop ↦ htop
#align codisjoint_top_right codisjoint_top_right

theorem Codisjoint.mono (h₁ : a ≤ b) (h₂ : c ≤ d) : Codisjoint a c → Codisjoint b d :=
  fun h _ ha hc ↦ h (h₁.trans ha) (h₂.trans hc)
#align codisjoint.mono Codisjoint.mono

theorem Codisjoint.mono_left (h : a ≤ b) : Codisjoint a c → Codisjoint b c :=
  Codisjoint.mono h le_rfl
#align codisjoint.mono_left Codisjoint.mono_left

theorem Codisjoint.mono_right : b ≤ c → Codisjoint a b → Codisjoint a c :=
  Codisjoint.mono le_rfl
#align codisjoint.mono_right Codisjoint.mono_right

@[simp]
theorem codisjoint_self : Codisjoint a a ↔ a = ⊤ :=
  ⟨fun hd ↦ top_unique <| hd le_rfl le_rfl, fun h _ ha _ ↦ h.symm.trans_le ha⟩
#align codisjoint_self codisjoint_self

/- TODO: Rename `Codisjoint.eq_top` to `Codisjoint.sup_eq` and `Codisjoint.eq_top_of_self` to
`Codisjoint.eq_top` -/
alias ⟨Codisjoint.eq_top_of_self, _⟩ := codisjoint_self
#align codisjoint.eq_top_of_self Codisjoint.eq_top_of_self

theorem Codisjoint.ne (ha : a ≠ ⊤) (hab : Codisjoint a b) : a ≠ b :=
  fun h ↦ ha <| codisjoint_self.1 <| by rwa [← h] at hab
                                        -- 🎉 no goals
#align codisjoint.ne Codisjoint.ne

theorem Codisjoint.eq_top_of_le (hab : Codisjoint a b) (h : b ≤ a) : a = ⊤ :=
  eq_top_iff.2 <| hab le_rfl h
#align codisjoint.eq_top_of_le Codisjoint.eq_top_of_le

theorem Codisjoint.eq_top_of_ge (hab : Codisjoint a b) : a ≤ b → b = ⊤ :=
  hab.symm.eq_top_of_le
#align codisjoint.eq_top_of_ge Codisjoint.eq_top_of_ge

end PartialOrderTop

section PartialBoundedOrder

variable [PartialOrder α] [BoundedOrder α] {a : α}

@[simp]
theorem codisjoint_bot : Codisjoint a ⊥ ↔ a = ⊤ :=
  ⟨fun h ↦ top_unique <| h le_rfl bot_le, fun h _ ha _ ↦ h.symm.trans_le ha⟩
#align codisjoint_bot codisjoint_bot

@[simp]
theorem bot_codisjoint : Codisjoint ⊥ a ↔ a = ⊤ :=
  ⟨fun h ↦ top_unique <| h bot_le le_rfl, fun h _ _ ha ↦ h.symm.trans_le ha⟩
#align bot_codisjoint bot_codisjoint

end PartialBoundedOrder

section SemilatticeSupTop

variable [SemilatticeSup α] [OrderTop α] {a b c d : α}

theorem codisjoint_iff_le_sup : Codisjoint a b ↔ ⊤ ≤ a ⊔ b :=
  @disjoint_iff_inf_le αᵒᵈ _ _ _ _
#align codisjoint_iff_le_sup codisjoint_iff_le_sup

theorem codisjoint_iff : Codisjoint a b ↔ a ⊔ b = ⊤ :=
  @disjoint_iff αᵒᵈ _ _ _ _
#align codisjoint_iff codisjoint_iff

theorem Codisjoint.top_le : Codisjoint a b → ⊤ ≤ a ⊔ b :=
  @Disjoint.le_bot αᵒᵈ _ _ _ _
#align codisjoint.top_le Codisjoint.top_le

theorem Codisjoint.eq_top : Codisjoint a b → a ⊔ b = ⊤ :=
  @Disjoint.eq_bot αᵒᵈ _ _ _ _
#align codisjoint.eq_top Codisjoint.eq_top

theorem codisjoint_assoc : Codisjoint (a ⊔ b) c ↔ Codisjoint a (b ⊔ c) :=
  @disjoint_assoc αᵒᵈ _ _ _ _ _
#align codisjoint_assoc codisjoint_assoc

theorem codisjoint_left_comm : Codisjoint a (b ⊔ c) ↔ Codisjoint b (a ⊔ c) :=
  @disjoint_left_comm αᵒᵈ _ _ _ _ _
#align codisjoint_left_comm codisjoint_left_comm

theorem codisjoint_right_comm : Codisjoint (a ⊔ b) c ↔ Codisjoint (a ⊔ c) b :=
  @disjoint_right_comm αᵒᵈ _ _ _ _ _
#align codisjoint_right_comm codisjoint_right_comm

variable (c)

theorem Codisjoint.sup_left (h : Codisjoint a b) : Codisjoint (a ⊔ c) b :=
  h.mono_left le_sup_left
#align codisjoint.sup_left Codisjoint.sup_left

theorem Codisjoint.sup_left' (h : Codisjoint a b) : Codisjoint (c ⊔ a) b :=
  h.mono_left le_sup_right
#align codisjoint.sup_left' Codisjoint.sup_left'

theorem Codisjoint.sup_right (h : Codisjoint a b) : Codisjoint a (b ⊔ c) :=
  h.mono_right le_sup_left
#align codisjoint.sup_right Codisjoint.sup_right

theorem Codisjoint.sup_right' (h : Codisjoint a b) : Codisjoint a (c ⊔ b) :=
  h.mono_right le_sup_right
#align codisjoint.sup_right' Codisjoint.sup_right'

variable {c}

theorem Codisjoint.of_codisjoint_sup_of_le (h : Codisjoint (a ⊔ b) c) (hle : c ≤ a) :
    Codisjoint a b :=
  @Disjoint.of_disjoint_inf_of_le αᵒᵈ _ _ _ _ _ h hle
#align codisjoint.of_codisjoint_sup_of_le Codisjoint.of_codisjoint_sup_of_le

theorem Codisjoint.of_codisjoint_sup_of_le' (h : Codisjoint (a ⊔ b) c) (hle : c ≤ b) :
    Codisjoint a b :=
  @Disjoint.of_disjoint_inf_of_le' αᵒᵈ _ _ _ _ _ h hle
#align codisjoint.of_codisjoint_sup_of_le' Codisjoint.of_codisjoint_sup_of_le'

end SemilatticeSupTop

section DistribLatticeTop

variable [DistribLattice α] [OrderTop α] {a b c : α}

@[simp]
theorem codisjoint_inf_left : Codisjoint (a ⊓ b) c ↔ Codisjoint a c ∧ Codisjoint b c := by
  simp only [codisjoint_iff, sup_inf_right, inf_eq_top_iff]
  -- 🎉 no goals
#align codisjoint_inf_left codisjoint_inf_left

@[simp]
theorem codisjoint_inf_right : Codisjoint a (b ⊓ c) ↔ Codisjoint a b ∧ Codisjoint a c := by
  simp only [codisjoint_iff, sup_inf_left, inf_eq_top_iff]
  -- 🎉 no goals
#align codisjoint_inf_right codisjoint_inf_right

theorem Codisjoint.inf_left (ha : Codisjoint a c) (hb : Codisjoint b c) : Codisjoint (a ⊓ b) c :=
  codisjoint_inf_left.2 ⟨ha, hb⟩
#align codisjoint.inf_left Codisjoint.inf_left

theorem Codisjoint.inf_right (hb : Codisjoint a b) (hc : Codisjoint a c) : Codisjoint a (b ⊓ c) :=
  codisjoint_inf_right.2 ⟨hb, hc⟩
#align codisjoint.inf_right Codisjoint.inf_right

theorem Codisjoint.left_le_of_le_inf_right (h : a ⊓ b ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  @Disjoint.left_le_of_le_sup_right αᵒᵈ _ _ _ _ _ h hd.symm
#align codisjoint.left_le_of_le_inf_right Codisjoint.left_le_of_le_inf_right

theorem Codisjoint.left_le_of_le_inf_left (h : b ⊓ a ≤ c) (hd : Codisjoint b c) : a ≤ c :=
  hd.left_le_of_le_inf_right <| by rwa [inf_comm]
                                   -- 🎉 no goals
#align codisjoint.left_le_of_le_inf_left Codisjoint.left_le_of_le_inf_left

end DistribLatticeTop

end Codisjoint

open OrderDual

theorem Disjoint.dual [SemilatticeInf α] [OrderBot α] {a b : α} :
    Disjoint a b → Codisjoint (toDual a) (toDual b) :=
  id
#align disjoint.dual Disjoint.dual

theorem Codisjoint.dual [SemilatticeSup α] [OrderTop α] {a b : α} :
    Codisjoint a b → Disjoint (toDual a) (toDual b) :=
  id
#align codisjoint.dual Codisjoint.dual

@[simp]
theorem disjoint_toDual_iff [SemilatticeSup α] [OrderTop α] {a b : α} :
    Disjoint (toDual a) (toDual b) ↔ Codisjoint a b :=
  Iff.rfl
#align disjoint_to_dual_iff disjoint_toDual_iff

@[simp]
theorem disjoint_ofDual_iff [SemilatticeInf α] [OrderBot α] {a b : αᵒᵈ} :
    Disjoint (ofDual a) (ofDual b) ↔ Codisjoint a b :=
  Iff.rfl
#align disjoint_of_dual_iff disjoint_ofDual_iff

@[simp]
theorem codisjoint_toDual_iff [SemilatticeInf α] [OrderBot α] {a b : α} :
    Codisjoint (toDual a) (toDual b) ↔ Disjoint a b :=
  Iff.rfl
#align codisjoint_to_dual_iff codisjoint_toDual_iff

@[simp]
theorem codisjoint_ofDual_iff [SemilatticeSup α] [OrderTop α] {a b : αᵒᵈ} :
    Codisjoint (ofDual a) (ofDual b) ↔ Disjoint a b :=
  Iff.rfl
#align codisjoint_of_dual_iff codisjoint_ofDual_iff

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] {a b c : α}

theorem Disjoint.le_of_codisjoint (hab : Disjoint a b) (hbc : Codisjoint b c) : a ≤ c := by
  rw [← @inf_top_eq _ _ _ a, ← @bot_sup_eq _ _ _ c, ← hab.eq_bot, ← hbc.eq_top, sup_inf_right]
  -- ⊢ a ⊓ (b ⊔ c) ≤ (a ⊔ c) ⊓ (b ⊔ c)
  exact inf_le_inf_right _ le_sup_left
  -- 🎉 no goals
#align disjoint.le_of_codisjoint Disjoint.le_of_codisjoint

end DistribLattice

section IsCompl

/-- Two elements `x` and `y` are complements of each other if `x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
structure IsCompl [PartialOrder α] [BoundedOrder α] (x y : α) : Prop where
  /-- If `x` and `y` are to be complementary in an order, they should be disjoint. -/
  protected disjoint : Disjoint x y
  /-- If `x` and `y` are to be complementary in an order, they should be codisjoint. -/
  protected codisjoint : Codisjoint x y
#align is_compl IsCompl

theorem isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} :
    IsCompl a b ↔ Disjoint a b ∧ Codisjoint a b :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
#align is_compl_iff isCompl_iff

namespace IsCompl

section BoundedPartialOrder

variable [PartialOrder α] [BoundedOrder α] {x y z : α}

@[symm]
protected theorem symm (h : IsCompl x y) : IsCompl y x :=
  ⟨h.1.symm, h.2.symm⟩
#align is_compl.symm IsCompl.symm

theorem dual (h : IsCompl x y) : IsCompl (toDual x) (toDual y) :=
  ⟨h.2, h.1⟩
#align is_compl.dual IsCompl.dual

theorem ofDual {a b : αᵒᵈ} (h : IsCompl a b) : IsCompl (ofDual a) (ofDual b) :=
  ⟨h.2, h.1⟩
#align is_compl.of_dual IsCompl.ofDual

end BoundedPartialOrder

section BoundedLattice

variable [Lattice α] [BoundedOrder α] {x y z : α}

theorem of_le (h₁ : x ⊓ y ≤ ⊥) (h₂ : ⊤ ≤ x ⊔ y) : IsCompl x y :=
  ⟨disjoint_iff_inf_le.mpr h₁, codisjoint_iff_le_sup.mpr h₂⟩
#align is_compl.of_le IsCompl.of_le

theorem of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y :=
  ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr h₂⟩
#align is_compl.of_eq IsCompl.of_eq

theorem inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥ :=
  h.disjoint.eq_bot
#align is_compl.inf_eq_bot IsCompl.inf_eq_bot

theorem sup_eq_top (h : IsCompl x y) : x ⊔ y = ⊤ :=
  h.codisjoint.eq_top
#align is_compl.sup_eq_top IsCompl.sup_eq_top

end BoundedLattice

variable [DistribLattice α] [BoundedOrder α] {a b x y z : α}

theorem inf_left_le_of_le_sup_right (h : IsCompl x y) (hle : a ≤ b ⊔ y) : a ⊓ x ≤ b :=
  calc
    a ⊓ x ≤ (b ⊔ y) ⊓ x := inf_le_inf hle le_rfl
    _ = b ⊓ x ⊔ y ⊓ x := inf_sup_right
    _ = b ⊓ x := by rw [h.symm.inf_eq_bot, sup_bot_eq]
                    -- 🎉 no goals
    _ ≤ b := inf_le_left
#align is_compl.inf_left_le_of_le_sup_right IsCompl.inf_left_le_of_le_sup_right

theorem le_sup_right_iff_inf_left_le {a b} (h : IsCompl x y) : a ≤ b ⊔ y ↔ a ⊓ x ≤ b :=
  ⟨h.inf_left_le_of_le_sup_right, h.symm.dual.inf_left_le_of_le_sup_right⟩
#align is_compl.le_sup_right_iff_inf_left_le IsCompl.le_sup_right_iff_inf_left_le

theorem inf_left_eq_bot_iff (h : IsCompl y z) : x ⊓ y = ⊥ ↔ x ≤ z := by
  rw [← le_bot_iff, ← h.le_sup_right_iff_inf_left_le, bot_sup_eq]
  -- 🎉 no goals
#align is_compl.inf_left_eq_bot_iff IsCompl.inf_left_eq_bot_iff

theorem inf_right_eq_bot_iff (h : IsCompl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
  h.symm.inf_left_eq_bot_iff
#align is_compl.inf_right_eq_bot_iff IsCompl.inf_right_eq_bot_iff

theorem disjoint_left_iff (h : IsCompl y z) : Disjoint x y ↔ x ≤ z := by
  rw [disjoint_iff]
  -- ⊢ x ⊓ y = ⊥ ↔ x ≤ z
  exact h.inf_left_eq_bot_iff
  -- 🎉 no goals
#align is_compl.disjoint_left_iff IsCompl.disjoint_left_iff

theorem disjoint_right_iff (h : IsCompl y z) : Disjoint x z ↔ x ≤ y :=
  h.symm.disjoint_left_iff
#align is_compl.disjoint_right_iff IsCompl.disjoint_right_iff

theorem le_left_iff (h : IsCompl x y) : z ≤ x ↔ Disjoint z y :=
  h.disjoint_right_iff.symm
#align is_compl.le_left_iff IsCompl.le_left_iff

theorem le_right_iff (h : IsCompl x y) : z ≤ y ↔ Disjoint z x :=
  h.symm.le_left_iff
#align is_compl.le_right_iff IsCompl.le_right_iff

theorem left_le_iff (h : IsCompl x y) : x ≤ z ↔ Codisjoint z y :=
  h.dual.le_left_iff
#align is_compl.left_le_iff IsCompl.left_le_iff

theorem right_le_iff (h : IsCompl x y) : y ≤ z ↔ Codisjoint z x :=
  h.symm.left_le_iff
#align is_compl.right_le_iff IsCompl.right_le_iff

protected theorem Antitone {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') (hx : x ≤ x') : y' ≤ y :=
  h'.right_le_iff.2 <| h.symm.codisjoint.mono_right hx
#align is_compl.antitone IsCompl.Antitone

theorem right_unique (hxy : IsCompl x y) (hxz : IsCompl x z) : y = z :=
  le_antisymm (hxz.Antitone hxy <| le_refl x) (hxy.Antitone hxz <| le_refl x)
#align is_compl.right_unique IsCompl.right_unique

theorem left_unique (hxz : IsCompl x z) (hyz : IsCompl y z) : x = y :=
  hxz.symm.right_unique hyz.symm
#align is_compl.left_unique IsCompl.left_unique

theorem sup_inf {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊔ x') (y ⊓ y') :=
  of_eq
    (by rw [inf_sup_right, ← inf_assoc, h.inf_eq_bot, bot_inf_eq, bot_sup_eq, inf_left_comm,
      h'.inf_eq_bot, inf_bot_eq])
    (by rw [sup_inf_left, @sup_comm _ _ x, sup_assoc, h.sup_eq_top, sup_top_eq, top_inf_eq,
      sup_assoc, sup_left_comm, h'.sup_eq_top, sup_top_eq])
#align is_compl.sup_inf IsCompl.sup_inf

theorem inf_sup {x' y'} (h : IsCompl x y) (h' : IsCompl x' y') : IsCompl (x ⊓ x') (y ⊔ y') :=
  (h.symm.sup_inf h'.symm).symm
#align is_compl.inf_sup IsCompl.inf_sup

end IsCompl

namespace Prod

variable {β : Type*} [PartialOrder α] [PartialOrder β]

protected theorem disjoint_iff [OrderBot α] [OrderBot β] {x y : α × β} :
    Disjoint x y ↔ Disjoint x.1 y.1 ∧ Disjoint x.2 y.2 := by
  constructor
  -- ⊢ Disjoint x y → Disjoint x.fst y.fst ∧ Disjoint x.snd y.snd
  · intro h
    -- ⊢ Disjoint x.fst y.fst ∧ Disjoint x.snd y.snd
    refine' ⟨fun a hx hy ↦ (@h (a, ⊥) ⟨hx, _⟩ ⟨hy, _⟩).1,
      fun b hx hy ↦ (@h (⊥, b) ⟨_, hx⟩ ⟨_, hy⟩).2⟩
    all_goals exact bot_le
    -- 🎉 no goals
  · rintro ⟨ha, hb⟩ z hza hzb
    -- ⊢ z ≤ ⊥
    refine' ⟨ha hza.1 hzb.1, hb hza.2 hzb.2⟩
    -- 🎉 no goals
#align prod.disjoint_iff Prod.disjoint_iff

protected theorem codisjoint_iff [OrderTop α] [OrderTop β] {x y : α × β} :
    Codisjoint x y ↔ Codisjoint x.1 y.1 ∧ Codisjoint x.2 y.2 :=
  @Prod.disjoint_iff αᵒᵈ βᵒᵈ _ _ _ _ _ _
#align prod.codisjoint_iff Prod.codisjoint_iff

protected theorem isCompl_iff [BoundedOrder α] [BoundedOrder β] {x y : α × β} :
    IsCompl x y ↔ IsCompl x.1 y.1 ∧ IsCompl x.2 y.2 := by
  simp_rw [isCompl_iff, Prod.disjoint_iff, Prod.codisjoint_iff, and_and_and_comm]
  -- 🎉 no goals
#align prod.is_compl_iff Prod.isCompl_iff

end Prod

section

variable [Lattice α] [BoundedOrder α] {a b x : α}

@[simp]
theorem isCompl_toDual_iff : IsCompl (toDual a) (toDual b) ↔ IsCompl a b :=
  ⟨IsCompl.ofDual, IsCompl.dual⟩
#align is_compl_to_dual_iff isCompl_toDual_iff

@[simp]
theorem isCompl_ofDual_iff {a b : αᵒᵈ} : IsCompl (ofDual a) (ofDual b) ↔ IsCompl a b :=
  ⟨IsCompl.dual, IsCompl.ofDual⟩
#align is_compl_of_dual_iff isCompl_ofDual_iff

theorem isCompl_bot_top : IsCompl (⊥ : α) ⊤ :=
  IsCompl.of_eq bot_inf_eq sup_top_eq
#align is_compl_bot_top isCompl_bot_top

theorem isCompl_top_bot : IsCompl (⊤ : α) ⊥ :=
  IsCompl.of_eq inf_bot_eq top_sup_eq
#align is_compl_top_bot isCompl_top_bot

theorem eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤ :=
  sup_bot_eq.symm.trans h.sup_eq_top
#align eq_top_of_is_compl_bot eq_top_of_isCompl_bot

theorem eq_top_of_bot_isCompl (h : IsCompl ⊥ x) : x = ⊤ :=
  eq_top_of_isCompl_bot h.symm
#align eq_top_of_bot_is_compl eq_top_of_bot_isCompl

theorem eq_bot_of_isCompl_top (h : IsCompl x ⊤) : x = ⊥ :=
  eq_top_of_isCompl_bot h.dual
#align eq_bot_of_is_compl_top eq_bot_of_isCompl_top

theorem eq_bot_of_top_isCompl (h : IsCompl ⊤ x) : x = ⊥ :=
  eq_top_of_bot_isCompl h.dual
#align eq_bot_of_top_is_compl eq_bot_of_top_isCompl

end

section IsComplemented

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- An element is *complemented* if it has a complement. -/
def IsComplemented (a : α) : Prop :=
  ∃ b, IsCompl a b
#align is_complemented IsComplemented

theorem isComplemented_bot : IsComplemented (⊥ : α) :=
  ⟨⊤, isCompl_bot_top⟩
#align is_complemented_bot isComplemented_bot

theorem isComplemented_top : IsComplemented (⊤ : α) :=
  ⟨⊥, isCompl_top_bot⟩
#align is_complemented_top isComplemented_top

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : α}

theorem IsComplemented.sup : IsComplemented a → IsComplemented b → IsComplemented (a ⊔ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊓ b', ha.sup_inf hb⟩
#align is_complemented.sup IsComplemented.sup

theorem IsComplemented.inf : IsComplemented a → IsComplemented b → IsComplemented (a ⊓ b) :=
  fun ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' ⊔ b', ha.inf_sup hb⟩
#align is_complemented.inf IsComplemented.inf

end IsComplemented

/-- A complemented bounded lattice is one where every element has a (not necessarily unique)
complement. -/
class ComplementedLattice (α) [Lattice α] [BoundedOrder α] : Prop where
  /-- In a `ComplementedLattice`, every element admits a complement. -/
  exists_isCompl : ∀ a : α, ∃ b : α, IsCompl a b
#align complemented_lattice ComplementedLattice

export ComplementedLattice (exists_isCompl)

namespace ComplementedLattice

variable [Lattice α] [BoundedOrder α] [ComplementedLattice α]

instance : ComplementedLattice αᵒᵈ :=
  ⟨fun a ↦
    let ⟨b, hb⟩ := exists_isCompl (show α from a)
    ⟨b, hb.dual⟩⟩

end ComplementedLattice

-- TODO: Define as a sublattice?
/-- The sublattice of complemented elements. -/
@[reducible]
def Complementeds (α : Type*) [Lattice α] [BoundedOrder α] : Type _ := {a : α // IsComplemented a}
#align complementeds Complementeds

namespace Complementeds

section Lattice

variable [Lattice α] [BoundedOrder α] {a b : Complementeds α}

instance hasCoeT : CoeTC (Complementeds α) α := ⟨Subtype.val⟩
#align complementeds.has_coe_t Complementeds.hasCoeT

theorem coe_injective : Injective ((↑) : Complementeds α → α) := Subtype.coe_injective
#align complementeds.coe_injective Complementeds.coe_injective

@[simp, norm_cast]
theorem coe_inj : (a : α) = b ↔ a = b := Subtype.coe_inj
#align complementeds.coe_inj Complementeds.coe_inj

-- porting note: removing `simp` because `Subtype.coe_le_coe` already proves it
@[norm_cast]
theorem coe_le_coe : (a : α) ≤ b ↔ a ≤ b := by simp
                                               -- 🎉 no goals
#align complementeds.coe_le_coe Complementeds.coe_le_coe

-- porting note: removing `simp` because `Subtype.coe_lt_coe` already proves it
@[norm_cast]
theorem coe_lt_coe : (a : α) < b ↔ a < b := Iff.rfl
#align complementeds.coe_lt_coe Complementeds.coe_lt_coe

instance : BoundedOrder (Complementeds α) :=
  Subtype.boundedOrder isComplemented_bot isComplemented_top

@[simp, norm_cast]
theorem coe_bot : ((⊥ : Complementeds α) : α) = ⊥ := rfl
#align complementeds.coe_bot Complementeds.coe_bot

@[simp, norm_cast]
theorem coe_top : ((⊤ : Complementeds α) : α) = ⊤ := rfl
#align complementeds.coe_top Complementeds.coe_top

-- porting note: removing `simp` because `Subtype.mk_bot` already proves it
theorem mk_bot : (⟨⊥, isComplemented_bot⟩ : Complementeds α) = ⊥ := rfl
#align complementeds.mk_bot Complementeds.mk_bot

-- porting note: removing `simp` because `Subtype.mk_top` already proves it
theorem mk_top : (⟨⊤, isComplemented_top⟩ : Complementeds α) = ⊤ := rfl
#align complementeds.mk_top Complementeds.mk_top

instance : Inhabited (Complementeds α) := ⟨⊥⟩

end Lattice

variable [DistribLattice α] [BoundedOrder α] {a b : Complementeds α}

instance : Sup (Complementeds α) :=
  ⟨fun a b => ⟨a ⊔ b, a.2.sup b.2⟩⟩

instance : Inf (Complementeds α) :=
  ⟨fun a b => ⟨a ⊓ b, a.2.inf b.2⟩⟩

@[simp, norm_cast]
theorem coe_sup (a b : Complementeds α) : ↑(a ⊔ b) = (a : α) ⊔ b := rfl
#align complementeds.coe_sup Complementeds.coe_sup

@[simp, norm_cast]
theorem coe_inf (a b : Complementeds α) : ↑(a ⊓ b) = (a : α) ⊓ b := rfl
#align complementeds.coe_inf Complementeds.coe_inf

@[simp]
theorem mk_sup_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊔ b, ha.sup hb⟩ := rfl
#align complementeds.mk_sup_mk Complementeds.mk_sup_mk

@[simp]
theorem mk_inf_mk {a b : α} (ha : IsComplemented a) (hb : IsComplemented b) :
    (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : Complementeds α) = ⟨a ⊓ b, ha.inf hb⟩ := rfl
#align complementeds.mk_inf_mk Complementeds.mk_inf_mk

instance : DistribLattice (Complementeds α) :=
  Complementeds.coe_injective.distribLattice _ coe_sup coe_inf

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (a : α) b ↔ Disjoint a b := by
  rw [disjoint_iff, disjoint_iff, ← coe_inf, ← coe_bot, coe_inj]
  -- 🎉 no goals
#align complementeds.disjoint_coe Complementeds.disjoint_coe

@[simp, norm_cast]
theorem codisjoint_coe : Codisjoint (a : α) b ↔ Codisjoint a b := by
  rw [codisjoint_iff, codisjoint_iff, ← coe_sup, ← coe_top, coe_inj]
  -- 🎉 no goals
#align complementeds.codisjoint_coe Complementeds.codisjoint_coe

@[simp, norm_cast]
theorem isCompl_coe : IsCompl (a : α) b ↔ IsCompl a b := by
  simp_rw [isCompl_iff, disjoint_coe, codisjoint_coe]
  -- 🎉 no goals
#align complementeds.is_compl_coe Complementeds.isCompl_coe

instance : ComplementedLattice (Complementeds α) :=
  ⟨fun ⟨a, b, h⟩ => ⟨⟨b, a, h.symm⟩, isCompl_coe.1 h⟩⟩

end Complementeds
end IsCompl
