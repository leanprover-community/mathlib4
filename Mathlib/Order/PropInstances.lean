/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Disjoint
import Mathlib.Order.WithBot

#align_import order.prop_instances from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!

# The order on `Prop`

Instances on `Prop` such as `DistribLattice`, `BoundedOrder`, `LinearOrder`.

-/

set_option autoImplicit true


/-- Propositions form a distributive lattice. -/
instance Prop.distribLattice : DistribLattice Prop where
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2
#align Prop.distrib_lattice Prop.distribLattice

/-- Propositions form a bounded order. -/
instance Prop.boundedOrder : BoundedOrder Prop where
  top := True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim
#align Prop.bounded_order Prop.boundedOrder

theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl
#align Prop.bot_eq_false Prop.bot_eq_false

theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl
#align Prop.top_eq_true Prop.top_eq_true

instance Prop.le_isTotal : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by by_cases h : q <;> simp [h]⟩
                 -- ⊢ p ≤ q ∨ q ≤ p
                                    -- 🎉 no goals
                                    -- 🎉 no goals
#align Prop.le_is_total Prop.le_isTotal

noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical
  exact Lattice.toLinearOrder Prop
#align Prop.linear_order Prop.linearOrder

@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl
#align sup_Prop_eq sup_Prop_eq

@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl
#align inf_Prop_eq inf_Prop_eq

namespace Pi

variable {ι : Type*} {α' : ι → Type*} [∀ i, PartialOrder (α' i)]

theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} :
    Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  classical
  constructor
  · intro h i x hf hg
    refine' (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => _⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => _⟩)).1
    · exact bot_le
    · exact bot_le
  · intro h x hf hg i
    apply h i (hf i) (hg i)
#align pi.disjoint_iff Pi.disjoint_iff

theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} :
    Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _
#align pi.codisjoint_iff Pi.codisjoint_iff

theorem isCompl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} :
    IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]
  -- 🎉 no goals
#align pi.is_compl_iff Pi.isCompl_iff

end Pi

@[simp]
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le
#align Prop.disjoint_iff Prop.disjoint_iff

@[simp]
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const True
#align Prop.codisjoint_iff Prop.codisjoint_iff

@[simp]
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [_root_.isCompl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff]
  -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
  by_cases P <;> by_cases Q <;> simp [*]
  -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
  -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
                 -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
                 -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
                 -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
                 -- ⊢ ¬(P ∧ Q) ∧ (P ∨ Q) ↔ (¬P ↔ Q)
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
#align Prop.is_compl_iff Prop.isCompl_iff

-- porting note: Lean 3 would unfold these for us, but we need to do it manually now
section decidable_instances
variable {α : Type u}

instance Prop.decidablePredBot : DecidablePred (⊥ : α → Prop) := fun _ => instDecidableFalse

instance Prop.decidablePredTop : DecidablePred (⊤ : α → Prop) := fun _ => instDecidableTrue

instance Prop.decidableRelBot : DecidableRel (⊥ : α → α → Prop) := fun _ _ => instDecidableFalse

instance Prop.decidableRelTop : DecidableRel (⊤ : α → α → Prop) := fun _ _ => instDecidableTrue

end decidable_instances
