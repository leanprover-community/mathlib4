/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Order.Disjoint

/-!

# The order on `Prop`

Instances on `Prop` such as `DistribLattice`, `BoundedOrder`, `LinearOrder`.

-/

/-- Propositions form a distributive lattice. -/
instance Prop.instDistribLattice : DistribLattice Prop where
  sup := Or
  le_sup_left := @Or.inl
  le_sup_right := @Or.inr
  sup_le := fun _ _ _ => Or.rec
  inf := And
  inf_le_left := @And.left
  inf_le_right := @And.right
  le_inf := fun _ _ _ Hab Hac Ha => And.intro (Hab Ha) (Hac Ha)
  le_sup_inf := fun _ _ _ => or_and_left.2

/-- Propositions form a bounded order. -/
instance Prop.instBoundedOrder : BoundedOrder Prop where
  top := True
  le_top _ _ := True.intro
  bot := False
  bot_le := @False.elim

@[simp]
theorem Prop.bot_eq_false : (⊥ : Prop) = False :=
  rfl

@[simp]
theorem Prop.top_eq_true : (⊤ : Prop) = True :=
  rfl

instance Prop.le_isTotal : IsTotal Prop (· ≤ ·) :=
  ⟨fun p q => by by_cases h : q <;> simp [h]⟩

noncomputable instance Prop.linearOrder : LinearOrder Prop := by
  classical
  exact Lattice.toLinearOrder Prop

@[simp]
theorem sup_Prop_eq : (· ⊔ ·) = (· ∨ ·) :=
  rfl

@[simp]
theorem inf_Prop_eq : (· ⊓ ·) = (· ∧ ·) :=
  rfl

namespace Pi

variable {ι : Type*} {α' : ι → Type*} [∀ i, PartialOrder (α' i)]

theorem disjoint_iff [∀ i, OrderBot (α' i)] {f g : ∀ i, α' i} :
    Disjoint f g ↔ ∀ i, Disjoint (f i) (g i) := by
  classical
  constructor
  · intro h i x hf hg
    exact (update_le_iff.mp <| h (update_le_iff.mpr ⟨hf, fun _ _ => bot_le⟩)
      (update_le_iff.mpr ⟨hg, fun _ _ => bot_le⟩)).1
  · intro h x hf hg i
    apply h i (hf i) (hg i)

theorem codisjoint_iff [∀ i, OrderTop (α' i)] {f g : ∀ i, α' i} :
    Codisjoint f g ↔ ∀ i, Codisjoint (f i) (g i) :=
  @disjoint_iff _ (fun i => (α' i)ᵒᵈ) _ _ _ _

theorem isCompl_iff [∀ i, BoundedOrder (α' i)] {f g : ∀ i, α' i} :
    IsCompl f g ↔ ∀ i, IsCompl (f i) (g i) := by
  simp_rw [_root_.isCompl_iff, disjoint_iff, codisjoint_iff, forall_and]

end Pi

@[simp]
theorem Prop.disjoint_iff {P Q : Prop} : Disjoint P Q ↔ ¬(P ∧ Q) :=
  disjoint_iff_inf_le

@[simp]
theorem Prop.codisjoint_iff {P Q : Prop} : Codisjoint P Q ↔ P ∨ Q :=
  codisjoint_iff_le_sup.trans <| forall_const True

@[simp]
theorem Prop.isCompl_iff {P Q : Prop} : IsCompl P Q ↔ ¬(P ↔ Q) := by
  rw [_root_.isCompl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff]
  by_cases P <;> by_cases Q <;> simp [*]

section decidable_instances

universe u
variable {α : Type u}

instance Prop.decidablePredBot : DecidablePred (⊥ : α → Prop) := fun _ => instDecidableFalse

instance Prop.decidablePredTop : DecidablePred (⊤ : α → Prop) := fun _ => instDecidableTrue

instance Prop.decidableRelBot : DecidableRel (⊥ : α → α → Prop) := fun _ _ => instDecidableFalse

instance Prop.decidableRelTop : DecidableRel (⊤ : α → α → Prop) := fun _ _ => instDecidableTrue

end decidable_instances
