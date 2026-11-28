/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Order dual

This file defines `OrderDual α`, a one-field structure around a type that reverses the meaning of
all inequalities.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.
-/

@[expose] public section

assert_not_exists Lex

variable {α : Type*}

/-- Structure to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
@[ext]
structure OrderDual (α : Type*) where
  /-- `toDual a` is `a` in the dual order. -/
  toDual ::
  /-- `ofDual a` is `a` in the original order. -/
  ofDual : α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

@[simp] theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a := rfl
@[simp] theorem ofDual_toDual (a : α) : ofDual (toDual a) = a := rfl
@[simp] theorem toDual_comp_ofDual : (toDual (α := α)) ∘ ofDual = id := rfl
@[simp] theorem ofDual_comp_toDual : (ofDual (α := α)) ∘ toDual = id := rfl

theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b := by simp
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b := by rw [← toDual_inj]

instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  ⟨toDual h.some⟩

instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ where
  allEq a b := by simpa [ofDual_inj] using h.allEq (ofDual a) (ofDual b)

instance (α : Type*) [LE α] : LE αᵒᵈ where
  le a b := ofDual b ≤ ofDual a

instance (α : Type*) [LT α] : LT αᵒᵈ where
  lt a b := ofDual b < ofDual a

instance (α : Type*) [Ord α] : Ord αᵒᵈ where
  compare a b := compare (ofDual b) (ofDual a)

@[to_dual]
instance (α : Type*) [Min α] : Max αᵒᵈ where
  max a b := ⟨min (ofDual a) (ofDual b)⟩

instance [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

instance [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab

instance [LT α] [T : @Std.Trichotomous α LT.lt] : @Std.Trichotomous αᵒᵈ LT.lt where
  trichotomous a b := by rw [eq_comm, ← ofDual_inj]; exact T.trichotomous (ofDual b) (ofDual a)

instance (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

instance (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  le_antisymm _ _ hab hba := ofDual_inj.mp (le_antisymm hba hab)

instance (α : Type*) [DecidableEq α] : DecidableEq αᵒᵈ :=
  fun a b ↦ by rw [← ofDual_inj]; infer_instance

instance (α : Type*) [LT α] [h : DecidableLT α] : DecidableLT (αᵒᵈ) :=
  fun a b ↦ h (ofDual b) (ofDual a)

instance (α : Type*) [LE α] [h : DecidableLE α] : DecidableLE (αᵒᵈ) :=
  fun a b ↦ h (ofDual b) (ofDual a)

instance (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  le_total a b := le_total (ofDual b) (ofDual a)
  min_def _ _ := by rw [toDual_inj, apply_ite ofDual]; exact max_def' ..
  max_def _ _ := by rw [toDual_inj, apply_ite ofDual]; exact min_def' ..
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, ofDual_inj,
      eq_comm]
    rfl

instance [h : Inhabited α] : Inhabited αᵒᵈ := ⟨toDual h.default⟩

--theorem Ord.dual_dual (α : Type*) [H : Ord α] : OrderDual.instOrd αᵒᵈ = H :=
--  rfl

--theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
--  rfl

--theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
--    OrderDual.instPartialOrder αᵒᵈ = H :=
--  rfl

--theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
--    OrderDual.instLinearOrder αᵒᵈ = H :=
--  rfl

instance [h : Nontrivial α] : Nontrivial αᵒᵈ where
  exists_pair_ne := by
    obtain ⟨x, y, hn⟩ := h
    exact ⟨toDual x, toDual y, by simp_all⟩

instance [h : Unique α] : Unique αᵒᵈ where uniq a := toDual_inj.mpr (h.uniq a.ofDual)

@[to_dual self, simp]
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a := .rfl

@[to_dual self, simp]
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a := .rfl

@[to_dual toDual_le]
theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a := .rfl

@[to_dual toDual_lt]
theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a := .rfl

@[simp] protected theorem «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  ⟨fun h a ↦ h (toDual a), fun h a ↦ h (ofDual a)⟩

@[simp] protected theorem «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  ⟨fun ⟨a, ha⟩ ↦ ⟨ofDual a, ha⟩, fun ⟨a, ha⟩ ↦ ⟨toDual a, ha⟩⟩

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

@[deprecated (since := "2026-10-20")] alias toDual_symm_eq := toDual_ofDual
@[deprecated (since := "2026-10-20")] alias ofDual_symm_eq := ofDual_toDual
@[deprecated (since := "2026-10-20")] alias toDual_trans_ofDual := toDual_comp_ofDual
@[deprecated (since := "2026-10-20")] alias ofDual_trans_toDual := ofDual_comp_toDual

/-- The natural equivalence between `α` and `αᵒᵈ`. -/
@[simps]
def equiv : α ≃ αᵒᵈ where
  toFun := toDual
  invFun := ofDual

end OrderDual

/-! ### `DenselyOrdered` for `OrderDual` -/

instance OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun x y l ↦ by
    obtain ⟨a, ha⟩ := h.dense (ofDual y) (ofDual x) (by simp [l])
    exact ⟨_, ha.2, ha.1⟩⟩

@[simp]
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α := by
  refine ⟨fun h ↦ ⟨fun x y l ↦ ?_⟩, @OrderDual.denselyOrdered α _⟩
  obtain ⟨a, ha⟩ := h.dense (.toDual y) (.toDual x) (by simp [l])
  exact ⟨_, ha.2, ha.1⟩

/-! ### Pushing order definitions through `Equiv` -/

namespace Equiv

variable {β : Type*} (e : α ≃ β)

/-- Transfer `Top` across an `Equiv`. -/
protected abbrev top [Top β] : Top α where
  top := e.symm ⊤

lemma top_def [Top β] :
    letI := e.top
    ⊤ = e.symm ⊤ := rfl

/-- Transfer `Bot` across an `Equiv`. -/
protected abbrev bot [Bot β] : Bot α where
  bot := e.symm ⊥

lemma bot_def [Bot β] :
    letI := e.bot
    ⊥ = e.symm ⊥ := rfl

/-- Transfer `Compl` across an `Equiv`. -/
protected abbrev compl [Compl β] : Compl α where
  compl a := e.symm (e a)ᶜ

lemma compl_def [Compl β] (a : α) :
    letI := e.compl
    aᶜ = e.symm (e a)ᶜ := rfl

/-- Transfer `SDiff` across an `Equiv`. -/
protected abbrev sdiff [SDiff β] : SDiff α where
  sdiff a b := e.symm (e a \ e b)

lemma sdiff_def [SDiff β] (a b : α) :
    letI := e.sdiff
    a \ b = e.symm (e a \ e b) := rfl

/-- Transfer `HImp` across an `Equiv`. -/
protected abbrev himp [HImp β] : HImp α where
  himp a b := e.symm (e a ⇨ e b)

lemma himp_def [HImp β] (a b : α) :
    letI := e.himp
    a ⇨ b = e.symm (e a ⇨ e b) := rfl

/-- Transfer `HNot` across an `Equiv`. -/
protected abbrev hnot [HNot β] : HNot α where
  hnot a := e.symm (￢e a)

lemma hnot_def [HNot β] (a : α) :
    letI := e.hnot
    ￢a = e.symm (￢e a) := rfl

end Equiv
