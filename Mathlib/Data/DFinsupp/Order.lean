/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.DFinsupp.Module

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `DFinsupp.orderEmbeddingToFun`: The order embedding from finitely supported dependent functions
  to functions.

-/

open Finset

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

/-! ### Order structures -/


section Zero
variable [∀ i, Zero (α i)]

section LE
variable [∀ i, LE (α i)] {f g : Π₀ i, α i}

instance : LE (Π₀ i, α i) :=
  ⟨fun f g ↦ ∀ i, f i ≤ g i⟩

lemma le_def : f ≤ g ↔ ∀ i, f i ≤ g i := Iff.rfl

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := Iff.rfl

/-- The order on `DFinsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o ∀ i, α i where
  toFun := DFunLike.coe
  inj' := DFunLike.coe_injective
  map_rel_iff' := Iff.rfl

@[simp, norm_cast]
lemma coe_orderEmbeddingToFun : ⇑(orderEmbeddingToFun (α := α)) = DFunLike.coe := rfl

theorem orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} :
    orderEmbeddingToFun f i = f i :=
  rfl

end LE

section Preorder
variable [∀ i, Preorder (α i)] {f g : Π₀ i, α i}

instance : Preorder (Π₀ i, α i) :=
  { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun _ _ ↦ le_rfl
    le_trans := fun _ _ _ hfg hgh i ↦ (hfg i).trans (hgh i) }

lemma lt_def : f < g ↔ f ≤ g ∧ ∃ i, f i < g i := Pi.lt_def
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := Iff.rfl

lemma coe_mono : Monotone ((⇑) : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ id

lemma coe_strictMono : Monotone ((⇑) : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ id

end Preorder

instance [∀ i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i) :=
  { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf ↦ ext fun i ↦ (hfg i).antisymm (hgf i) }

instance [∀ i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    min := zipWith (fun _ ↦ (· ⊓ ·)) fun _ ↦ inf_idem _
    inf_le_left := fun _ _ _ ↦ inf_le_left
    inf_le_right := fun _ _ _ ↦ inf_le_right
    le_inf := fun _ _ _ hf hg i ↦ le_inf (hf i) (hg i) }

@[simp, norm_cast]
lemma coe_inf [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) : f ⊓ g = ⇑f ⊓ g := rfl

theorem inf_apply [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  zipWith_apply _ _ _ _ _

instance [∀ i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    max := zipWith (fun _ ↦ (· ⊔ ·)) fun _ ↦ sup_idem _
    le_sup_left := fun _ _ _ ↦ le_sup_left
    le_sup_right := fun _ _ _ ↦ le_sup_right
    sup_le := fun _ _ _ hf hg i ↦ sup_le (hf i) (hg i) }

@[simp, norm_cast]
lemma coe_sup [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) : f ⊔ g = ⇑f ⊔ g := rfl

theorem sup_apply [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  zipWith_apply _ _ _ _ _

section Lattice
variable [∀ i, Lattice (α i)] (f g : Π₀ i, α i)

instance lattice : Lattice (Π₀ i, α i) :=
  { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }

variable [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)]

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _

end Lattice
end Zero

/-! ### Algebraic order structures -/

instance (α : ι → Type*) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedAddMonoid (α i)] : IsOrderedAddMonoid (Π₀ i, α i) :=
  { add_le_add_left := fun _ _ h c i ↦ add_le_add_left (h i) (c i) }

instance (α : ι → Type*) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Π₀ i, α i) :=
  { le_of_add_le_add_left := fun _ _ _ H i ↦ le_of_add_le_add_left (H i) }

instance [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, AddLeftReflectLE (α i)] :
    AddLeftReflectLE (Π₀ i, α i) :=
  ⟨fun _ _ _ H i ↦ le_of_add_le_add_left (H i)⟩

section Module
variable {α : Type*} {β : ι → Type*} [Semiring α] [Preorder α] [∀ i, AddCommMonoid (β i)]
  [∀ i, Preorder (β i)] [∀ i, Module α (β i)]

instance instPosSMulMono [∀ i, PosSMulMono α (β i)] : PosSMulMono α (Π₀ i, β i) :=
  PosSMulMono.lift _ coe_le_coe coe_smul

instance instSMulPosMono [∀ i, SMulPosMono α (β i)] : SMulPosMono α (Π₀ i, β i) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

instance instPosSMulReflectLE [∀ i, PosSMulReflectLE α (β i)] : PosSMulReflectLE α (Π₀ i, β i) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul

instance instSMulPosReflectLE [∀ i, SMulPosReflectLE α (β i)] : SMulPosReflectLE α (Π₀ i, β i) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end Module

section Module
variable {α : Type*} {β : ι → Type*} [Semiring α] [PartialOrder α] [∀ i, AddCommMonoid (β i)]
  [∀ i, PartialOrder (β i)] [∀ i, Module α (β i)]

instance instPosSMulStrictMono [∀ i, PosSMulStrictMono α (β i)] : PosSMulStrictMono α (Π₀ i, β i) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul

instance instSMulPosStrictMono [∀ i, SMulPosStrictMono α (β i)] : SMulPosStrictMono α (Π₀ i, β i) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- Note: There is no interesting instance for `PosSMulReflectLT α (Π₀ i, β i)` that's not already
-- implied by the other instances

instance instSMulPosReflectLT [∀ i, SMulPosReflectLT α (β i)] : SMulPosReflectLT α (Π₀ i, β i) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end Module

section PartialOrder

variable (α) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)] [∀ i, CanonicallyOrderedAdd (α i)]

instance : OrderBot (Π₀ i, α i) where
  bot := 0
  bot_le := by simp only [le_def, coe_zero, Pi.zero_apply, imp_true_iff, zero_le]

variable {α}

protected theorem bot_eq_zero : (⊥ : Π₀ i, α i) = 0 :=
  rfl

@[simp]
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]

section LE

variable [DecidableEq ι]

section

variable [∀ (i) (x : α i), Decidable (x ≠ 0)] {f g : Π₀ i, α i} {s : Finset ι}

theorem le_iff' (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _ ↦ h s, fun h s ↦
    if H : s ∈ f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le (g s)⟩

theorem le_iff : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' <| Subset.refl _

lemma support_monotone : Monotone (support (ι := ι) (β := α)) :=
  fun f g h a ha ↦ by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

lemma support_mono (hfg : f ≤ g) : f.support ⊆ g.support := support_monotone hfg

variable (α) in
instance decidableLE [∀ i, DecidableLE (α i)] : DecidableLE (Π₀ i, α i) :=
  fun _ _ ↦ decidable_of_iff _ le_iff.symm

end

@[simp]
theorem single_le_iff {f : Π₀ i, α i} {i : ι} {a : α i} :
    single i a ≤ f ↔ a ≤ f i := by
  classical exact (le_iff' support_single_subset).trans <| by simp

end LE

variable (α) [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun _ m n ↦ m - n) fun _ ↦ tsub_self 0⟩

variable {α}

theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zipWith_apply _ _ _ _ _

@[simp, norm_cast]
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  exact tsub_apply f g i

variable (α)

instance : OrderedSub (Π₀ i, α i) :=
  ⟨fun _ _ _ ↦ forall_congr' fun _ ↦ tsub_le_iff_right⟩

instance [∀ i, AddLeftMono (α i)] : CanonicallyOrderedAdd (Π₀ i, α i) where
  exists_add_of_le := by
    intro f g h
    exists g - f
    ext i
    exact (add_tsub_cancel_of_le <| h i).symm
  le_add_self := fun _ _ _ ↦ le_add_self
  le_self_add := fun _ _ _ ↦ le_self_add

variable {α} [DecidableEq ι]

@[simp]
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

variable [∀ (i) (x : α i), Decidable (x ≠ 0)]

theorem support_tsub : (f - g).support ⊆ f.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

theorem subset_support_tsub : f.support \ g.support ⊆ (f - g).support := by
  simp +contextual [subset_iff]

end PartialOrder

section LinearOrder
variable [∀ i, AddCommMonoid (α i)] [∀ i, LinearOrder (α i)] [∀ i, CanonicallyOrderedAdd (α i)]
  [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
theorem support_inf : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  simp only [inf_apply, mem_support_iff, Ne, Finset.mem_inter]
  simp only [← nonpos_iff_eq_zero, min_le_iff, not_or]

@[simp]
theorem support_sup : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne, ← nonpos_iff_eq_zero, sup_le_iff,
    Classical.not_and_iff_not_or_not]

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  rw [disjoint_iff, disjoint_iff, DFinsupp.bot_eq_zero, ← DFinsupp.support_eq_empty,
    DFinsupp.support_inf]
  rfl

end LinearOrder

end DFinsupp
