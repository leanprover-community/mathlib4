/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Order.Preorder.Finsupp

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `α` to `ι →₀ α`.

## Main declarations

* `Finsupp.orderEmbeddingToFun`: The order embedding from finitely supported functions to
  functions.
-/

noncomputable section

open Finset

variable {ι κ α β : Type*}

namespace Finsupp

/-! ### Order structures -/


section Zero

variable [Zero α]

section OrderedAddCommMonoid
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] {f : ι →₀ α} {h₁ h₂ : ι → α → β}

@[gcongr]
lemma sum_le_sum (h : ∀ i ∈ f.support, h₁ i (f i) ≤ h₂ i (f i)) : f.sum h₁ ≤ f.sum h₂ :=
  Finset.sum_le_sum h

end OrderedAddCommMonoid

section Preorder
variable [Preorder α] {f g : ι →₀ α} {i : ι} {a b : α}

@[simp] lemma single_le_single : single i a ≤ single i b ↔ a ≤ b := by
  classical exact Pi.single_le_single

lemma single_mono : Monotone (single i : α → ι →₀ α) := fun _ _ ↦ single_le_single.2

@[gcongr] protected alias ⟨_, GCongr.single_mono⟩ := single_le_single

@[simp] lemma single_nonneg : 0 ≤ single i a ↔ 0 ≤ a := by classical exact Pi.single_nonneg
@[simp] lemma single_nonpos : single i a ≤ 0 ↔ a ≤ 0 := by classical exact Pi.single_nonpos

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]

lemma sum_le_sum_index [DecidableEq ι] {f₁ f₂ : ι →₀ α} {h : ι → α → β} (hf : f₁ ≤ f₂)
    (hh : ∀ i ∈ f₁.support ∪ f₂.support, Monotone (h i))
    (hh₀ : ∀ i ∈ f₁.support ∪ f₂.support, h i 0 = 0) : f₁.sum h ≤ f₂.sum h := by
  classical
  rw [sum_of_support_subset _ Finset.subset_union_left _ hh₀,
    sum_of_support_subset _ Finset.subset_union_right _ hh₀]
  exact Finset.sum_le_sum fun i hi ↦ hh _ hi <| hf _

end Preorder
end Zero

/-! ### Algebraic order structures -/

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
  {i : ι} {f : ι → κ} {g g₁ g₂ : ι →₀ α}

instance isOrderedAddMonoid : IsOrderedAddMonoid (ι →₀ α) :=
  { add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

@[gcongr]
lemma mapDomain_mono : Monotone (mapDomain f : (ι →₀ α) → (κ →₀ α)) := by
  classical exact fun g₁ g₂ h ↦ sum_le_sum_index h (fun _ _ ↦ single_mono) (by simp)

lemma mapDomain_nonneg (hg : 0 ≤ g) : 0 ≤ g.mapDomain f := by simpa using mapDomain_mono hg
lemma mapDomain_nonpos (hg : g ≤ 0) : g.mapDomain f ≤ 0 := by simpa using mapDomain_mono hg

end OrderedAddCommMonoid

instance isOrderedCancelAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid (ι →₀ α) :=
  { le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }

instance addLeftReflectLE [AddCommMonoid α] [PartialOrder α] [AddLeftReflectLE α] :
    AddLeftReflectLE (ι →₀ α) :=
  ⟨fun _f _g _h H x => le_of_add_le_add_left <| H x⟩

section SMulZeroClass
variable [Zero α] [Preorder α] [Zero β] [Preorder β] [SMulZeroClass α β]

instance instPosSMulMono [PosSMulMono α β] : PosSMulMono α (ι →₀ β) :=
  PosSMulMono.lift _ coe_le_coe coe_smul

instance instSMulPosMono [SMulPosMono α β] : SMulPosMono α (ι →₀ β) :=
  SMulPosMono.lift _ coe_le_coe coe_smul coe_zero

instance instPosSMulReflectLE [PosSMulReflectLE α β] : PosSMulReflectLE α (ι →₀ β) :=
  PosSMulReflectLE.lift _ coe_le_coe coe_smul

instance instSMulPosReflectLE [SMulPosReflectLE α β] : SMulPosReflectLE α (ι →₀ β) :=
  SMulPosReflectLE.lift _ coe_le_coe coe_smul coe_zero

end SMulZeroClass

section SMulWithZero
variable [Zero α] [PartialOrder α] [Zero β] [PartialOrder β] [SMulWithZero α β]

instance instPosSMulStrictMono [PosSMulStrictMono α β] : PosSMulStrictMono α (ι →₀ β) :=
  PosSMulStrictMono.lift _ coe_le_coe coe_smul

instance instSMulPosStrictMono [SMulPosStrictMono α β] : SMulPosStrictMono α (ι →₀ β) :=
  SMulPosStrictMono.lift _ coe_le_coe coe_smul coe_zero

-- `PosSMulReflectLT α (ι →₀ β)` already follows from the other instances

instance instSMulPosReflectLT [SMulPosReflectLT α β] : SMulPosReflectLT α (ι →₀ β) :=
  SMulPosReflectLT.lift _ coe_le_coe coe_smul coe_zero

end SMulWithZero

section PartialOrder

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α] {f g : ι →₀ α}

instance orderBot : OrderBot (ι →₀ α) where
  bot := 0
  bot_le := by simp only [le_def, coe_zero, Pi.zero_apply, imp_true_iff, zero_le]

protected theorem bot_eq_zero : (⊥ : ι →₀ α) = 0 :=
  rfl

@[simp]
theorem add_eq_zero_iff (f g : ι →₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [DFunLike.ext_iff, forall_and]

theorem le_iff' (f g : ι →₀ α) {s : Finset ι} (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _hs => h s, fun h s => by
    classical exact
        if H : s ∈ f.support then h s (hf H) else (notMem_support_iff.1 H).symm ▸ zero_le (g s)⟩

theorem le_iff (f g : ι →₀ α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' f g <| Subset.refl _

lemma support_monotone : Monotone (support (α := ι) (M := α)) :=
  fun f g h a ha ↦ by rw [mem_support_iff, ← pos_iff_ne_zero] at ha ⊢; exact ha.trans_le (h _)

lemma support_mono (hfg : f ≤ g) : f.support ⊆ g.support := support_monotone hfg

instance decidableLE [DecidableLE α] : DecidableLE (ι →₀ α) := fun f g =>
  decidable_of_iff _ (le_iff f g).symm

instance decidableLT [DecidableLE α] : DecidableLT (ι →₀ α) :=
  decidableLTOfDecidableLE

@[simp]
theorem single_le_iff {i : ι} {x : α} {f : ι →₀ α} : single i x ≤ f ↔ x ≤ f i :=
  (le_iff' _ _ support_single_subset).trans <| by simp

variable [Sub α] [OrderedSub α] {f g : ι →₀ α} {i : ι} {a b : α}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (ι →₀ α) :=
  ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩

instance orderedSub : OrderedSub (ι →₀ α) :=
  ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩

instance [AddLeftMono α] : CanonicallyOrderedAdd (ι →₀ α) where
  exists_add_of_le := fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
  le_add_self _ _ _ := le_add_self
  le_self_add := fun _f _g _x => le_self_add

@[simp, norm_cast] lemma coe_tsub (f g : ι →₀ α) : ⇑(f - g) = f - g := rfl

theorem tsub_apply (f g : ι →₀ α) (a : ι) : (f - g) a = f a - g a :=
  rfl

@[simp]
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne j i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]

theorem support_tsub {f1 f2 : ι →₀ α} : (f1 - f2).support ⊆ f1.support := by
  simp +contextual only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]

theorem subset_support_tsub [DecidableEq ι] {f1 f2 : ι →₀ α} :
    f1.support \ f2.support ⊆ (f1 - f2).support := by
  simp +contextual [subset_iff]

end PartialOrder

section LinearOrder

variable [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α]

@[simp]
theorem support_inf [DecidableEq ι] (f g : ι →₀ α) : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  simp only [inf_apply, mem_support_iff, Ne,
    Finset.mem_inter]
  simp only [← nonpos_iff_eq_zero, min_le_iff, not_or]

@[simp]
theorem support_sup [DecidableEq ι] (f g : ι →₀ α) : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  simp only [mem_support_iff, Ne, sup_apply, ← nonpos_iff_eq_zero, sup_le_iff, mem_union,
    not_and_or]

nonrec theorem disjoint_iff {f g : ι →₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
    rw [disjoint_iff, disjoint_iff, Finsupp.bot_eq_zero, ← Finsupp.support_eq_empty,
      Finsupp.support_inf]
    rfl

end LinearOrder

/-! ### Some lemmas about `ℕ` -/


section Nat

theorem sub_single_one_add {a : ι} {u u' : ι →₀ ℕ} (h : u a ≠ 0) :
    u - single a 1 + u' = u + u' - single a 1 :=
  tsub_add_eq_add_tsub <| single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h

theorem add_sub_single_one {a : ι} {u u' : ι →₀ ℕ} (h : u' a ≠ 0) :
    u + (u' - single a 1) = u + u' - single a 1 :=
  (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm

lemma sub_add_single_one_cancel {u : ι →₀ ℕ} {i : ι} (h : u i ≠ 0) :
    u - single i 1 + single i 1 = u := by
  rw [sub_single_one_add h, add_tsub_cancel_right]

end Nat

end Finsupp
