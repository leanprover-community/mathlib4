/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.dfinsupp.order
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Dfinsupp.Basic

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `Dfinsupp.orderEmbeddingToFun`: The order embedding from finitely supported dependent functions
  to functions.

-/

open BigOperators

open Finset

variable {ι : Type _} {α : ι → Type _}

namespace Dfinsupp

/-! ### Order structures -/


section Zero

-- porting note: The unusedVariables linter has false positives in code like
--    variable (α) [∀ i, Zero (α i)]
-- marking the `i` as unused. The linter is fine when the code is split into 2 lines.
-- Likely issue https://github.com/leanprover/lean4/issues/2088, so combine lines when that is fixed
variable (α)
variable [∀ i, Zero (α i)]

section LE

variable [∀ i, LE (α i)]

instance : LE (Π₀ i, α i) :=
  ⟨fun f g ↦ ∀ i, f i ≤ g i⟩

variable {α}

theorem le_def {f g : Π₀ i, α i} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl
#align dfinsupp.le_def Dfinsupp.le_def

/-- The order on `Dfinsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o ∀ i, α i where
  toFun := FunLike.coe
  inj' := FunLike.coe_injective
  map_rel_iff' := by rfl
#align dfinsupp.order_embedding_to_fun Dfinsupp.orderEmbeddingToFun

-- Porting note: we added implicit arguments here in #3414.
@[simp]
theorem orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} :
    (@orderEmbeddingToFun ι α _ _ f) i = f i :=
  rfl
#align dfinsupp.order_embedding_to_fun_apply Dfinsupp.orderEmbeddingToFun_apply

end LE

section Preorder

variable [∀ i, Preorder (α i)]

instance : Preorder (Π₀ i, α i) :=
  { (inferInstance : LE (Dfinsupp α)) with
    le_refl := fun f i ↦ le_rfl
    le_trans := fun f g h hfg hgh i ↦ (hfg i).trans (hgh i) }

theorem coeFn_mono : Monotone (FunLike.coe : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ le_def.1
#align dfinsupp.coe_fn_mono Dfinsupp.coeFn_mono

end Preorder

instance [∀ i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i) :=
  { (inferInstance : Preorder (Dfinsupp α)) with
    le_antisymm := fun _ _ hfg hgf ↦ ext fun i ↦ (hfg i).antisymm (hgf i) }

instance [∀ i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (Dfinsupp α)) with
    inf := zipWith (fun _ ↦ (· ⊓ ·)) fun _ ↦ inf_idem
    inf_le_left := fun _ _ _ ↦ inf_le_left
    inf_le_right := fun _ _ _ ↦ inf_le_right
    le_inf := fun _ _ _ hf hg i ↦ le_inf (hf i) (hg i) }

@[simp]
theorem inf_apply [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.inf_apply Dfinsupp.inf_apply

instance [∀ i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (Dfinsupp α)) with
    sup := zipWith (fun _ ↦ (· ⊔ ·)) fun _ ↦ sup_idem
    le_sup_left := fun _ _ _ ↦ le_sup_left
    le_sup_right := fun _ _ _ ↦ le_sup_right
    sup_le := fun _ _ _ hf hg i ↦ sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.sup_apply Dfinsupp.sup_apply

instance lattice [∀ i, Lattice (α i)] : Lattice (Π₀ i, α i) :=
  { (inferInstance : SemilatticeInf (Dfinsupp α)),
    (inferInstance : SemilatticeSup (Dfinsupp α)) with }
#align dfinsupp.lattice Dfinsupp.lattice

end Zero

/-! ### Algebraic order structures -/


instance (α : ι → Type _) [∀ i, OrderedAddCommMonoid (α i)] : OrderedAddCommMonoid (Π₀ i, α i) :=
  { (inferInstance : AddCommMonoid (Dfinsupp α)),
    (inferInstance : PartialOrder (Dfinsupp α)) with
    add_le_add_left := fun _ _ h c i ↦ add_le_add_left (h i) (c i) }

instance (α : ι → Type _) [∀ i, OrderedCancelAddCommMonoid (α i)] :
    OrderedCancelAddCommMonoid (Π₀ i, α i) :=
  { (inferInstance : OrderedAddCommMonoid (Dfinsupp α)) with
    le_of_add_le_add_left := fun _ _ _ H i ↦ le_of_add_le_add_left (H i) }

instance [∀ i, OrderedAddCommMonoid (α i)] [∀ i, ContravariantClass (α i) (α i) (· + ·) (· ≤ ·)] :
    ContravariantClass (Π₀ i, α i) (Π₀ i, α i) (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ H i ↦ le_of_add_le_add_left (H i)⟩

section CanonicallyOrderedAddMonoid

-- porting note: Split into 2 lines to satisfy the unusedVariables linter.
variable (α)
variable [∀ i, CanonicallyOrderedAddMonoid (α i)]

instance : OrderBot (Π₀ i, α i) where
  bot := 0
  bot_le := by simp only [le_def, coe_zero, Pi.zero_apply, imp_true_iff, zero_le]

variable {α}

protected theorem bot_eq_zero : (⊥ : Π₀ i, α i) = 0 :=
  rfl
#align dfinsupp.bot_eq_zero Dfinsupp.bot_eq_zero

@[simp]
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [FunLike.ext_iff, forall_and]
#align dfinsupp.add_eq_zero_iff Dfinsupp.add_eq_zero_iff

section LE

variable [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] {f g : Π₀ i, α i} {s : Finset ι}

theorem le_iff' (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _ ↦ h s, fun h s ↦
    if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩
#align dfinsupp.le_iff' Dfinsupp.le_iff'

theorem le_iff : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' <| Subset.refl _
#align dfinsupp.le_iff Dfinsupp.le_iff

variable (α)

instance decidableLE [∀ i, DecidableRel (@LE.le (α i) _)] : DecidableRel (@LE.le (Π₀ i, α i) _) :=
  fun _ _ ↦ decidable_of_iff _ le_iff.symm
#align dfinsupp.decidable_le Dfinsupp.decidableLE

variable {α}

@[simp]
theorem single_le_iff {i : ι} {a : α i} : single i a ≤ f ↔ a ≤ f i :=
  (le_iff' support_single_subset).trans <| by simp
#align dfinsupp.single_le_iff Dfinsupp.single_le_iff

end LE

-- porting note: Split into 2 lines to satisfy the unusedVariables linter.
variable (α)
variable [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun _ m n ↦ m - n) fun _ ↦ tsub_self 0⟩
#align dfinsupp.tsub Dfinsupp.tsub

variable {α}

theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.tsub_apply Dfinsupp.tsub_apply

@[simp]
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  exact tsub_apply f g i
#align dfinsupp.coe_tsub Dfinsupp.coe_tsub

variable (α)

instance : OrderedSub (Π₀ i, α i) :=
  ⟨fun _ _ _ ↦ forall_congr' fun _ ↦ tsub_le_iff_right⟩

instance : CanonicallyOrderedAddMonoid (Π₀ i, α i) :=
  { (inferInstance : OrderBot (Dfinsupp α)),
    (inferInstance : OrderedAddCommMonoid (Dfinsupp α)) with
    exists_add_of_le := by
      intro f g h
      exists g - f
      ext i
      exact (add_tsub_cancel_of_le <| h i).symm
    le_self_add := fun _ _ _ ↦ le_self_add }

variable {α} [DecidableEq ι]

@[simp]
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  obtain rfl | h := eq_or_ne i j
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]
#align dfinsupp.single_tsub Dfinsupp.single_tsub

variable [∀ (i) (x : α i), Decidable (x ≠ 0)]

theorem support_tsub : (f - g).support ⊆ f.support := by
  simp (config := { contextual := true }) only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne.def, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]
#align dfinsupp.support_tsub Dfinsupp.support_tsub

theorem subset_support_tsub : f.support \ g.support ⊆ (f - g).support := by
  simp (config := { contextual := true }) [subset_iff]
#align dfinsupp.subset_support_tsub Dfinsupp.subset_support_tsub

end CanonicallyOrderedAddMonoid

section CanonicallyLinearOrderedAddMonoid

variable [∀ i, CanonicallyLinearOrderedAddMonoid (α i)] [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
theorem support_inf : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  simp only [inf_apply, mem_support_iff, Ne.def, Finset.mem_inter]
  simp only [inf_eq_min, ← nonpos_iff_eq_zero, min_le_iff, not_or]
#align dfinsupp.support_inf Dfinsupp.support_inf

@[simp]
theorem support_sup : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne.def, ← bot_eq_zero]
  rw [_root_.sup_eq_bot_iff, not_and_or]
#align dfinsupp.support_sup Dfinsupp.support_sup

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  rw [disjoint_iff, disjoint_iff, Dfinsupp.bot_eq_zero, ← Dfinsupp.support_eq_empty,
    Dfinsupp.support_inf]
  rfl
#align dfinsupp.disjoint_iff Dfinsupp.disjoint_iff

end CanonicallyLinearOrderedAddMonoid

end Dfinsupp
