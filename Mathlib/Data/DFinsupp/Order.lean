/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.DFinsupp.Basic

#align_import data.dfinsupp.order from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Pointwise order on finitely supported dependent functions

This file lifts order structures on the `α i` to `Π₀ i, α i`.

## Main declarations

* `DFinsupp.orderEmbeddingToFun`: The order embedding from finitely supported dependent functions
  to functions.

-/

open BigOperators

open Finset

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

/-! ### Order structures -/


section Zero
variable [∀ i, Zero (α i)]

section LE

variable [∀ i, LE (α i)]

instance : LE (Π₀ i, α i) :=
  ⟨fun f g ↦ ∀ i, f i ≤ g i⟩

theorem le_def {f g : Π₀ i, α i} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl
#align dfinsupp.le_def DFinsupp.le_def

/-- The order on `DFinsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (Π₀ i, α i) ↪o ∀ i, α i where
  toFun := FunLike.coe
  inj' := FunLike.coe_injective
  map_rel_iff' := by rfl
                     -- 🎉 no goals
#align dfinsupp.order_embedding_to_fun DFinsupp.orderEmbeddingToFun

-- Porting note: we added implicit arguments here in #3414.
@[simp]
theorem orderEmbeddingToFun_apply {f : Π₀ i, α i} {i : ι} :
    (@orderEmbeddingToFun ι α _ _ f) i = f i :=
  rfl
#align dfinsupp.order_embedding_to_fun_apply DFinsupp.orderEmbeddingToFun_apply

end LE

section Preorder

variable [∀ i, Preorder (α i)]

instance : Preorder (Π₀ i, α i) :=
  { (inferInstance : LE (DFinsupp α)) with
    le_refl := fun f i ↦ le_rfl
    le_trans := fun f g h hfg hgh i ↦ (hfg i).trans (hgh i) }

theorem coeFn_mono : Monotone (FunLike.coe : (Π₀ i, α i) → ∀ i, α i) := fun _ _ ↦ le_def.1
#align dfinsupp.coe_fn_mono DFinsupp.coeFn_mono

end Preorder

instance [∀ i, PartialOrder (α i)] : PartialOrder (Π₀ i, α i) :=
  { (inferInstance : Preorder (DFinsupp α)) with
    le_antisymm := fun _ _ hfg hgf ↦ ext fun i ↦ (hfg i).antisymm (hgf i) }

instance [∀ i, SemilatticeInf (α i)] : SemilatticeInf (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    inf := zipWith (fun _ ↦ (· ⊓ ·)) fun _ ↦ inf_idem
    inf_le_left := fun _ _ _ ↦ inf_le_left
    inf_le_right := fun _ _ _ ↦ inf_le_right
    le_inf := fun _ _ _ hf hg i ↦ le_inf (hf i) (hg i) }

@[simp]
theorem inf_apply [∀ i, SemilatticeInf (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.inf_apply DFinsupp.inf_apply

instance [∀ i, SemilatticeSup (α i)] : SemilatticeSup (Π₀ i, α i) :=
  { (inferInstance : PartialOrder (DFinsupp α)) with
    sup := zipWith (fun _ ↦ (· ⊔ ·)) fun _ ↦ sup_idem
    le_sup_left := fun _ _ _ ↦ le_sup_left
    le_sup_right := fun _ _ _ ↦ le_sup_right
    sup_le := fun _ _ _ hf hg i ↦ sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [∀ i, SemilatticeSup (α i)] (f g : Π₀ i, α i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.sup_apply DFinsupp.sup_apply

section Lattice
variable [∀ i, Lattice (α i)] (f g : Π₀ i, α i)

instance lattice : Lattice (Π₀ i, α i) :=
  { (inferInstance : SemilatticeInf (DFinsupp α)),
    (inferInstance : SemilatticeSup (DFinsupp α)) with }
#align dfinsupp.lattice DFinsupp.lattice

variable [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)]

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective $ compl_injective $ by ext; simp [inf_eq_and_sup_eq_iff]
                                       -- ⊢ x✝ ∈ (↑(support (f ⊓ g) ∪ support (f ⊔ g)))ᶜ ↔ x✝ ∈ (↑(support f ∪ support g …
                                            -- 🎉 no goals
#align dfinsupp.support_inf_union_support_sup DFinsupp.support_inf_union_support_sup

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans $ support_inf_union_support_sup _ _
#align dfinsupp.support_sup_union_support_inf DFinsupp.support_sup_union_support_inf

end Lattice
end Zero

/-! ### Algebraic order structures -/


instance (α : ι → Type*) [∀ i, OrderedAddCommMonoid (α i)] : OrderedAddCommMonoid (Π₀ i, α i) :=
  { (inferInstance : AddCommMonoid (DFinsupp α)),
    (inferInstance : PartialOrder (DFinsupp α)) with
    add_le_add_left := fun _ _ h c i ↦ add_le_add_left (h i) (c i) }

instance (α : ι → Type*) [∀ i, OrderedCancelAddCommMonoid (α i)] :
    OrderedCancelAddCommMonoid (Π₀ i, α i) :=
  { (inferInstance : OrderedAddCommMonoid (DFinsupp α)) with
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
               -- 🎉 no goals

variable {α}

protected theorem bot_eq_zero : (⊥ : Π₀ i, α i) = 0 :=
  rfl
#align dfinsupp.bot_eq_zero DFinsupp.bot_eq_zero

@[simp]
theorem add_eq_zero_iff (f g : Π₀ i, α i) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [FunLike.ext_iff, forall_and]
  -- 🎉 no goals
#align dfinsupp.add_eq_zero_iff DFinsupp.add_eq_zero_iff

section LE

variable [DecidableEq ι] [∀ (i) (x : α i), Decidable (x ≠ 0)] {f g : Π₀ i, α i} {s : Finset ι}

theorem le_iff' (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _ ↦ h s, fun h s ↦
    if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩
#align dfinsupp.le_iff' DFinsupp.le_iff'

theorem le_iff : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' <| Subset.refl _
#align dfinsupp.le_iff DFinsupp.le_iff

variable (α)

instance decidableLE [∀ i, DecidableRel (@LE.le (α i) _)] : DecidableRel (@LE.le (Π₀ i, α i) _) :=
  fun _ _ ↦ decidable_of_iff _ le_iff.symm
#align dfinsupp.decidable_le DFinsupp.decidableLE

variable {α}

@[simp]
theorem single_le_iff {i : ι} {a : α i} : single i a ≤ f ↔ a ≤ f i :=
  (le_iff' support_single_subset).trans <| by simp
                                              -- 🎉 no goals
#align dfinsupp.single_le_iff DFinsupp.single_le_iff

end LE

-- porting note: Split into 2 lines to satisfy the unusedVariables linter.
variable (α)
variable [∀ i, Sub (α i)] [∀ i, OrderedSub (α i)] {f g : Π₀ i, α i} {i : ι} {a b : α i}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (Π₀ i, α i) :=
  ⟨zipWith (fun _ m n ↦ m - n) fun _ ↦ tsub_self 0⟩
#align dfinsupp.tsub DFinsupp.tsub

variable {α}

theorem tsub_apply (f g : Π₀ i, α i) (i : ι) : (f - g) i = f i - g i :=
  zipWith_apply _ _ _ _ _
#align dfinsupp.tsub_apply DFinsupp.tsub_apply

@[simp]
theorem coe_tsub (f g : Π₀ i, α i) : ⇑(f - g) = f - g := by
  ext i
  -- ⊢ ↑(f - g) i = (↑f - ↑g) i
  exact tsub_apply f g i
  -- 🎉 no goals
#align dfinsupp.coe_tsub DFinsupp.coe_tsub

variable (α)

instance : OrderedSub (Π₀ i, α i) :=
  ⟨fun _ _ _ ↦ forall_congr' fun _ ↦ tsub_le_iff_right⟩

instance : CanonicallyOrderedAddMonoid (Π₀ i, α i) :=
  { (inferInstance : OrderBot (DFinsupp α)),
    (inferInstance : OrderedAddCommMonoid (DFinsupp α)) with
    exists_add_of_le := by
      intro f g h
      -- ⊢ ∃ c, g = f + c
      exists g - f
      -- ⊢ g = f + (g - f)
      ext i
      -- ⊢ ↑g i = ↑(f + (g - f)) i
      exact (add_tsub_cancel_of_le <| h i).symm
      -- 🎉 no goals
    le_self_add := fun _ _ _ ↦ le_self_add }

variable {α} [DecidableEq ι]

@[simp]
theorem single_tsub : single i (a - b) = single i a - single i b := by
  ext j
  -- ⊢ ↑(single i (a - b)) j = ↑(single i a - single i b) j
  obtain rfl | h := eq_or_ne i j
  -- ⊢ ↑(single i (a - b)) i = ↑(single i a - single i b) i
  · rw [tsub_apply, single_eq_same, single_eq_same, single_eq_same]
    -- 🎉 no goals
  · rw [tsub_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, tsub_self]
    -- 🎉 no goals
#align dfinsupp.single_tsub DFinsupp.single_tsub

variable [∀ (i) (x : α i), Decidable (x ≠ 0)]

theorem support_tsub : (f - g).support ⊆ f.support := by
  simp (config := { contextual := true }) only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne.def, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]
#align dfinsupp.support_tsub DFinsupp.support_tsub

theorem subset_support_tsub : f.support \ g.support ⊆ (f - g).support := by
  simp (config := { contextual := true }) [subset_iff]
  -- 🎉 no goals
#align dfinsupp.subset_support_tsub DFinsupp.subset_support_tsub

end CanonicallyOrderedAddMonoid

section CanonicallyLinearOrderedAddMonoid

variable [∀ i, CanonicallyLinearOrderedAddMonoid (α i)] [DecidableEq ι] {f g : Π₀ i, α i}

@[simp]
theorem support_inf : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  -- ⊢ a✝ ∈ support (f ⊓ g) ↔ a✝ ∈ support f ∩ support g
  simp only [inf_apply, mem_support_iff, Ne.def, Finset.mem_inter]
  -- ⊢ ¬↑f a✝ ⊓ ↑g a✝ = 0 ↔ ¬↑f a✝ = 0 ∧ ¬↑g a✝ = 0
  simp only [inf_eq_min, ← nonpos_iff_eq_zero, min_le_iff, not_or]
  -- 🎉 no goals
#align dfinsupp.support_inf DFinsupp.support_inf

@[simp]
theorem support_sup : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  -- ⊢ a✝ ∈ support (f ⊔ g) ↔ a✝ ∈ support f ∪ support g
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne.def, ← bot_eq_zero]
  -- ⊢ ¬↑f a✝ ⊔ ↑g a✝ = ⊥ ↔ ¬↑f a✝ = ⊥ ∨ ¬↑g a✝ = ⊥
  rw [_root_.sup_eq_bot_iff, not_and_or]
  -- 🎉 no goals
#align dfinsupp.support_sup DFinsupp.support_sup

nonrec theorem disjoint_iff : Disjoint f g ↔ Disjoint f.support g.support := by
  rw [disjoint_iff, disjoint_iff, DFinsupp.bot_eq_zero, ← DFinsupp.support_eq_empty,
    DFinsupp.support_inf]
  rfl
  -- 🎉 no goals
#align dfinsupp.disjoint_iff DFinsupp.disjoint_iff

end CanonicallyLinearOrderedAddMonoid

end DFinsupp
