/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
import Mathlib.Data.Finsupp.Defs

#align_import data.finsupp.order from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `α` to `ι →₀ α`.

## Main declarations

* `Finsupp.orderEmbeddingToFun`: The order embedding from finitely supported functions to
  functions.
-/

-- porting notes: removed from module documentation because it moved to `data.finsupp.multiset`
-- TODO: move to `Data.Finsupp.Multiset` when that is ported
-- * `Finsupp.orderIsoMultiset`: The order isomorphism between `ℕ`-valued finitely supported
--   functions and multisets.


noncomputable section

open BigOperators

open Finset

variable {ι α : Type*}

namespace Finsupp

/-! ### Order structures -/


section Zero

variable [Zero α]

section LE

variable [LE α]

instance instLEFinsupp : LE (ι →₀ α) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

theorem le_def {f g : ι →₀ α} : f ≤ g ↔ ∀ i, f i ≤ g i :=
  Iff.rfl
#align finsupp.le_def Finsupp.le_def

/-- The order on `Finsupp`s over a partial order embeds into the order on functions -/
def orderEmbeddingToFun : (ι →₀ α) ↪o (ι → α) where
  toFun f := f
  inj' f g h :=
    Finsupp.ext fun i => by
      dsimp at h
      -- ⊢ ↑f i = ↑g i
      rw [h]
      -- 🎉 no goals
  map_rel_iff' {a b} := (@le_def _ _ _ _ a b).symm
#align finsupp.order_embedding_to_fun Finsupp.orderEmbeddingToFun

@[simp]
theorem orderEmbeddingToFun_apply {f : ι →₀ α} {i : ι} : orderEmbeddingToFun f i = f i :=
  rfl
#align finsupp.order_embedding_to_fun_apply Finsupp.orderEmbeddingToFun_apply

end LE

section Preorder

variable [Preorder α]

instance preorder : Preorder (ι →₀ α) :=
  { Finsupp.instLEFinsupp with
    le_refl := fun f i => le_rfl
    le_trans := fun f g h hfg hgh i => (hfg i).trans (hgh i) }

theorem monotone_toFun : Monotone (Finsupp.toFun : (ι →₀ α) → ι → α) :=
    fun _f _g h a => le_def.1 h a
#align finsupp.monotone_to_fun Finsupp.monotone_toFun

end Preorder

instance partialorder [PartialOrder α] : PartialOrder (ι →₀ α) :=
  { Finsupp.preorder with le_antisymm :=
      fun _f _g hfg hgf => ext fun i => (hfg i).antisymm (hgf i) }

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (ι →₀ α) :=
  { Finsupp.partialorder with
    inf := zipWith (· ⊓ ·) inf_idem
    inf_le_left := fun _f _g _i => inf_le_left
    inf_le_right := fun _f _g _i => inf_le_right
    le_inf := fun _f _g _i h1 h2 s => le_inf (h1 s) (h2 s) }

@[simp]
theorem inf_apply [SemilatticeInf α] {i : ι} {f g : ι →₀ α} : (f ⊓ g) i = f i ⊓ g i :=
  rfl
#align finsupp.inf_apply Finsupp.inf_apply

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (ι →₀ α) :=
  { Finsupp.partialorder with
    sup := zipWith (· ⊔ ·) sup_idem
    le_sup_left := fun _f _g _i => le_sup_left
    le_sup_right := fun _f _g _i => le_sup_right
    sup_le := fun _f _g _h hf hg i => sup_le (hf i) (hg i) }

@[simp]
theorem sup_apply [SemilatticeSup α] {i : ι} {f g : ι →₀ α} : (f ⊔ g) i = f i ⊔ g i :=
  rfl
#align finsupp.sup_apply Finsupp.sup_apply

instance lattice [Lattice α] : Lattice (ι →₀ α) :=
  { Finsupp.semilatticeInf, Finsupp.semilatticeSup with }
#align finsupp.lattice Finsupp.lattice

section Lattice
variable [DecidableEq ι] [Lattice α] (f g : ι →₀ α)

theorem support_inf_union_support_sup : (f ⊓ g).support ∪ (f ⊔ g).support = f.support ∪ g.support :=
  coe_injective <| compl_injective <| by ext; simp [inf_eq_and_sup_eq_iff]
                                         -- ⊢ x✝ ∈ (↑((f ⊓ g).support ∪ (f ⊔ g).support))ᶜ ↔ x✝ ∈ (↑(f.support ∪ g.support …
                                              -- 🎉 no goals
#align finsupp.support_inf_union_support_sup Finsupp.support_inf_union_support_sup

theorem support_sup_union_support_inf : (f ⊔ g).support ∪ (f ⊓ g).support = f.support ∪ g.support :=
  (union_comm _ _).trans <| support_inf_union_support_sup _ _
#align finsupp.support_sup_union_support_inf Finsupp.support_sup_union_support_inf

end Lattice
end Zero

/-! ### Algebraic order structures -/


instance orderedAddCommMonoid [OrderedAddCommMonoid α] : OrderedAddCommMonoid (ι →₀ α) :=
  { Finsupp.addCommMonoid, Finsupp.partialorder with
    add_le_add_left := fun _a _b h c s => add_le_add_left (h s) (c s) }

instance orderedCancelAddCommMonoid [OrderedCancelAddCommMonoid α] :
    OrderedCancelAddCommMonoid (ι →₀ α) :=
  { Finsupp.orderedAddCommMonoid with
    le_of_add_le_add_left := fun _f _g _i h s => le_of_add_le_add_left (h s) }

instance contravariantClass [OrderedAddCommMonoid α] [ContravariantClass α α (· + ·) (· ≤ ·)] :
    ContravariantClass (ι →₀ α) (ι →₀ α) (· + ·) (· ≤ ·) :=
  ⟨fun _f _g _h H x => le_of_add_le_add_left <| H x⟩

section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddMonoid α]

instance orderBot : OrderBot (ι →₀ α) where
  bot := 0
  bot_le := by simp only [le_def, coe_zero, Pi.zero_apply, imp_true_iff, zero_le]
               -- 🎉 no goals

protected theorem bot_eq_zero : (⊥ : ι →₀ α) = 0 :=
  rfl
#align finsupp.bot_eq_zero Finsupp.bot_eq_zero

@[simp]
theorem add_eq_zero_iff (f g : ι →₀ α) : f + g = 0 ↔ f = 0 ∧ g = 0 := by
  simp [FunLike.ext_iff, forall_and]
  -- 🎉 no goals
#align finsupp.add_eq_zero_iff Finsupp.add_eq_zero_iff

theorem le_iff' (f g : ι →₀ α) {s : Finset ι} (hf : f.support ⊆ s) : f ≤ g ↔ ∀ i ∈ s, f i ≤ g i :=
  ⟨fun h s _hs => h s, fun h s => by
    classical exact
        if H : s ∈ f.support then h s (hf H) else (not_mem_support_iff.1 H).symm ▸ zero_le (g s)⟩
#align finsupp.le_iff' Finsupp.le_iff'

theorem le_iff (f g : ι →₀ α) : f ≤ g ↔ ∀ i ∈ f.support, f i ≤ g i :=
  le_iff' f g <| Subset.refl _
#align finsupp.le_iff Finsupp.le_iff

instance decidableLE [DecidableRel (@LE.le α _)] : DecidableRel (@LE.le (ι →₀ α) _) := fun f g =>
  decidable_of_iff _ (le_iff f g).symm
#align finsupp.decidable_le Finsupp.decidableLE

@[simp]
theorem single_le_iff {i : ι} {x : α} {f : ι →₀ α} : single i x ≤ f ↔ x ≤ f i :=
  (le_iff' _ _ support_single_subset).trans <| by simp
                                                  -- 🎉 no goals
#align finsupp.single_le_iff Finsupp.single_le_iff

variable [Sub α] [OrderedSub α] {f g : ι →₀ α} {i : ι} {a b : α}

/-- This is called `tsub` for truncated subtraction, to distinguish it with subtraction in an
additive group. -/
instance tsub : Sub (ι →₀ α) :=
  ⟨zipWith (fun m n => m - n) (tsub_self 0)⟩
#align finsupp.tsub Finsupp.tsub

instance orderedSub : OrderedSub (ι →₀ α) :=
  ⟨fun _n _m _k => forall_congr' fun _x => tsub_le_iff_right⟩

instance : CanonicallyOrderedAddMonoid (ι →₀ α) :=
  { Finsupp.orderBot,
    Finsupp.orderedAddCommMonoid with
    exists_add_of_le := fun {f g} h => ⟨g - f, ext fun x => (add_tsub_cancel_of_le <| h x).symm⟩
    le_self_add := fun _f _g _x => le_self_add }

@[simp]
theorem coe_tsub (f g : ι →₀ α) : ⇑(f - g) = f - g :=
  rfl
#align finsupp.coe_tsub Finsupp.coe_tsub

theorem tsub_apply (f g : ι →₀ α) (a : ι) : (f - g) a = f a - g a :=
  rfl
#align finsupp.tsub_apply Finsupp.tsub_apply

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
#align finsupp.single_tsub Finsupp.single_tsub

theorem support_tsub {f1 f2 : ι →₀ α} : (f1 - f2).support ⊆ f1.support := by
  simp (config := { contextual := true }) only [subset_iff, tsub_eq_zero_iff_le, mem_support_iff,
    Ne.def, coe_tsub, Pi.sub_apply, not_imp_not, zero_le, imp_true_iff]
#align finsupp.support_tsub Finsupp.support_tsub

theorem subset_support_tsub [DecidableEq ι] {f1 f2 : ι →₀ α} :
    f1.support \ f2.support ⊆ (f1 - f2).support := by
  simp (config := { contextual := true }) [subset_iff]
  -- 🎉 no goals
#align finsupp.subset_support_tsub Finsupp.subset_support_tsub

end CanonicallyOrderedAddMonoid

section CanonicallyLinearOrderedAddMonoid

variable [CanonicallyLinearOrderedAddMonoid α]

@[simp]
theorem support_inf [DecidableEq ι] (f g : ι →₀ α) : (f ⊓ g).support = f.support ∩ g.support := by
  ext
  -- ⊢ a✝ ∈ (f ⊓ g).support ↔ a✝ ∈ f.support ∩ g.support
  simp only [inf_apply, mem_support_iff, Ne.def, Finset.mem_union, Finset.mem_filter,
    Finset.mem_inter]
  simp only [inf_eq_min, ← nonpos_iff_eq_zero, min_le_iff, not_or]
  -- 🎉 no goals
#align finsupp.support_inf Finsupp.support_inf

@[simp]
theorem support_sup [DecidableEq ι] (f g : ι →₀ α) : (f ⊔ g).support = f.support ∪ g.support := by
  ext
  -- ⊢ a✝ ∈ (f ⊔ g).support ↔ a✝ ∈ f.support ∪ g.support
  simp only [Finset.mem_union, mem_support_iff, sup_apply, Ne.def, ← bot_eq_zero]
  -- ⊢ ¬↑f a✝ ⊔ ↑g a✝ = ⊥ ↔ ¬↑f a✝ = ⊥ ∨ ¬↑g a✝ = ⊥
  rw [_root_.sup_eq_bot_iff, not_and_or]
  -- 🎉 no goals
#align finsupp.support_sup Finsupp.support_sup

nonrec theorem disjoint_iff {f g : ι →₀ α} : Disjoint f g ↔ Disjoint f.support g.support := by
  classical
    rw [disjoint_iff, disjoint_iff, Finsupp.bot_eq_zero, ← Finsupp.support_eq_empty,
      Finsupp.support_inf]
    rfl
#align finsupp.disjoint_iff Finsupp.disjoint_iff

end CanonicallyLinearOrderedAddMonoid

/-! ### Some lemmas about `ℕ` -/


section Nat

theorem sub_single_one_add {a : ι} {u u' : ι →₀ ℕ} (h : u a ≠ 0) :
    u - single a 1 + u' = u + u' - single a 1 :=
  tsub_add_eq_add_tsub <| single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h
#align finsupp.sub_single_one_add Finsupp.sub_single_one_add

theorem add_sub_single_one {a : ι} {u u' : ι →₀ ℕ} (h : u' a ≠ 0) :
    u + (u' - single a 1) = u + u' - single a 1 :=
  (add_tsub_assoc_of_le (single_le_iff.mpr <| Nat.one_le_iff_ne_zero.mpr h) _).symm
#align finsupp.add_sub_single_one Finsupp.add_sub_single_one

end Nat

end Finsupp
