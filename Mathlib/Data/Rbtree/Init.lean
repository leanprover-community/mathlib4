/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.init
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Algebra.Classes
/-!
# Alignment file for porting Rbtree.Init

## Summary

In mathlib4, `Std.Data.RBMap` is intended to completely replace the `rbtree` directory,
hence the porting process for this folder removes all content (excpet for #aligns) from its
files and #aligns with the corresponding `Std.Data` entries.
See also the discussion at
leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/porting.20.60Data.2ERBTree.2EInit.60
-/

-- porting note: `rbnode.color.decidable_eq` has no replacement in std4
#align rbnode Std.RBNodeₓ
#align rbnode.color Std.RBColor
/- porting note: In contrast to `rbnode.depth`, `Std.RBNode.depth` does not allow for dependence
on a function `f : ℕ → ℕ → ℕ` to generalize `max`. This may cause issues down the line. -/
#noalign rbnode.depth
#align rbnode.min Std.RBNode.minₓ
#align rbnode.max Std.RBNode.maxₓ
#align rbnode.fold Std.RBNode.foldlₓ
#align rbnode.rev_fold Std.RBNode.foldrₓ
#noalign rbnode.balance1
#align rbnode.balance1_node Std.RBNode.balance1ₓ
#noalign rbnode.balance2
#align rbnode.balance2_node Std.RBNode.balance2ₓ
#align rbnode.get_color Std.RBNode.isRedₓ
#align rbnode.ins Std.RBNode.insₓ
#noalign rbnode.mk_insert_result
#align rbnode.insert Std.RBNode.insertₓ
#align rbnode.mem Std.RBNode.MemPₓ
#align rbnode.mem_exact Std.RBNode.EMemₓ
#align rbnode.find Std.RBNode.find?ₓ
#align rbnode.well_formed Std.RBNode.WFₓ
#align rbtree Std.RBSetₓ
#align mk_rbtree Std.mkRBSetₓ
#align rbtree.mem Std.RBSet.MemPₓ
#align rbtree.mem_exact Std.RBSet.EMemₓ
#align rbtree.fold Std.RBSet.foldlₓ
#align rbtree.rev_fold Std.RBSet.foldrₓ
#align rbtree.empty Std.RBSet.isEmptyₓ
#align rbtree.to_list Std.RBSet.toListₓ
#align rbtree.min Std.RBSet.minₓ
#align rbtree.max Std.RBSet.maxₓ
#align rbtree.insert Std.RBSet.insertₓ
#align rbtree.find Std.RBSet.find?ₓ
#align rbtree.contains Std.RBSet.containsₓ
#align rbtree.from_list Std.RBSet.ofListₓ
-- porting note: rbtree_of seems to be a duplicate of rbtree.from_list?
#align rbtree_of Std.RBSet.ofListₓ
