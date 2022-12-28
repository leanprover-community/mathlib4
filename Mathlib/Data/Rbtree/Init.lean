/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.init
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Alignment file for porting RBTrees

## Summary

In mathlib4, `Std.Data.RBMap` is intended to completely replace the `rbtree` directory,
hence the porting process for this folder removes all content (excpet for #aligns) from its
files and #aligns with the corresponding `Std.Data` entries.
See also the discussion at
leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/porting.20.60Data.2ERBTree.2EInit.60
-/

#align rbnode Std.RBNode
#align rbnode.color Std.RBColor
/- porting note: In contrast to `rbnode.depth`, `Std.RBNode.depth` does not allow for dependence
on a function `f : ℕ → ℕ → ℕ` to generalize `max`. This may cause issues down the line. -/
#align rbnode.depth Std.RBNode.depth
#align rbnode.min Std.RBNode.min
#align rbnode.max Std.RBNode.max
#align rbnode.fold Std.RBNode.foldl
#align rbnode.rev_fold Std.RBNode.foldr
#align rbnode.balance1_node Std.RBNode.balance1
#align rbnode.balance2_node Std.RBNode.balance2
#align rbnode.get_color Std.RBNode.isRed
#align rbnode.ins Std.RBNode.ins
#align rbnode.insert Std.RBNode.insert
#align rbnode.mem Std.RBNode.MemP
#align rbnode.mem_exact Std.RBNode.EMem
#align rbnode.find Std.RBNode.find?
#align rbnode.well_formed Std.RBNode.WF

#align rbtree Std.RBSet
#align mk_rbtree Std.mkRBSet
#align rbtree.mem Std.RBSet.MemP
#align rbtree.mem_exact Std.RBSet.EMem
#align rbtree.fold Std.RBSet.foldl
#align rbtree.rev_fold Std.RBSet.foldr
#align rbtree.empty Std.RBSet.isEmpty
#align rbtree.to_list Std.RBSet.toList
#align rbtree.min Std.RBSet.min
#align rbtree.max Std.RBSet.max
#align rbtree.insert Std.RBSet.insert
#align rbtree.find Std.RBSet.find?
#align rbtree.contains Std.RBSet.contains
#align rbtree.from_list Std.RBSet.ofList
-- porting note: rbtree_of seems to be a duplicate of rbtree.from_list?
#align rbtree_of Std.RBSet.ofList
