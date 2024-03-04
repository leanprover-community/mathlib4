/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Align
import Std.Data.RBMap.Lemmas

#align_import data.rbtree.init from "leanprover-community/mathlib"@"fcc158e986d4896605e97fb3ad17d5cfed49a242"

/-!

# Align statements for RBTree

Porting note: essentially already ported to std4

https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Mathlib4.20porting.20meeting.20series/near/369848971

-/

#align rbnode Std.RBNode
#align rbnode.color Std.RBColor
#noalign rbnode.color.decidable_eq
#align rbnode.depth Std.RBNode.depth
#align rbnode.min Std.RBNode.min
#align rbnode.max Std.RBNode.max
#align rbnode.fold Std.RBNode.fold

#noalign rbnode.rev_fold

#align rbnode.balance1 Std.RBNode.balance1

#noalign rbnode.balance1_node

#align rbnode.balance2 Std.RBNode.balance2

#noalign rbnode.balance2_node

#noalign rbnode.get_color

#align rbnode.ins Std.RBNode.ins

#noalign rbnode.mk_insert_result

#align rbnode.insert Std.RBNode.insert
#align rbnode.mem Std.RBNode.Mem

#noalign rbnode.mem_exact

#align rbnode.find Std.RBNode.find?
#align rbnode.well_formed Std.RBNode.WF

#align rbtree Std.RBSet
#align mk_rbtree Std.mkRBSet
#align rbtree.mem Std.RBSet.Mem

#noalign rbtree.mem_exact
#noalign rbtree.depth

#align rbtree.fold Std.RBSet.foldl

#noalign rbtree.rev_fold

#align rbtree.empty Std.RBSet.empty
#align rbtree.to_list Std.RBSet.toList
#align rbtree.min Std.RBSet.min
#align rbtree.max Std.RBSet.max
#align rbtree.insert Std.RBSet.insert
#align rbtree.find Std.RBSet.find?
#align rbtree.contains Std.RBSet.contains
#align rbtree.from_list Std.RBSet.ofList

#noalign rbtree_of
