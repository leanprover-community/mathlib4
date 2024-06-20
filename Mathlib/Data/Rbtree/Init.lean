/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Align
import Batteries.Data.RBMap.Depth

#align_import data.rbtree.init from "leanprover-community/mathlib"@"fcc158e986d4896605e97fb3ad17d5cfed49a242"

/-!

# Align statements for RBTree

Porting note: essentially already ported to std4

https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Mathlib4.20porting.20meeting.20series/near/369848971

-/

#align rbnode Batteries.RBNode
#align rbnode.color Batteries.RBColor
#noalign rbnode.color.decidable_eq
#align rbnode.depth Batteries.RBNode.depth
#align rbnode.min Batteries.RBNode.min
#align rbnode.max Batteries.RBNode.max
#align rbnode.fold Batteries.RBNode.fold

#noalign rbnode.rev_fold

#align rbnode.balance1 Batteries.RBNode.balance1

#noalign rbnode.balance1_node

#align rbnode.balance2 Batteries.RBNode.balance2

#noalign rbnode.balance2_node

#noalign rbnode.get_color

#align rbnode.ins Batteries.RBNode.ins

#noalign rbnode.mk_insert_result

#align rbnode.insert Batteries.RBNode.insert
#align rbnode.mem Batteries.RBNode.Mem

#noalign rbnode.mem_exact

#align rbnode.find Batteries.RBNode.find?
#align rbnode.well_formed Batteries.RBNode.WF

#align rbtree Batteries.RBSet
#align mk_rbtree Batteries.mkRBSet
#align rbtree.mem Batteries.RBSet.Mem

#noalign rbtree.mem_exact
#noalign rbtree.depth

#align rbtree.fold Batteries.RBSet.foldl

#noalign rbtree.rev_fold

#align rbtree.empty Batteries.RBSet.empty
#align rbtree.to_list Batteries.RBSet.toList
#align rbtree.min Batteries.RBSet.min
#align rbtree.max Batteries.RBSet.max
#align rbtree.insert Batteries.RBSet.insert
#align rbtree.find Batteries.RBSet.find?
#align rbtree.contains Batteries.RBSet.contains
#align rbtree.from_list Batteries.RBSet.ofList

#noalign rbtree_of
