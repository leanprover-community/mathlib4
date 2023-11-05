/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Align
import Std.Data.RBMap.Basic

#align_import data.rbtree.init from "leanprover-community/mathlib"@"fcc158e986d4896605e97fb3ad17d5cfed49a242"

/-!

# Align statements for RBTree

Porting note: essentially already ported to std4

https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Mathlib4.20porting.20meeting.20series/near/369848971

-/

#noalign rbnode.color.decidable_eq

#noalign rbnode.rev_fold


#noalign rbnode.balance1_node


#noalign rbnode.balance2_node

#noalign rbnode.get_color


#noalign rbnode.mk_insert_result


#noalign rbnode.mem_exact



#noalign rbtree.mem_exact
#noalign rbtree.depth


#noalign rbtree.rev_fold


#noalign rbtree_of
