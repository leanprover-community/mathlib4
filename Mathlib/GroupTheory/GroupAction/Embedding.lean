/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.embedding
! leanprover-community/mathlib commit a437a2499163d85d670479f69f625f461cc5fef9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Group actions on embeddings

This file provides a `mul_action G (α ↪ β)` instance that agrees with the `mul_action G (α → β)`
instances defined by `pi.mul_action`.

Note that unlike the `pi` instance, this requires `G` to be a group.
-/


universe u v w

variable {G G' α β : Type _}

namespace Function.Embedding

@[to_additive Function.Embedding.hasVadd]
instance [Group G] [MulAction G β] : HasSmul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]
theorem smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) :
    g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl
#align function.embedding.smul_def Function.Embedding.smul_def

@[simp, to_additive]
theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
  rfl
#align function.embedding.smul_apply Function.Embedding.smul_apply

@[to_additive]
theorem coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • f :=
  rfl
#align function.embedding.coe_smul Function.Embedding.coe_smul

instance [Group G] [Group G'] [HasSmul G G'] [MulAction G β] [MulAction G' β]
    [IsScalarTower G G' β] : IsScalarTower G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]
instance [Group G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
    SMulCommClass G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

instance [Group G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
    IsCentralScalar G (α ↪ β) :=
  ⟨fun r m => Function.Embedding.ext fun i => op_smul_eq_smul _ _⟩

@[to_additive]
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  FunLike.coe_injective.MulAction _ coe_smul

end Function.Embedding

