/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Module.FunLikeSMul

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Group actions on embeddings

This file provides a `MulAction G (α ↪ β)` instance that agrees with the `MulAction G (α → β)`
instances defined by `Pi.mulAction`.

Note that unlike the `Pi` instance, this requires `G` to be a group.
-/

public section

assert_not_exists MonoidWithZero

universe u v w

variable {G G' α β : Type*}

namespace Function.Embedding

@[to_additive]
instance smul [Group G] [MulAction G β] : SMul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]
instance [Group G] [MulAction G β] : IsSMulApply G (α ↪ β) where

@[to_additive]
theorem smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) :
    g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl

@[deprecated vadd_apply +typeChanged (since := "2026-10-29")]
protected theorem vadd_apply [AddGroup G] [AddAction G β] (g : G) (f : α ↪ β) (a : α) :
    (g +ᵥ f) a = g +ᵥ f a :=
  rfl

@[deprecated smul_apply +typeChanged (since := "2026-10-29")]
protected theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) :
    (g • f) a = g • f a :=
  rfl

@[deprecated FunLike.coe_vadd +typeChanged (since := "2026-10-29")]
theorem coe_vadd [AddGroup G] [AddAction G β] (g : G) (f : α ↪ β) : ⇑(g +ᵥ f) = g +ᵥ ⇑f :=
  rfl

@[deprecated FunLike.coe_smul +typeChanged (since := "2026-10-29")]
theorem coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • ⇑f :=
  rfl

instance [Group G] [Group G'] [SMul G G'] [MulAction G β] [MulAction G' β]
    [IsScalarTower G G' β] : IsScalarTower G G' (α ↪ β) :=
  FunLike.isScalarTower

@[to_additive]
instance [Group G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
    SMulCommClass G G' (α ↪ β) :=
  FunLike.smulCommClass

instance [Group G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
    IsCentralScalar G (α ↪ β) :=
  ⟨fun _ _ => Function.Embedding.ext fun _ => op_smul_eq_smul _ _⟩

@[to_additive]
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end Function.Embedding
