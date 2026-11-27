/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.EMetricSpace.Defs

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Extended metric spaces on multiplicative opposites

This file proves that if `α` is some (weak) pseudo extended metric space, so is `αᵐᵒᵖ`.
We do this in this file instead of `Mathlib/Topology/EMetricSpace/Defs.lean` to avoid imports.
-/

public section

open Filter Set Topology Set.Notation

namespace MulOpposite

variable {α : Type*} [TopologicalSpace α] [WeakPseudoEMetricSpace α]

/-- weak pseudoemetric space instance on the multiplicative opposite of a
weak pseudoemetric space. -/
@[to_additive
/-- Weak pseudoemetric space instance on the additive opposite of a weak pseudoemetric space. -/]
instance {α : Type*} [TopologicalSpace α] [WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace αᵐᵒᵖ :=
  WeakPseudoEMetricSpace.IsInducing (f := unop) MulOpposite.opHomeomorph.symm.isInducing ‹_›

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive
/-- Pseudoemetric space instance on the additive opposite of a pseudoemetric space. -/]
instance {α : Type*} [PseudoEMetricSpace α] : PseudoEMetricSpace αᵐᵒᵖ :=
  PseudoEMetricSpace.induced unop ‹_›

@[to_additive]
theorem eDist_unop (x y : αᵐᵒᵖ) : eDist (unop x) (unop y) = eDist x y := rfl

@[deprecated (since := "2026-11-27")] alias edist_unop := eDist_unop

@[to_additive]
theorem eDist_op (x y : α) : eDist (op x) (op y) = eDist x y := rfl

@[deprecated (since := "2026-11-27")] alias edist_op := eDist_op

end MulOpposite
