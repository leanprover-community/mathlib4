/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Topology.Algebra.Support

/-!
# The topological support of sup and inf of functions

In a topological space `X` and a space `M` with `Sup` structure, for `f g : X → M` with compact
support, we show that `f ⊔ g` has compact support. Similarly, in `β` with `Inf` structure, `f ⊓ g`
has compact support if so do `f` and `g`.

-/

variable {X M : Type*} [TopologicalSpace X] [One M]

section SemilatticeSup

variable [SemilatticeSup M]

@[to_additive]
theorem HasCompactMulSupport.sup {f g : X → M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) :  HasCompactMulSupport (f ⊔ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport, mulTSupport, mulTSupport, ← closure_union]
  apply closure_mono
  exact Function.mulSupport_sup f g

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf M]

@[to_additive]
theorem HasCompactMulSupport.inf {f g : X → M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) :  HasCompactMulSupport (f ⊓ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport, mulTSupport, mulTSupport, ← closure_union]
  apply closure_mono
  exact Function.mulSupport_inf f g

end SemilatticeInf
