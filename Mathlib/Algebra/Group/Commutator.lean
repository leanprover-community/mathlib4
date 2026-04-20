/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Bracket

/-!
# The bracket on a group given by commutator.

## Notation

After `open scoped commutatorElement`, `⁅g₁, g₂⁆` is syntax for `g₁ * g₂ * g₁⁻¹ * g₂⁻¹`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

/-- The commutator of two elements `g₁` and `g₂`. This is a scoped instance in the
`commutatorElement` namespace to avoid clashing with other brackets. -/
@[to_additive (attr := reducible) /-- The additive commutator of two elements `g₁` and `g₂`. This
is a scoped instance in the `commutatorElement` namespace to avoid clashing with other brackets -/]
def commutatorElement {G : Type*} [Group G] : Bracket G G :=
  ⟨fun g₁ g₂ ↦ g₁ * g₂ * g₁⁻¹ * g₂⁻¹⟩

namespace commutatorElement

attribute [scoped instance] commutatorElement addCommutatorElement

end commutatorElement

open scoped commutatorElement

@[to_additive]
theorem commutatorElement_def {G : Type*} [Group G] (g₁ g₂ : G) :
    ⁅g₁, g₂⁆ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ :=
  rfl
