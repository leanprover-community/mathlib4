/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Tactic.FBinop

/-!
# Set Product Notation
This file provides notation for a product of sets, and other similar types.

## Main Definitions

* `SProd α β γ` for a binary operation `(· ×ˢ ·) : α → β → γ`.

## Notation

We introduce the notation `x ×ˢ y` for the `sprod` of any `SProd` structure. Ideally, `x × y`
notation is desirable but this notation is defined in core for `Prod` so replacing `x ×ˢ y` with
`x × y` seems difficult.
-/

universe u v w

/-- Notation type class for the set product `×ˢ`. -/
class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The Cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α → β → γ

-- This notation binds more strongly than (pre)images, unions and intersections.
@[inherit_doc SProd.sprod] infixr:82 " ×ˢ " => SProd.sprod
macro_rules | `($x ×ˢ $y)   => `(fbinop% SProd.sprod $x $y)
