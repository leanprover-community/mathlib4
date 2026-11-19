/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

import Mathlib.Tactic.Translate.ToAdditive

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Notations for operations involving order and algebraic structure

## Notation

* `a⁺ᵐ = a ⊔ 1`: _Positive component_ of an element `a` of a multiplicative lattice ordered group
* `a⁻ᵐ = a⁻¹ ⊔ 1`: _Negative component_ of an element `a` of a multiplicative lattice ordered group
* `a⁺ = a ⊔ 0`: _Positive component_ of an element `a` of a lattice ordered group
* `a⁻ = (-a) ⊔ 0`: _Negative component_ of an element `a` of a lattice ordered group
-/

public section

/--
A notation class for the _positive part_ function: `a⁺`.
-/
class PosPart (α : Type*) where
  /--
  The _positive part_ of an element `a`.
  -/
  posPart : α → α

/--
A notation class for the _positive part_ function (multiplicative version): `a⁺ᵐ`.
-/
@[to_additive]
class OneLePart (α : Type*) where
  /--
  The _positive part_ of an element `a`.
  -/
  oneLePart : α → α

/--
A notation class for the _negative part_ function: `a⁻`.
-/
class NegPart (α : Type*) where
  /--
  The _negative part_ of an element `a`.
  -/
  negPart : α → α

/--
A notation class for the _negative part_ function (multiplicative version): `a⁻ᵐ`.
-/
@[to_additive]
class LeOnePart (α : Type*) where
  /--
  The _negative part_ of an element `a`.
  -/
  leOnePart : α → α

export OneLePart (oneLePart)
export LeOnePart (leOnePart)
export PosPart (posPart)
export NegPart (negPart)

@[inherit_doc] postfix:max "⁺ᵐ" => OneLePart.oneLePart
@[inherit_doc] postfix:max "⁻ᵐ" => LeOnePart.leOnePart
@[inherit_doc] postfix:max "⁺" => PosPart.posPart
@[inherit_doc] postfix:max "⁻" => NegPart.negPart
