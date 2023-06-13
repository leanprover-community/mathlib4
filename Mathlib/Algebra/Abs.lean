/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.abs
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Mathport.Rename
/-!
# Absolute value

This file defines a notational class `Abs` which adds the unary operator `abs` and the notation
`|.|`. The concept of an absolute value occurs in lattice ordered groups and in GL and GM spaces.

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure). This file also defines `PosPart` and `NegPart` classes
which add unary operators `pos` and `neg`, representing the maps taking an element to its positive
and negative part respectively along with the notation `⁺` and `⁻`.

## Notations

The following notation is introduced:

* `|.|` for the absolute value;
* `.⁺` for the positive part;
* `.⁻` for the negative part.

## Tags

absolute
-/


/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class Abs (α : Type _) where
  /-- The absolute value function. -/
  abs : α → α

#align has_abs Abs

export Abs (abs)

/-- The positive part of an element admitting a decomposition into positive and negative parts.
-/
class PosPart (α : Type _) where
  /-- The positive part function. -/
  pos : α → α

#align has_pos_part PosPart

/-- The negative part of an element admitting a decomposition into positive and negative parts.
-/
class NegPart (α : Type _) where
  /-- The negative part function. -/
  neg : α → α

#align has_neg_part NegPart

@[inherit_doc Abs.abs]
macro atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

@[inherit_doc]
postfix:1000 "⁺" => PosPart.pos

@[inherit_doc]
postfix:1000 "⁻" => NegPart.neg
