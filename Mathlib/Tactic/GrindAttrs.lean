/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand
public import Mathlib.Init

/-!
# Custom grind-sets

In this file we declare custom grind attributes and tactics that call grind using only these grind
attributes. These grind sets are helpful because they can contain a lot of specialized ways to
prove a particular problem.

Currently, this implements the `compactness` and `closedness` grind attribute and tactic.

## Usage Notes

These tactics can be useful for various purposes:
* directly as a tactic: `by compactness`
* as auto-params for lemmas: `(h : IsCompact K := by compactness)`
* as discharger for other tactics, e.g. `fun_prop (disch := compactness)`
* You can also use the grind sets directly: `grind only [compactness, closedness]`.
  This is especially useful if you want to combine multiple grind sets.

## Implementation Notes

We define these grind sets so that we can aggressively tag lemmas in one particular topic as
grind lemmas for a particular grind set. For the default grind set we should be a lot
more careful with tagging lemmas, to avoid slowing down `grind`, but since these specialized grind
attributes don't have any tagged lemmas outside its specialized domain, it should still be
performant.

These tactics will not use the full power of grind, and could disable some of the grind engines if
these would slow down these tactics. We could have alternatively used a tactic similar to
`apply_rules` here, but we think that the efficient implementation of `grind` is helpful even for
these simpler tactics. For example, we can safely tag both the following lemmas, and `grind` will
add both pairs of hypotheses to the whiteboard without having to backtrack.
```
IsCompact.inter_left : IsClosed s → IsCompact t → IsCompact (s ∩ t)
IsCompact.inter_right : IsCompact s → IsClosed t → IsCompact (s ∩ t)
```

We will tag transition theorems, e.g. `Set.Finite.isCompact : Finite s → IsCompact s` should be
tagged `@[compactness .]`, even if `compactness` will contain lemmas about finite sets.
The advantages of this are that we can use local finiteness hypotheses, and this will ensure that
the different grind sets will interact well with each other. For the same reason we tag lemmas
that involve other properties, e.g. `IsCompact.inter_left`

## To do

* Implement other grind sets, e.g. `openness`, `boundedness`, `countability`, `connectedness`, ...

-/

open Lean Parser Tactic

/-- A hash set of the grind attributes in Mathlib.

When adding a new grind attribute, manually add it to this hash set as well. -/
def Mathlib.grindAttrs : Std.HashSet Name :=
 {`compactness, `closedness}

/-- The `compactness` attribute is a custom grind-set specialized to prove that sets are compact.
It is called by the `compactness` tactic. -/
register_grind_attr compactness

/--
`compactness` is a simple tactic that tries various lemmas to prove that a set is compact.
It is implemented using `grind`, and has the same configuration options as `grind`.

Use `grind only [compactness, closedness]` instead if you want to prove that the closure of sets are
compact.

It also exists as a grind attribute, and can be combined with other grind attributes using
`grind only [compactness, ...]`.
-/
macro (name := compactnessTac) "compactness" config:optConfig : tactic =>
  -- note: directly giving `compactness` as argument in the syntax quotation below is treated
  -- as an unknown identifier by the hygiene system.
  `(tactic|grind $config only [$(mkIdent `compactness):term])

@[inherit_doc compactnessTac]
macro "compactness?" config:optConfig : tactic =>
    `(tactic|grind? $config only [$(mkIdent `compactness):term])

/-- The `closedness` attribute is a custom grind-set specialized to prove that sets are closed.
It is called by the `closedness` tactic. -/
register_grind_attr closedness

/--
`closedness` is a simple tactic that tries various lemmas to prove that a set is closed,
and reasoning about the closure of sets.
It is implemented using `grind`, and has the same configuration options as `grind`.

It also exists as a grind attribute, and can be combined with other grind attributes using
`grind only [closedness, ...]`.
-/
macro (name := closednessTac) "closedness" config:optConfig : tactic =>
  -- note: directly giving `closedness` as argument in the syntax quotation below is treated
  -- as an unknown identifier by the hygiene system.
  `(tactic|grind $config only [$(mkIdent `closedness):term])

@[inherit_doc closednessTac]
macro "closedness?" config:optConfig : tactic =>
    `(tactic|grind? $config only [$(mkIdent `closedness):term])
