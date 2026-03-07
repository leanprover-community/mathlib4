/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.Tactic.Translate.ToSubgroupOf

/-!
## `@[to_subgroupOf]`

The `@[to_subgroupOf]` attribute generates a sibling theorem whose ambient group is restricted to
an ambient subgroup `K : Subgroup G`, replacing subgroup binders `H : Subgroup G` by
`H.subgroupOf K`.
-/
