/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Massot
-/
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# `group_exp` tactic

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group theory
-/

namespace Mathlib.Tactic.Group
open Lean Meta Parser.Tactic Elab.Tactic

/-- Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]     -- the goal is now `a*d*d⁻¹ = a`
  group      -- which then normalized and closed
```
-/
syntax (name := group_exp) "group_exp" (location)? : tactic

macro_rules
| `(tactic| group $[$loc]?) =>
  `(tactic| repeat (fail_if_no_progress (group $[$loc]? <;> ring_nf $[$loc]?)))

end Mathlib.Tactic.Group
