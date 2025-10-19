/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Eric Wieser, Mario Carneiro, Thomas Zhu
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Init

/-!

# polyrith Tactic

The `polyrith` tactic relied on an external Sage server which has been shut down.
Hence this is no longer supported in Mathlib,
but could be restored if someone wanted to provide an alternative backend
(based on Sage or otherwise).

In the meantime, the `grobner` tactic (which calls into the Grobner basis module of `grind`)
can close goals requiring polynomial reasoning,
but is not able to give a "Try this:" suggestion based on `linear_combination`.
-/

namespace Mathlib.Tactic.Polyrith

/--
The `polyrith` tactic is no longer supported in Mathlib,
because it relied on a defunct external service.

---

Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Notes:
* This tactic only works with a working internet connection, since it calls Sage
  using the SageCell web API at <https://sagecell.sagemath.org/>.
  Many thanks to the Sage team and organization for allowing this use.
* This tactic assumes that the user has `curl` available on path.
-/
syntax "polyrith" (&" only")? (" [" term,* "]")? : tactic

open Tactic
elab_rules : tactic
  | `(tactic| polyrith $[only]? $[[$hyps,*]]?) => do
    throwError "`polyrith` is no longer available, \
      as the external service it relied on has been shut down."

end Mathlib.Tactic.Polyrith
