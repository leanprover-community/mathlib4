/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Tactic.Push

/-! # Contrapose

The `contrapose` tactic transforms the goal into its contrapositive when that goal is an
implication.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

-/
namespace Mathlib.Tactic.Contrapose

lemma mtr {p q : Prop} : (¬ q → ¬ p) → (p → q) := fun h hp ↦ by_contra (fun h' ↦ h h' hp)

/--
Transforms the goal into its contrapositive.
* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
-/
syntax (name := contrapose) "contrapose" (ppSpace colGt ident (" with " ident)?)? : tactic
macro_rules
  | `(tactic| contrapose) => `(tactic| (refine mtr ?_))
  | `(tactic| contrapose $e) => `(tactic| (revert $e:ident; contrapose; intro $e:ident))
  | `(tactic| contrapose $e with $e') => `(tactic| (revert $e:ident; contrapose; intro $e':ident))

/--
Transforms the goal into its contrapositive and uses pushes negations inside `P` and `Q`.
Usage matches `contrapose`
-/
syntax (name := contrapose!) "contrapose!" (ppSpace colGt ident (" with " ident)?)? : tactic
macro_rules
  | `(tactic| contrapose!) => `(tactic| (contrapose; try push_neg))
  | `(tactic| contrapose! $e) => `(tactic| (revert $e:ident; contrapose!; intro $e:ident))
  | `(tactic| contrapose! $e with $e') => `(tactic| (revert $e:ident; contrapose!; intro $e':ident))

end Mathlib.Tactic.Contrapose
