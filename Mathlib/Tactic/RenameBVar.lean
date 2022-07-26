/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Patrick Massot
-/

import Lean
import Mathlib.Util.Tactic

namespace Mathlib.Tactic

open Lean Parser Elab Tactic

syntax "rename_bvar " ident " → " ident (ppSpace location)? : tactic

/--
* `rename_bvar old new` renames all bound variables named `old` to `new` in the target.
* `rename_bvar old new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m :=
begin
  rename_bvar n q at h, -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_bvar m n, -- target is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
end
```
Note: name clashes are resolved automatically.
-/
elab_rules : tactic
  | `(tactic| rename_bvar $old → $new at $loc) =>
    withLocation (expandLocation loc)
      (renameBVarHyp old.getId new.getId)
      (renameBVarTarget old.getId new.getId)
      fun _ => pure ()
  | `(tactic| rename_bvar $old → $new) => renameBVarTarget old.getId new.getId

example (h : ∀ a b : Nat, a = b → b = a) : ∀ a b : Nat, a = b → b = a := by
  rename_bvar a → x at h -- why doesn't this work?
  exact h
