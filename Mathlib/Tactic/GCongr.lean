/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Jovan Gerbscheid, Yury Kudryashov
-/
module

public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.Hint

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`. -/

public section

namespace Mathlib.Tactic.GCongr

variable {a b c d : Prop}

/-- A version of `imp_imp_imp` that has an extra hypothesis `c` in the `b → d` hypothesis. -/
@[gcongr] lemma imp_mono (h₁ : c → a) (h₂ : c → b → d) : (a → b) → c → d :=
  fun h₃ hc => h₂ hc (h₃ (h₁ hc))

/-- Monotonicity of conjunction, with an extra hypothesis `a` in the `b → d` hypothesis. -/
@[gcongr] lemma and_mono (h₁ : a → c) (h₂ : a → b → d) : (a ∧ b) → c ∧ d :=
  fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩

attribute [gcongr] mt Or.imp forall_imp Exists.imp
  List.Sublist.append List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.cons List.Perm.append List.Perm.map
  List.cons_subset_cons
  Nat.sub_le_sub_left Nat.sub_le_sub_right Nat.sub_lt_sub_left Nat.sub_lt_sub_right
  Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div

-- `Nat.pow_le_pow_right` has side condition `0 < n`, which `gcongr` discharges automatically via
-- `positivity`, unlike the `1 ≤ a` side condition of the more general `pow_le_pow_right₀`.
attribute [gcongr high] Nat.pow_le_pow_right


/-! We also use `assumption` to discharge side goals.
In a further downstream file, `positivity` will also be registered as a discharger.
From that point, `positivity` will be tried before `assumption` is: that is perfectly fine. -/
macro_rules | `(tactic| gcongr_discharger) => `(tactic| assumption)

/-!
We register `gcongr` with the `hint` tactic.
-/

register_hint 1000 gcongr

end Mathlib.Tactic.GCongr
