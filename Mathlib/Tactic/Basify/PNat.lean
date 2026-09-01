/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.Basify.Core

/-!
# `basify` for `ℕ+`

`ℕ+` is the subtype of the positive naturals, so it is handled the way `ℝ≥0` is: nothing is taken
apart, the positivity of each atom is recorded, and the propositions move to `ℕ`. The lemmas are
the ones the specialised `pnat_to_nat` tactic already uses.
-/

public section

namespace Mathlib.Tactic.Basify

/-- A `Subtype.mk`-free eliminator for `ℕ+`, exposing the underlying natural and its positivity. -/
@[elab_as_elim, basify_elim]
def _root_.PNat.recToPNat {C : ℕ+ → Sort*} (mk : ∀ (n : ℕ) (_pos : 0 < n), C n.toPNat') (t : ℕ+) :
    C t :=
  PNat.coe_toPNat' t ▸ mk t t.pos

attribute [basify_simp] PNatToNat.coe_inj PNatToNat.coe_le_coe PNatToNat.coe_lt_coe
  PNat.toPNat'_coe

attribute [basify_simp, basify_op] PNat.one_coe PNat.val_ofNat PNat.add_coe PNat.mul_coe
  PNatToNat.sub_coe

end Mathlib.Tactic.Basify
