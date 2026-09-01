/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify.Core

/-!
# `basify` for `ℕ∞`

`ℕ∞` is `WithTop ℕ`, so a single case split separates `⊤` from the natural numbers. The lemmas are
the ones the specialised `enat_to_nat` tactic already uses; `basify` reuses them so that goals
mixing `ℕ∞` with other registered types are handled in one pass.
-/

public section

namespace Mathlib.Tactic.Basify

attribute [basify_elim] ENat.recTopCoe

attribute [basify_split] top_add ENat.sub_top ENat.top_sub_natCast ENat.mul_top ENat.top_mul
  ENat.natCast_ne_top ENat.top_ne_natCast ENat.natCast_lt_top ENatToNat.not_lt_top
  top_le_iff le_top
  ne_eq not_false_eq_true OfNat.ofNat_ne_zero

attribute [basify_cast, basify_op] ENatToNat.coe_add ENatToNat.coe_sub
  ENatToNat.coe_mul ENatToNat.coe_ofNat ENatToNat.coe_zero ENatToNat.coe_one

attribute [basify_cast] ENat.natCast_inj ENat.natCast_le_natCast ENat.natCast_lt_natCast

end Mathlib.Tactic.Basify
