/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Tactic.FastInstance

/-!
# Tests for `#check_instance`

`#check_instance foo` reports ✅ if the instance has correct data-field binder types
(all data fields use the exact type expected from the class declaration),
and ❌ if there is a "leak" (a data field uses a coercion-equivalent but not
`.instances`-transparent type).
-/

/--
info: ❌️ 'RestrictScalars.module': leaky binder types detected.
  The data field `smul` differs from the re-inferred canonical form at instances transparency.
  Other data fields may also be leaky.
  The `fast_instance%` elaborator may be useful as a repair or band-aid:
  `instance : ... := fast_instance% <body>`
-/
#guard_msgs in
-- `RestrictScalars.module` is leaky; fix it with `fast_instance%`.
#check_instance RestrictScalars.module

-- A minimal type alias to demonstrate the ✅ canonical case.
-- Without `fast_instance%`, the `add` field binder type would be `ℕ` rather than `MyNat`,
-- which differs at instances transparency.
def MyNat := ℕ
instance myNatInstAdd : Add MyNat := fast_instance% ⟨Nat.add⟩

/-- info: ✅️ 'myNatInstAdd': canonical (re-inferred form agrees at instances transparency) -/
#guard_msgs in
#check_instance myNatInstAdd
