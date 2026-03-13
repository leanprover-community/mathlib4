/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kim Morrison
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

/-- info: ✅ 'RestrictScalars.module': canonical (re-inferred form agrees at instances transparency) -/
#guard_msgs in
-- `RestrictScalars.module` is fixed with `fast_instance%` and should be canonical.
#check_instance RestrictScalars.module

/--
info: ❌ 'RestrictScalars.opModule': leaky binder types detected.
  The body differs from the re-inferred form at instances transparency.
  Use `fast_instance%` to repair: `instance : ... := fast_instance% <body>`
-/
#guard_msgs in
-- `RestrictScalars.opModule` is defined without `fast_instance%` and is leaky.
#check_instance RestrictScalars.opModule
