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

/-! ### Names with unusual components

`#check_instance` extracts the instance name structurally from the `Expr` embedded in the
trace `MessageData` rather than parsing the rendered header. This handles names that the
previous string-based extraction would have mangled, e.g. instances declared `private`, or
names containing dots inside escaped components. -/

-- A `private` instance: the actual registered `Name` is mangled (e.g.
-- `_private.MathlibTest.CheckInstance.0.privInstAdd`), but `pp.privateNames := false`
-- (the default for user output) renders just the short form.
def MyNat2 := ℕ
private instance privInstAdd : Add MyNat2 := fast_instance% ⟨Nat.add⟩

/-- info: ✅️ 'privInstAdd': canonical (re-inferred form agrees at instances transparency) -/
#guard_msgs in
#check_instance privInstAdd

-- A name with an escaped dotted component. The old string-based extractor split on
-- `"apply "` and `" to "`, then stripped trailing `.{…}` universe annotations; round-tripping
-- through those parsers via `.toName` would re-split the escaped dot. Structural extraction
-- is immune to this.
def MyNat3 := ℕ
instance «odd.name.with.dots» : Add MyNat3 := fast_instance% ⟨Nat.add⟩

/--
info: ✅️ '«odd.name.with.dots»': canonical (re-inferred form agrees at instances transparency)
-/
#guard_msgs in
#check_instance «odd.name.with.dots»
