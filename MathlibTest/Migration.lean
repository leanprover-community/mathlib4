/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

import Mathlib.Migration
import Lean.Elab.GuardMsgs

/-! # Tests for the `Mathlib.Migration` Verso docstring roles. -/

library_note «migration role test» /-- A note used to test the `library_note` role. -/

-- The `{url}` role renders a link without diagnostics.
#guard_msgs in
set_option doc.verso true in
/-- See {url}`https://leanprover.org`. -/
def urlTest : Nat := 0

-- The `{library_note}` role accepts a known label without diagnostics.
#guard_msgs in
set_option doc.verso true in
/-- See {library_note}`migration role test`. -/
def libraryNoteTest : Nat := 0

-- The `{library_note}` role warns on an unknown label, allowing forward references.
/-- warning: No library note with label `does not exist`. -/
#guard_msgs in
set_option doc.verso true in
/-- See {library_note}`does not exist`. -/
def libraryNoteFailTest : Nat := 0

-- The `{cite}` role accepts a key present in `docs/references.bib` without diagnostics.
#guard_msgs in
set_option doc.verso true in
/-- See {cite "Adamek_Rosicky_1994"}[Adámek–Rosický]. -/
def citeTest : Nat := 0

-- The `{cite}` role warns on a key absent from `docs/references.bib`.
/-- warning: No bibliography entry `NotARealKey` in `docs/references.bib`. -/
#guard_msgs in
set_option doc.verso true in
/-- See {cite "NotARealKey"}[text]. -/
def citeFailTest : Nat := 0

-- The `code` code block records its language and renders verbatim, without diagnostics.
#guard_msgs in
set_option doc.verso true in
/--
```code python
print("hi")
```
-/
def codeTest : Nat := 0
