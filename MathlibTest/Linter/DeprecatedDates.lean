/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
import Mathlib.Tactic.Linter.DeprecatedDates

/-!
# Tests for the DeprecatedDates linter

Tests for the linter that checks consecutive deprecated declarations
have consistent date formatting.
-/

set_option linter.style.deprecatedDates true

-- Define replacement definitions first
def newFoo := 1
def newBar := 2
def newBaz := 3

section ConsecutiveDifferentDates

-- Test: consecutive deprecated declarations with different dates and no blank line (should warn)
@[deprecated newFoo (since := "2025-01-01")]
def oldFoo := 1
@[deprecated newBar (since := "2025-02-01")]
def oldBar := 2

end ConsecutiveDifferentDates

section ConsecutiveSameDates

-- Test: consecutive deprecated declarations with same date (should be OK)
@[deprecated newFoo (since := "2025-01-01")]
def oldFoo2 := 1
@[deprecated newBar (since := "2025-01-01")]
def oldBar2 := 2

end ConsecutiveSameDates

section WithBlankLine

-- Test: consecutive deprecated declarations with different dates but with blank line (should be OK)
@[deprecated newFoo (since := "2025-01-01")]
def oldFoo3 := 1

@[deprecated newBar (since := "2025-02-01")]
def oldBar3 := 2

end WithBlankLine

section NonConsecutive

-- Test: non-deprecated declaration in between resets the state (should be OK)
@[deprecated newFoo (since := "2025-01-01")]
def oldFoo4 := 1

def normalDecl := 5

@[deprecated newBar (since := "2025-02-01")]
def oldBar4 := 2

end NonConsecutive
