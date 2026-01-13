/-
Copyright (c) 2026 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import Mathlib.Tactic.Linter.Header

set_option doc.verso true in
/-!
# Test that Verso docstrings are recognized as module docs.
-/

#guard_msgs in
set_option linter.style.header true in
set_option doc.verso true in
def foo : Nat := 37
