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


-- Make sure Verso is indeed enabled when we do `set_option docs.verso true`.

/--
warning: Code block could be more specific.

Hint: Insert a specific kind of code block:
  ```l̲e̲a̲n̲
-/
#guard_msgs in
set_option doc.verso true in
/--
```
#check foo
```
-/
def bar : Nat := 37 * 2
