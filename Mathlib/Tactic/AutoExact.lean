/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/

/-!
# Zero-character term tactic

This file turns every term into a tactic:
```lean
example : True := by True.intro
-- expands to:
example : True := by refine True.intro
```

-/

macro (priority := 0) t:term : tactic => `(tactic| refine $t)
