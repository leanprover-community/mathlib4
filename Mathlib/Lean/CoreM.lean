/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Lean

/-!
# `mkFreshNameFrom`

Temporary file. Should be moved to core.
-/

namespace Lean

namespace Name

/-- `mkFreshNameFrom orig base` returns `mkFreshUserName base` if ``orig = `_``
and `orig` otherwise. -/
def mkFreshNameFrom (orig base : Name) : CoreM Name :=
  if orig = `_ then mkFreshUserName base else pure orig
