/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.Lint

/-!
# FIXME needs documentation

See also
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.233463.20universe.20constraint.20issues
-/

@[nolint checkUnivs]
abbrev TypeMax.{u, v} := Type max u v
