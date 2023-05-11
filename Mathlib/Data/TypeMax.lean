/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Tactic.Lint

/-!
# Workaround for changes in universe unification

Universe inequalities in Mathlib 3 are expressed through use of `max u v`. Unfortunately,
this leads to unbound universes which cannot be solved for during unification, eg
`max u v =?= max v ?`. The current solution is to wrap `Type max u v` (and other concrete
categories) in `TypeMax.{u,v}` to expose both universe parameters directly.

See also
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.233463.20universe.20constraint.20issues
-/

@[nolint checkUnivs]
abbrev TypeMax.{u, v} := Type max u v
