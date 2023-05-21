/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module topology.tactic
! leanprover-community/mathlib commit 79abf670d5f946912964c232736e97a761f29ebb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity

/-!
# Tactics for topology

Currently we have one domain-specific tactic for topology: `continuity`.
It is implemented in `Mathlib.Tactic.Continuity`.

Porting note: the sole purpose of this file is to mark it as "ported".
This file seems to be tripping up the porting dashboard.

-/
