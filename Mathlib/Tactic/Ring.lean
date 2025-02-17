/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: euprunin
-/

import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Ring.PNat

/-!
We register `ring` with the `hint` tactic.
-/

register_hint ring
