/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Defs

/-! ### `norm_num` plugin for `sqrt`

The `norm_num` plugin evaluates `sqrt` by bounding it between consecutive integers.

Porting note: the sole purpose of this file is to mark it as "ported".
This file seems to be tripping up the porting dashboard.

-/
