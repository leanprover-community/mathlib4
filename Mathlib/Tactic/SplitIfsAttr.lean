/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, David Renshaw
-/

import Lean

/-!
  Companion file to SplitIfs.lean. Lean does not allow attributes to be used
  in the same file that they are defined.
-/

/--
  Attribute to tag simp lemmas used in the `split_ifs` tactic.
-/
register_simp_attr split_ifs_reduction
