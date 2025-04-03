/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Aesop

/-!
# Rule sets related to topological (pre)sheaves

This module defines the `Restrict` Aesop rule set. Aesop rule sets only become
visible once the file in which they're declared is imported, so we must put this
declaration into its own file.
-/

/- to prove subset relations -/
declare_aesop_rule_sets [Restrict]
