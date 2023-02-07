/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Aesop

/-!
# Continuity

We define the `continuity` tactic using `aesop`. -/

declare_aesop_rule_sets [Continuous]

set_option hygiene false in -- We have to turn off the hygiene to use the `Continuous` rule set
/-- The `continuity` attribute -/
macro "continuity" : attr => `(attr|aesop safe apply (rule_sets [Continuous]))

set_option hygiene false in
/-- The `continuity` tactic -/
macro "continuity" : tactic =>
  `(tactic|aesop (rule_sets [Continuous]))

-- syntax (name := continuity) "continuity" (config)? : tactic
-- syntax (name := continuity!) "continuity!" (config)? : tactic
-- syntax (name := continuity?) "continuity?" (config)? : tactic
-- syntax (name := continuity!?) "continuity!?" (config)? : tactic
