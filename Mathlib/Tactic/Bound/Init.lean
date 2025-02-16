/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Mathlib.Init
import Aesop.Frontend.Command

/-!
# Bound Rule Set

This module defines the `Bound` Aesop rule set which is used by the
`bound` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Bound]
