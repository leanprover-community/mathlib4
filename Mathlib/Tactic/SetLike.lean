/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Aesop

/-!
# SetLike Rule Set

This module defines the `SetLike` Aesop rule set which is used by the
`SetLike` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [SetLike] (default := true)
