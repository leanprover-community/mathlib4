/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Aesop

/-!
# arith_mult Rule Set

This module defines the `IsMultiplicative` Aesop rule set which is used by the
`arith_mult` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [IsMultiplicative]
