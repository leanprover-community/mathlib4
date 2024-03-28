/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg, Adomas Baliuka
-/

import Aesop

/-!
# Differentiability Rule Set

This module defines the `Differentiable` Aesop rule set which is used by the
`differentiability` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Differentiable]
