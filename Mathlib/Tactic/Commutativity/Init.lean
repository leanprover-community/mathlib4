/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir (based on Measurability by Miyahara Kō)
-/

import Aesop

/-!
# Commutativity Rule Set

This module defines the `Commute` Aesop rule set which is used by the
`commutativity` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Commute]
