/-
Copyright (c) 2023 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop

/-!
# Groupoid and UniversalGroupoid Rule Set

This module defines the `Groupoid` and `UniversalGroupoid` Aesop rule sets.
Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [Groupoid]
declare_aesop_rule_sets [UniversalGroupoid]
