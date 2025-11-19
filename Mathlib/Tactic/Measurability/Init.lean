/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Init
public meta import Aesop

/-!
# Measurability Rule Set

This module defines the `Measurable` Aesop rule set which is used by the
`measurability` tactic. Aesop rule sets only become visible once the file in which
they're declared is imported, so we must put this declaration into its own file.
-/

public meta section

declare_aesop_rule_sets [Measurable]
