/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init
public import Aesop

/-! # Finiteness tactic attribute -/

public meta section

declare_aesop_rule_sets [finiteness]
