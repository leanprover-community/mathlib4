/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init
public import Aesop.Frontend

/-! # Finiteness tactic attribute -/
set_option backward.defeqAttrib.useBackward true

declare_aesop_rule_sets [finiteness]
