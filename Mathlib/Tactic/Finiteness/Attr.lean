/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public meta import Aesop.Frontend

import Mathlib.Init

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Finiteness tactic attribute
-/

declare_aesop_rule_sets [finiteness]
