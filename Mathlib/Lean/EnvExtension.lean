/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Lean.ScopedEnvExtension

import Mathlib.Init

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Helper function for environment extensions and attributes.
-/

public section

open Lean

instance {σ : Type} [Inhabited σ] : Inhabited (ScopedEnvExtension.State σ) := ⟨{state := default}⟩
