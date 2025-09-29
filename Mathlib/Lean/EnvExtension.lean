/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init
public import Lean.ScopedEnvExtension

@[expose] public section

/-!
# Helper function for environment extensions and attributes.
-/

open Lean

instance {σ : Type} [Inhabited σ] : Inhabited (ScopedEnvExtension.State σ) := ⟨{state := default}⟩
