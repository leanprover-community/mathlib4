/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Lean.Meta.Tactic.Simp

/-!
# `@[reduce_mod_char]` attribute

This file registers `@[reduce_mod_char]` as a `simp` attribute.
-/

open Lean Meta

initialize reduceModCharExt : SimpExtension ←
  registerSimpAttr `reduce_mod_char
    "lemmas for preprocessing and cleanup in the `reduce_mod_char` tactic"
