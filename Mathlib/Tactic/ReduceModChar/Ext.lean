
/-!
# `@[reduce_mod_char]` attribute

This file registers `@[reduce_mod_char]` as a `simp` attribute.
-/

public meta section

open Lean Meta

/-- `@[reduce_mod_char]` is an attribute that tags lemmas for preprocessing and cleanup in the
`reduce_mod_char` tactic -/
initialize reduceModCharExt : SimpExtension ←
  registerSimpAttr `reduce_mod_char
    "lemmas for preprocessing and cleanup in the `reduce_mod_char` tactic"
