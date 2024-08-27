/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Attributes

/-!
# The `stacks` attribute

This allows tagging of mathlib lemmas with the corresponding
[Tags](https://stacks.math.columbia.edu/tags) from the Stacks Project.
-/

open Lean

namespace Mathlib.Stacks

/--
The syntax for a Stacks tag: it is an optional number followed by an optional identifier.
This allows `044Q3` and `GH3F6` as possibilities.
-/
declare_syntax_cat stackTag

@[inherit_doc Parser.Category.stackTag]
syntax (num)? (ident)? : stackTag

/-- The `stacks` attribute.
Use it as `@[stacks TAG "Optional comment"]`.
The `TAG` is mandatory.

See the [Tags page](https://stacks.math.columbia.edu/tags) in the Stacks project for more details.
-/
syntax (name := stacks) "stacks " (stackTag)? (str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `stacks
  descr := "Apply a Stacks project tag to a theorem."
  add := fun _decl stx _attrKind => Lean.withRef stx do
    -- check that the tag consists of 4 characters and
    -- that only digits and uppercase letter are present
    let tag := stx[1]
    if let some s := tag.getSubstring? then
      let str := s.toString.trimRight
      if str.length != 4 then
        logWarningAt tag
          m!"Tag '{str}' is {str.length} characters long, but it should be 4 characters long"
      if 2 ≤ (str.split (fun c => (!c.isUpper) && !c.isDigit)).length then
        logWarningAt tag m!"Tag '{str}' should only consist of digits and uppercase letters"
    match stx with
      | `(attr| stacks $_:stackTag $_:str) => return
      | `(attr| stacks $_:stackTag) => return
      | _ => logWarning "Please, enter a Tag after `stacks`."
}
