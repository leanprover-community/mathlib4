module

public import Lean

open Lean Elab Tactic Doc in
/-- Writing `{insertDocstringOf foo}` inside a verso doc-string inserts the doc-string of
declaration `foo` in the current environment, as a separate paragraph.
If `foo` does not exist or has no doc-string, it throws an error.
-/
@[doc_command] meta def _root_.insertDocstringOf (n : Ident) :
    DocM <| Block ElabInline ElabBlock := do
  let doc ← realizeGlobalConstNoOverloadWithInfo n
  let some docStr ← findDocString? (← getEnv) doc
    | throwError "No doc-string for `{.ofConstName doc}`"
  -- Future: once there is a better auto-converter between markdown and verso doc-strings,
  -- rewrite this code accordingly!
  -- Perhaps, it could be nice to write .verso here.
  return .para #[.text docStr]

/-- `Foo` is my favourite definition -/
def Foo := 0

-- via `lake build`, this works
set_option doc.verso true in
set_option doc.verso.suggestions false in
/-- `bar` is somehow related to `Foo`: let's include its doc-string

{insertDocstringOf Foo}
-/
theorem bar : True := trivial

#check Nat

set_option doc.verso true in
set_option doc.verso.suggestions false in
/-- a doc-string including a doc-string of an item defined in a previous module

{insertDocstringOf Nat}
-/
theorem baz : True := trivial
