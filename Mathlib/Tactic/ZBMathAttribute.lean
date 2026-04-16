/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# The `zbmath` attribute

This allows tagging of mathlib results corresponding to key mathematical concepts,
for use with automatic linking in the zbmath database.
-/

public meta section

open Lean Elab

namespace Mathlib.ZBMathTag

/-- `Tag` is the structure that carries the data of a project tag and a corresponding
Mathlib declaration. -/
structure Tag where
  /-- The name of the declaration with the given tag. -/
  declName : Name
  /-- The database tag. -/
  tag : String
  /-- The (optional) comment that comes with the given tag. -/
  comment : String
  deriving BEq, Hashable

/-- Defines the `tagExt` extension for storing all `Tag`s in the environment.
`addImportedFn` is a constant function to avoid a performance overhead during initialization. -/
initialize tagExt : SimplePersistentEnvExtension Tag (Array (Array Tag)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn tags := tags
    addEntryFn tags _ := tags
  }

/--
`addTagEntry declName tag comment` takes as input the `Name` `declName` of a declaration and
the `String`s `tag` and `comment` of the `zbmath` attribute.
It extends the `Tag` environment extension with the data `declName, tag, comment`.
-/
def addTagEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (tag comment : String) : m Unit :=
  modifyEnv (tagExt.addEntry ·
    { declName := declName, tag := tag, comment := comment })

end Mathlib.ZBMathTag

open Mathlib.ZBMathTag

namespace Mathlib.ZBMathTag

/-- The `zbMathTag` attribute. Use it as `@[zbMath "concept" "Optional comment"]` -/
syntax (name := zbMathTag) "zbmath" ppSpace str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `zbMathTag
  descr := "Apply a zbmath tag to a theorem."
  add := fun decl stx _attrKind => do
    let (tag, comment) ← match stx with
    | `(attr| zbmath $tag $[$comment]?) => pure (tag, comment)
    | _ => throwUnsupportedSyntax
    addTagEntry decl tag.getString ((comment.map (·.getString)).getD "")
  -- docstrings are immutable once an asynchronous elaboration task has been started
  applicationTime := .beforeElaboration
}

end Mathlib.ZBMathTag

/--
`getSortedZBMathTags env` returns the array of `Tags`, sorted by alphabetical order of tag.
-/
private def Lean.Environment.getSortedZBMathTags (env : Environment) : Array Tag :=
  let tags := PersistentEnvExtension.getState tagExt env
  tags.2.flatten.appendList tags.1 |>.qsort (·.tag < ·.tag)

-- unused!
/--
`getSortedZBMathDeclNames env tag` returns the array of declaration names of results
with zbmath concept equal to `tag`.
-/
private def Lean.Environment.getSortedZBMathDeclNames (env : Environment) (tag : String) :
    Array Name :=
  let tags := env.getSortedZBMathTags
  tags.filterMap fun d => if d.tag == tag then some d.declName else none

namespace Mathlib.ZBMathTag

/--
`traceZBMathTags verbose` prints the zbmath tags to the user and
inlines the theorem statements if `verbose` is `true`.
-/
def traceZBMathTags (verbose : Bool := false) : Command.CommandElabM Unit := do
  let env ← getEnv
  let entries := env.getSortedZBMathTags
  if entries.isEmpty then logInfo "No tags found." else
  let mut msgs := #[m!""]
  for d in entries do
    let (parL, parR) := if d.comment.isEmpty then ("", "") else (" (", ")")
    let cmt := parL ++ d.comment ++ parR
    msgs := msgs.push
      m!"ZBMath concept {d.tag} corresponds to declaration '{.ofConstName d.declName}'.{cmt}"
    if verbose then
      let dType := ((env.find? d.declName).getD default).type
      msgs := (msgs.push m!"{dType}").push ""
  let msg := MessageData.joinSep msgs.toList "\n"
  logInfo msg

/--
`#zbmath_concepts` retrieves all declarations that have the `zbmath` attribute.

For each found declaration, it prints a line
```
'declaration_name' corresponds to tag 'declaration_tag'.
```
The variant `#zbmath_concepts!` also adds the theorem statement after each summary line.
-/
elab (name := zbmathConcepts) "#zbmath_concepts" tk:("!")?: command =>
  traceZBMathTags (tk.isSome)

end Mathlib.ZBMathTag
