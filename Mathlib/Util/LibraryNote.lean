/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

/-!
# Define the `library_note` command.
-/

namespace Mathlib.Util.LibraryNote

open Lean

/-- A library note consists of a (short) tag and a (long) note. -/
def LibraryNoteEntry := String × String

/-- Environment extension supporting `library_note`. -/
initialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) ←
  registerSimplePersistentEnvExtension {
    name := `library_note
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

/-- Extract the doc-comment from a `Syntax`. -/
-- TODO move?
def getDocCommentContent (stx : Syntax) : String :=
  let val := stx[1].getAtomVal!
  val.extract 0 (val.endPos - ⟨2⟩)

open Lean Parser Command in
/--
```
/-- ... some explanation ... -/
library_note "some tag"
```
creates a new "library note", which can then be cross-referenced using
```
-- See note [some tag]
```
in doc-comments.
-/
elab "library_note " title:strLit ppSpace text:docComment : command => do
  modifyEnv (libraryNoteExt.addEntry · (title.1.isStrLit?.get!, getDocCommentContent text))
