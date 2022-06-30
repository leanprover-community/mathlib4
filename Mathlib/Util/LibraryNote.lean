/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

namespace Mathlib.Util.LibraryNote

open Lean

def LibraryNoteEntry := String × String

initialize libraryNoteExt : SimplePersistentEnvExtension LibraryNoteEntry (Array LibraryNoteEntry) ←
  registerSimplePersistentEnvExtension {
    name := `library_note
    addEntryFn := Array.push
    addImportedFn := Array.concatMap id
  }

def getDocCommentContent (stx : Syntax) : String :=
  let val := stx[1].getAtomVal!
  val.extract 0 (val.endPos - ⟨2⟩)

open Lean Parser Command in
elab "library_note " title:strLit ppSpace text:docComment : command => do
  modifyEnv (libraryNoteExt.addEntry · (title.1.isStrLit?.get!, getDocCommentContent text))
