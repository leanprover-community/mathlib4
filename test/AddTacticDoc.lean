import Mathlib.Tactic.AddTacticDoc
open Lean Elab

/--My docstring for :one-/
def one   := 1
def two   := 2
/--My docstring for :three-/
def three := 3

def tde : TacticDocEntry := {
  name       := "something outlandish",
  category   := DocCategory.hole_cmd,
  decl_names := [`one],
  tags       := ["not", "necessarily", "existent"]
}

def tde2 : TacticDocEntry := {
  name       := "something outlandish",
  category   := DocCategory.hole_cmd,
  decl_names := [`one],
  inherit_description_from := `three
}

-- 1. Test add_tactic_doc: use meta docstring
/--meta!-/
add_tactic_doc tde

#eval show TermElabM _ from do
  let tdes ← tactic.getTacticDocEntries
  guard (tdes.length == 1)
  if let some tde := tdes[0]? then
    guard (tde.snd == "meta!")

-- 2. Test add_tactic_doc: use the docstring of a single declaration from decl_names
add_tactic_doc tde

#eval show TermElabM _ from do
  let tdes ← tactic.getTacticDocEntries
  guard (tdes.length == 2)
  if let some tde := tdes[0]? then
    guard (tde.snd == "My docstring for :one")

-- 3. Test add_tactic_doc: use inherit_description_from
add_tactic_doc tde2

#eval show TermElabM _ from do
  let tdes ← tactic.getTacticDocEntries
  guard (tdes.length == 3)
  if let some tde := tdes[0]? then
    guard (tde.snd == "My docstring for :three")

-- 4. Test add_tactic_doc: create the tacticDocEntry on the fly
add_tactic_doc {
  name       := "never defined separately",
  category   := DocCategory.hole_cmd,
  decl_names := [`one]
}

#eval show TermElabM _ from do
  let tdes ← tactic.getTacticDocEntries
  guard (tdes.length == 4)
