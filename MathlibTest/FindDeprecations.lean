import Mathlib.Tactic.Linter.FindDeprecations

open Mathlib.Tactic

#guard parseLine "" == none
#guard parseLine "a: []" == some []
#guard parseLine "a: [1, 2, 3]" == some [⟨1⟩, ⟨2⟩, ⟨3⟩]
#guard parseLine "info: File/Path.lean:12:0: [362, 398, 399]" == some [⟨362⟩, ⟨398⟩, ⟨399⟩]

/--
info:
01234567   9
0134567   9
0134569
-/
#guard_msgs in
#eval show Lean.Elab.Term.TermElabM _ from do
  let file := "01234567   9"
  IO.println s!"\n{file}"
  guard <| -- An empty array of changes leaves `file` unchanged
    removeRanges file #[] == file
  IO.println <| removeRanges file #[⟨⟨2⟩, ⟨3⟩⟩]
  guard <| -- Removing a single character not followed by whitespace, removes that character only
    removeRanges file #[⟨⟨2⟩, ⟨3⟩⟩] == file.replace "2" ""
  IO.println <| removeRanges file #[⟨⟨2⟩, ⟨3⟩⟩, ⟨⟨7⟩, ⟨8⟩⟩]
  guard <| -- Also removing a range followed by whitespace, removes the trailing whitespace as well
    removeRanges file #[⟨⟨2⟩, ⟨3⟩⟩, ⟨⟨7⟩, ⟨8⟩⟩] ==
                 ((file.replace "2" "").replace "7" "").replace " " ""
