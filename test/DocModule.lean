/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.DocModule

/-!
# Tests for the `docModule` linter
-/

/--
A convenience function that replaces `/-` with `→` and `-/` with `←`.
Without this replacement, using `#guard_msgs` for a message that contains these strings is a
major headache!
-/
def replaceMultilineComments (s : String) : String :=
  (s.replace "/-" "→").replace "-/" "←"

open Lean Elab Command in
/--
`#check_copyright cop` takes as input the `String` `cop`, expected to be a copyright statement.
It logs details of what the linter would report if the `cop` is "malformed".
-/
elab "#check_copyright " cop:str : command => do
  let cop := cop.getString
  for (s, m) in Mathlib.Linter.copyrightHeaderLinter cop do
    match s.getRange? with
      | none => logWarning "Should have range"
      | some rg =>
        logInfo
          m!"Text: `{replaceMultilineComments s.getAtomVal}`\n\
             Range: {(rg.start, rg.stop)}\n\
             Message: '{replaceMultilineComments m}'"

-- well-formed
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName, Name LastName,
Name LastName,
 Name LastName,
  Name LastName
-/
"

/--
info: Text: ` →`
Range: (0, 3)
Message: 'Malformed or missing copyright header: `→` should be alone on its own line.'
-/
#guard_msgs in
#check_copyright
" /-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/
"

/--
info: Text: `←`
Range: (149, 151)
Message: 'Malformed or missing copyright header: `←` should be alone on its own line.'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/"

/--
info: Text: `Cpyright (c) 2`
Range: (3, 17)
Message: 'Copyright line should start with 'Copyright (c) YYYY''
-/
#guard_msgs in
#check_copyright
"/-
Cpyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/
"

/--
info: Text: ` All rights reserve.`
Range: (36, 56)
Message: 'Copyright line should end with '. All rights reserved.''
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserve.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/
"

/--
info: Text: `Rleased under Apache 2.0 license as described in the file LICENSE.`
Range: (58, 124)
Message: 'Second copyright line should be
"Released under Apache 2.0 license as described in the file LICENSE."'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Rleased under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/
"

/--
info: Text: `A uthors:`
Range: (126, 135)
Message: 'The authors line should begin with 'Authors: ''
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
A uthors: Name LastName
-/
"

/--
info: Text: `  `
Range: (139, 141)
Message: 'Double spaces are not allowed.'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name  LastName
-/
"

/--
info: Text: `.`
Range: (148, 149)
Message: 'Please, do not end the authors' line with a period.'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName.
-/
"

/--
info: Text: `  `
Range: (150, 152)
Message: 'Double spaces are not allowed.'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName,
   Name LastName
-/
"
