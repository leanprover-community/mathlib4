/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.Header
import Lake
import /- -/ Mathlib.Tactic -- the `TextBased` linter does not flag this `broadImport`

/--
warning: In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter (see e.g. mathlib4#13779). Please consider carefully if this import is useful and make sure to benchmark it. If this is fine, feel free to allow this linter.
note: this linter can be disabled with `set_option linter.style.header false`
---
warning: Files in mathlib cannot import the whole tactic folder.
note: this linter can be disabled with `set_option linter.style.header false`
---
warning: The module doc-string for a file should be the first command after the imports.
Please, add a module doc-string before `/-!# Tests for the `docModule` linter
-/`.
note: this linter can be disabled with `set_option linter.style.header false`
-/
#guard_msgs in
set_option linter.style.header true in

/-!
# Tests for the `docModule` linter
-/

/--
A convenience function that replaces `/` with `|`.
This converts `/-` and `-/` into `|-` and `-|` that no longer interfere with the ending of the
`#guard_msgs` doc-string.
-/
def replaceMultilineComments (s : String) : String :=
  s.replace "/" "|"

open Lean Elab Command in
/--
`#check_copyright cop` takes as input the `String` `cop`, expected to be a copyright statement.
It logs details of what the linter would report if the `cop` is "malformed".
-/
elab "#check_copyright " cop:str : command => do
  let cop := cop.getString
  for (s, m) in Mathlib.Linter.copyrightHeaderChecks cop do
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
info: Text: ` |-`
Range: (0, 3)
Message: 'Malformed or missing copyright header: `|-` should be alone on its own line.'
-/
#guard_msgs in
#check_copyright
" /-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/
"

-- The last line does not end with a newline.
/--
info: Text: `-|`
Range: (149, 151)
Message: 'Malformed or missing copyright header: `-|` should be alone on its own line.'
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
-/"

-- TODO: should this raise an error?
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name LastName
stuff
-/
"

-- TODO: should this raise an error "Copyright too short" instead?
/--
info: Text: ``
Range: (126, 126)
Message: 'The authors line should begin with 'Authors: ''
-/
#guard_msgs in
#check_copyright
"/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
"

/--
info: Text: `Cpyright (c) 202`
Range: (3, 19)
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
info: Text: `a. All rights reserve.`
Range: (34, 56)
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
Range: (149, 151)
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

-- The `Copyright` and `Authors` lines are allowed to overflow.
#check_copyright
"/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot
-/
"
