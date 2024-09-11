import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Lemma

set_option linter.docPrime true

-- no warning on a primed-declaration with a doc-string containing `'`
/-- X' has a doc-string -/
def X' := 0

/--
warning: `thm_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain a justification for the presence of a `'` in their doc-string.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
theorem thm_no_doc' : True := .intro

/--
warning: `thm_with_attr_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain a justification for the presence of a `'` in their doc-string.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
@[simp]
theorem thm_with_attr_no_doc' : True := .intro

/--
warning: `inst_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain a justification for the presence of a `'` in their doc-string.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
instance inst_no_doc' : True := .intro

/--
warning: `abbrev_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain a justification for the presence of a `'` in their doc-string.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
abbrev abbrev_no_doc' : True := .intro

/--
warning: `def_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain a justification for the presence of a `'` in their doc-string.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
def def_no_doc' : True := .intro
