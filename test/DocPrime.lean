import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Lemma

set_option linter.docPrime true

-- no warning on a primed-declaration with a doc-string containing `'`
/-- X' has a doc-string -/
def X' := 0

/--
warning: `thm_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
theorem thm_no_doc' : True := .intro

/--
warning: `thm_with_attr_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
@[simp]
theorem thm_with_attr_no_doc' : True := .intro

/--
warning: `inst_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
instance inst_no_doc' : True := .intro

/--
warning: `abbrev_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
abbrev abbrev_no_doc' : True := .intro

/--
warning: `def_no_doc'` is missing doc-string, please add one.
Declarations whose name contains a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.
note: this linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
def def_no_doc' : True := .intro
