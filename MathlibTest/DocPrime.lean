import Mathlib.Tactic.Linter.DocPrime
import Mathlib.Tactic.Lemma

set_option linter.docPrime true

-- no warning on a primed-declaration with a doc-string containing `'`
/-- X' has a doc-string -/
def X' := 0

-- no warning on a declaration whose name contains a `'` *and does not end with it*
def X'X := 0

-- A list of universe names in the declaration is handled correctly, i.e. warns.
/--
warning: `Y'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
def Y'.{u} := ULift.{u} Nat

namespace X
/--
warning: `ABC.thm_no_doc1'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
theorem _root_.ABC.thm_no_doc1' : True := .intro

/--
warning: `X.thm_no_doc2'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
theorem thm_no_doc2' : True := .intro

end X

/--
warning: `thm_no_doc'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
theorem thm_no_doc' : True := .intro

/--
warning: `thm_with_attr_no_doc'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
@[simp]
theorem thm_with_attr_no_doc' : True := .intro

/--
warning: `inst_no_doc'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
instance inst_no_doc' : True := .intro

/--
warning: `abbrev_no_doc'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
abbrev abbrev_no_doc' : True := .intro

/--
warning: `def_no_doc'` is missing a doc-string, please add one.
Declarations whose name ends with a `'` are expected to contain an explanation for the presence of a `'` in their doc-string. This may consist of discussion of the difference relative to the unprimed version, or an explanation as to why no better naming scheme is possible.

Note: This linter can be disabled with `set_option linter.docPrime false`
-/
#guard_msgs in
def def_no_doc' : True := .intro

-- Anonymous declarations in a primed namespace should not get flagged by the linter.
namespace Foo'

example : True := .intro
instance : True := .intro

end Foo'
