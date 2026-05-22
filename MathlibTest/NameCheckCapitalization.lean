import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma

set_option linter.style.nameCheck.capitalization true

/-! ## Positive examples (no warnings expected) -/

theorem good_snake_case : True := trivial

theorem good_with_camelCase_chunk : True := trivial

lemma good_lemma_name : True := trivial

structure GoodStruct where
  x : Nat

class GoodClass where
  y : Nat

inductive GoodInductive where
  | bar
  | baz

class inductive GoodClassInductive where
  | bar

-- A `def` whose return value is a term of a `Type` should be `lowerCamelCase`.
def goodValueDef : Nat := 0

-- A `def` whose return value is a `Type` should be `UpperCamelCase`.
def GoodTypeDef : Type := Nat

-- A `def` whose return value is a `Prop` (a "predicate") should also be `UpperCamelCase`.
def GoodPredicate (n : Nat) : Prop := n = 0

-- A `def` that ultimately produces a proof should be `snake_case`.
def good_proof_def : ∀ n : Nat, n = n := fun _ => rfl

-- `abbrev` follows the same rules as `def`.
abbrev goodValueAbbrev : Nat := 0
abbrev GoodTypeAbbrev : Type := Nat

-- `opaque` follows the same rules. The return type is `Nat`, so lowerCamelCase.
opaque goodValueOpaque : Nat

-- An `instance` returns an instance of a class (a term of a `Type`), so lowerCamelCase.
instance goodInstance : Inhabited Nat := ⟨0⟩

/-! ## Negative examples (warnings expected) -/

/--
warning: The theorem name 'BadTheoremName' does not follow the mathlib snake_case convention. Each underscore-separated chunk should start with a lowercase letter.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
theorem BadTheoremName : True := trivial

/--
warning: The theorem name 'foo_Bar_baz' does not follow the mathlib snake_case convention. Each underscore-separated chunk should start with a lowercase letter.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
theorem foo_Bar_baz : True := trivial

/--
warning: The lemma name 'BadLemma' does not follow the mathlib snake_case convention. Each underscore-separated chunk should start with a lowercase letter.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
lemma BadLemma : True := trivial

/--
warning: The structure or class name 'bad_struct' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
structure bad_struct where
  x : Nat

/--
warning: The structure or class name 'badClass' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
class badClass where
  y : Nat

/--
warning: The inductive type name 'bad_inductive' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
inductive bad_inductive where
  | bar

/--
warning: The class inductive name 'bad_class_inductive' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
class inductive bad_class_inductive where
  | bar

-- A `def` whose return value is a term of a `Type` should be `lowerCamelCase`, not
-- `UpperCamelCase`.
/--
warning: The def name 'BadValueDef' does not follow the mathlib lowerCamelCase convention. Definitions whose return value is a term of a `Type` should start with a lowercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
def BadValueDef : Nat := 0

-- A `def` whose return value is a term of a `Type` should be `lowerCamelCase`, not `snake_case`.
/--
warning: The def name 'bad_value_def' does not follow the mathlib lowerCamelCase convention. Definitions whose return value is a term of a `Type` should start with a lowercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
def bad_value_def : Nat := 0

-- A `def` whose return value is a `Type` should be `UpperCamelCase`.
/--
warning: The def name 'badTypeDef' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
def badTypeDef : Type := Nat

-- A `def` whose return value is a `Prop` (a predicate) should be `UpperCamelCase`.
/--
warning: The def name 'badPredicate' does not follow the mathlib UpperCamelCase convention. Names of types, structures, classes and inductives should start with an uppercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
def badPredicate (n : Nat) : Prop := n = 0

-- A `def` whose return value is a proof should be `snake_case`.
/--
warning: The def name 'BadProofDef' does not follow the mathlib snake_case convention. Each underscore-separated chunk should start with a lowercase letter.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
def BadProofDef : ∀ n : Nat, n = n := fun _ => rfl

-- `abbrev` follows the same rules.
/--
warning: The abbrev name 'BadValueAbbrev' does not follow the mathlib lowerCamelCase convention. Definitions whose return value is a term of a `Type` should start with a lowercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
abbrev BadValueAbbrev : Nat := 0

-- `instance` should be `lowerCamelCase`.
/--
warning: The instance name 'BadInstance' does not follow the mathlib lowerCamelCase convention. Definitions whose return value is a term of a `Type` should start with a lowercase letter and contain no underscores.
See https://leanprover-community.github.io/contribute/naming.html#capitalization.

Note: This linter can be disabled with `set_option linter.style.nameCheck.capitalization false`
-/
#guard_msgs in
instance BadInstance : Inhabited Nat := ⟨0⟩

/-! ## Default off: when the option is not set, nothing is flagged. -/

set_option linter.style.nameCheck.capitalization false in
theorem Silenced_When_Off : True := trivial
