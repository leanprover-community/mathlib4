import Mathlib.Tactic.Linter.Indentation
import Mathlib.Tactic.Lemma

/--
Override the original `#guard_msgs` with `whitespace := lax` to allow delete blank line in messages
to make tests tight
-/
local macro doc:(docComment)? "#guard_msgs" "in" cmd:command : command => `(
  $[$doc]? #guard_msgs(drop info, warning, whitespace := lax) in $cmd
)

set_option linter.indentation true

section Declaration

-- arguments
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example
  (a : Nat) : Nat := a

-- type
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) :
  Nat := a

-- `:`
/--
warning: should not be at the beginning of a line
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat)
    : Nat := a

-- `:=`
/--
warning: should not be at the beginning of a line
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat
  := a

/--
warning: too many spaces, which should be at most 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat :=
    a

-- additional indentation of declaration value's subsyntax is enforced to be not less than 2 spaces
/--
warning: too few spaces, which should be at least 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat := 1 +
a

-- `by`
/--
warning: should not be at the beginning of a line
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat :=
  by exact a

-- after `by`
/--
warning: too few spaces, which should be at least 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat := by
exact a

-- after `by`
/--
warning: too many spaces, which should be at most 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (a : Nat) : Nat := by
    exact a

/-
The right bracket in brackets pair like `[ ]` is sometimes immuned from being enforced by the
requirement about additional indentation. Here it should still be indented by 4 spaces. This "hard"
limitation is checked in a text-based way.
-/
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (_ : Nat) : ! List.isEmpty (α := Nat) [1
  ] := by decide

-- An example where the right bracket is immuned from additional indentation requirement.
/---/
#guard_msgs in
example : List Nat := [
  1
]

/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
example (_ : Nat) : by
  exact True := trivial

-- modifiers
/--
warning: too many spaces, which should be at most 0
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
/-- doc comment is a kind of modifiers -/
@[simp]
  noncomputable
example : Nat := 1

-- initial indentation of modifiers
/--
warning: too many spaces, which should be at most 0
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
  @[simp]
noncomputable
example : Nat := 1

-- initial indentation of the declaration (without modifier)
/--
warning: too many spaces, which should be at most 0
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
  example : Nat := 1

-- in `mutual`
/-- -/
#guard_msgs in
mutual
  example : Nat := 1
end

-- in `mutual`
/-- -/
#guard_msgs in
mutual
  example :
      Nat := 1
end

-- in `mutual`
/--
warning: too few spaces, which should be at least 6
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
mutual
  example :
    Nat := 1
end

-- `theorem`
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
theorem
  thm1 : True := trivial

-- `theorem`
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
theorem thm2 :
  True := trivial

-- `def`
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
def def1 :
  Nat := 1

-- `def` with `deriving`
/-- -/
#guard_msgs in
def def2 := Nat
deriving Repr

-- 2 additional spaces of `deriving` is also allowed
/-- -/
#guard_msgs in
def def3 := Nat
  deriving Repr

-- but no more than 2
/--
warning: too many spaces, which should be at most 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
def def4 := Nat
    deriving Repr

-- opaque
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
opaque opaque1 :
  Nat

-- opaque with value
/--
warning: too few spaces, which should be at least 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
opaque opaque2 : Nat :=
2

-- opaque with value
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
axiom aximo1 :
True

end Declaration

section TermApp

-- additional indentation of argument
/--
warning: too few spaces, which should be at least 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check Nat.add 1
1

/-
it can also be based on the last indentation of ancestors, if it doesn't have its indentation -- if
it isn't the first token in its line.
-/
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check Nat.add 1 <|
  Nat.add 2 <| Nat.add 3 <| Nat.add 4
  5 -- here it should be at least 2 + the indentation of `Nat.add 2`

/-- -/
#guard_msgs in
#check Nat.add 1 <|
  Nat.add 2 <| Nat.add 3 <| Nat.add 4
    5

/-
When it doesn't have a direct indentation, the indentation of children has a lower limit, but not a
upper limit.
-/
/-- -/
#guard_msgs in
#check Nat.add 1 <|
  Nat.add 2 <| Nat.add 3 <| Nat.add 4
      5 -- indented by 6 spaces

/- with parentheses -/
#guard_msgs in
#check Nat.add 1 <|
  Nat.add 2 <| Nat.add 3 <| Nat.add 4 (1 +
    1
  ) -- here it should be at least 2 + the indentation of `Nat.add 2`

end TermApp

section By

/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  by
  exact 1

/--
warning: too many spaces, which should be at most 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  by
      exact 1

/-- -/
#guard_msgs in
#check
  by
    exact 1

/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  ¬ by
  exact False

/-- -/
#guard_msgs in
#check
  ¬ by
    exact False

/-
When it doesn't have a direct indentation, the indentation of children has a lower limit, but not a
upper limit.
-/
/-- -/
#guard_msgs in
#check
  ¬ by
      exact False

end By

section Brackets

/-
allow the right bracket to ignore the additional indentation, if the left bracket isn't the first
token of a line.
-/
/-- -/
#guard_msgs in
#check
  Nat.add 1 (
    1
  )

/-
The right bracket can also follow the additional indentation.
-/
/-- -/
#guard_msgs in
#check
  Nat.add 1 (
      1
    )

/-
The right bracket should not have a deeper indentation than content bracketed.
-/
/--
warning: too many spaces, which should be at most 6
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  Nat.add 1 (
      1
        )

/--
warning: too few spaces, which should be at least 2
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  Nat.add 1 (
    1
)

-- TODO: can the right bracket have the same indentation with bracketed content?
-- #check
--   Nat.add 1 (
--     1
--     )

/-- -/
#guard_msgs in
#check
  Nat.add 1
    (
      1 + 1
    )

/-
If the left bracket is the first token in its line, it should follow the additional indentation if
that is set
-/
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check
  Nat.add 1
  (
    1 + 1
  )

/-
the content should have deeper indentation than the left bracket, it the left bracket is on its own
line.
-/
/--
warning: too few spaces, which should be at least 4
Note: This linter can be disabled with `set_option linter.indentation false`
-/
#guard_msgs in
#check Nat.add 1
  (
  1
  )

-- TODO: should this be allowed?
-- #check
--   Nat.add 1
--     (1 +
--     1
--     )

-- TODO: should 1 space indentation step be allowed in `⟨...⟩`?
/-- -/
#guard_msgs in
#check show Prod Nat Nat from
  ⟨
   1,
   1
  ⟩

/-- -/
#guard_msgs in
#check show Prod Nat Nat from
  ⟨
    1,
    1
  ⟩

-- TODO: is mixing 1 space and 2 spaces be allowed?
-- #guard_msgs in
-- #check show Fin 3 from
--   ⟨
--    1, -- 1 space
--    by
--      simp -- 2 spaces
--   ⟩

-- TODO:
-- /-- -/
-- #guard_msgs in
-- #check show Fin 2 from
--   id
--   -- other kinds of syntax should be indented with 2 spaces additional indentation
--   -- is `⟨` an exception?
--    ⟨
--     1,
--     by simp
--    ⟩

-- TODOs

end Brackets
