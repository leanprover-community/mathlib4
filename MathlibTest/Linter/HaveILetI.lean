import Mathlib.Tactic.Linter.HaveILetI

set_option linter.style.haveILetI true

/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'let' instead:
  letI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  letI : Inhabited Nat := ⟨0⟩
  trivial

-- Other forms of the `haveI`/`letI` declaration are flagged too: a named hypothesis...
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI h : 0 < 1 := Nat.one_pos
  trivial

-- ... and the bare anonymous form.
/--
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'let' instead:
  letI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  letI := (⟨0⟩ : Inhabited Nat)
  trivial

-- The suggested replacements are legal in exactly the same positions, including the
-- anonymous forms.
#guard_msgs in
example : True := by
  have : Inhabited Nat := ⟨0⟩
  have h : 0 < 1 := Nat.one_pos
  let : Inhabited Bool := ⟨true⟩
  let := (⟨0⟩ : Inhabited Nat)
  trivial

-- `haveI`/`letI` with a data goal are not flagged, for instance in the body of a `def`.
#guard_msgs in
def zero : Nat := by
  haveI : Inhabited Nat := ⟨0⟩
  letI : Inhabited Bool := ⟨true⟩
  exact 0

-- A tactic block constructing *data* inside the proof of a proposition is not flagged:
-- the goal of the inner `haveI` is `Nat → Nat`, not a proposition.
#guard_msgs in
example : True := by
  let f : Nat → Nat := by
    haveI : Inhabited Nat := ⟨0⟩
    exact id
  trivial

-- Conversely, a tactic proof of a *proposition* inside the body of a `def` is flagged.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
def oneAsSubtype : {n : Nat // 0 < n} :=
  ⟨1, by haveI : Inhabited Nat := ⟨0⟩; exact Nat.one_pos⟩

-- Instances of `Prop`-valued classes are proofs of propositions, so they are flagged too.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : Subsingleton PUnit := by
  haveI : Inhabited Nat := ⟨0⟩
  exact ⟨fun _ _ => rfl⟩

-- The term-mode `haveI`/`letI` are flagged when the term being constructed is a proof
-- of a proposition.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True :=
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'let' instead:
  letI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True :=
  letI : Inhabited Nat := ⟨0⟩
  trivial

-- Term-mode uses nested inside tactics are flagged too...
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  exact haveI : Inhabited Nat := ⟨0⟩; trivial

-- ... including inside an anonymous constructor under `refine`.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ⟨haveI : Inhabited Nat := ⟨0⟩; trivial, trivial⟩

-- Nested term-mode uses are each flagged once.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
---
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'let' instead:
  letI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True :=
  haveI : Inhabited Nat := ⟨0⟩
  letI : Inhabited Bool := ⟨true⟩
  trivial

-- A term-mode `haveI` constructing *data* is not flagged.
#guard_msgs in
def zero' : Nat :=
  haveI : Inhabited Nat := ⟨0⟩
  0

-- A term-mode `haveI` in a *statement* is not flagged: there the term being constructed is
-- the proposition itself, not a proof of it, and replacing `haveI` (which inlines, leaving
-- the statement literally `True`) with `have` would change the statement.
#guard_msgs in
example : (haveI : Inhabited Nat := ⟨0⟩; True) := trivial

#guard_msgs in
/-- A tactic macro producing a `haveI`, to check that the linter only flags syntax that
the user actually wrote. Note that the `haveI` inside the quotation is not flagged either:
no elaboration information is ever recorded for it. -/
macro "aux_haveI" : tactic => `(tactic| haveI : Inhabited Nat := ⟨0⟩)

-- Macro-generated `haveI` is not flagged.
#guard_msgs in
example : True := by
  aux_haveI
  trivial

-- Several `haveI`/`letI` in one proof are each flagged once.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
---
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'let' instead:
  letI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  letI : Inhabited Bool := ⟨true⟩
  trivial

-- A `haveI` that is run on several (propositional) goals by a combinator is only
-- reported once.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ⟨?_, ?_⟩ <;> haveI : Inhabited Nat := ⟨0⟩ <;> trivial

-- ... and the same holds for `all_goals`.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True ∧ True := by
  constructor
  all_goals haveI : Inhabited Nat := ⟨0⟩
  all_goals trivial

-- With mixed goals, a combinator-run `haveI` is *not* flagged: the single suggested source
-- replacement would also affect the run against the data goal, where `haveI` and `have`
-- produce different terms.
#guard_msgs in
example : PProd Nat True := by
  constructor <;> haveI : Inhabited Nat := ⟨0⟩
  · exact 0
  · trivial

-- The mirror image with the propositional goal *first* is not flagged either: the linter
-- must inspect all recorded runs before concluding, not stop at the first `Prop` one.
#guard_msgs in
example : PProd True Nat := by
  constructor <;> haveI : Inhabited Nat := ⟨0⟩
  · trivial
  · exact 0

universe u

/-- An auxiliary lemma whose first explicit argument has a fully implicit type. -/
theorem auxSortTrue : ∀ {α : Sort u}, α → True → True := fun _ h => h

-- The mixed-goal check is robust to the data goal's type being an unresolved metavariable
-- while the `haveI` runs: here it is only the later `exact (0 : Nat)` that determines the
-- first goal's type, so the linter must consult the final metavariable context to see that
-- this run was against data.
#guard_msgs in
example : True := by
  apply auxSortTrue <;> haveI : Inhabited Nat := ⟨0⟩
  · exact (0 : Nat)
  · trivial

/-- An auxiliary definition extracting data from a term with a fully implicit type. -/
def auxSortData : ∀ {α : Sort u}, α → 0 < 1 → Nat := fun _ _ => 5

-- ... and not flagging the above matters: in this variant, applying the suggested
-- replacement would change the body of the (data!) definition from `auxSortData 37 ⋯` to
-- `auxSortData (have this : Inhabited Nat := ⟨0⟩; 37) ⋯`.
#guard_msgs in
def dataFromMixed : Nat := by
  apply auxSortData <;> haveI : Inhabited Nat := ⟨0⟩
  · exact (37 : Nat)
  · exact Nat.one_pos

/-- An auxiliary lemma for creating a goal whose type is an unassigned metavariable. -/
theorem auxLaterTrue.{v} {α : Sort v} (a : α) (f : α → True) : True := f a

-- Conversely, a goal whose type is an unresolved metavariable at `haveI`-time *is* flagged
-- when the final metavariable context reveals it to be a proposition: below, `?α := True`
-- is only forced by the later `case f`.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  refine @auxLaterTrue ?α ?a ?f
  case a => haveI : Inhabited Nat := ⟨0⟩; exact trivial
  case f => exact id

-- A goal whose type is a bare metavariable of sort `Prop` is flagged: a *positive*
-- `Meta.isProp` answer is trusted even in the presence of metavariables.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : ∃ p : Prop, p := by
  constructor
  case h => haveI : Inhabited Nat := ⟨0⟩; exact trivial

-- A goal `α` with `α : Sort ?u` is indeterminate at `haveI`-time (a negative `Meta.isProp`
-- answer is *not* trusted, since the metavariable is hidden in the sort); it is flagged
-- once the final metavariable context resolves `?u := 0`, as forced by `_check` below.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True :=
  let F := fun (α : Sort _) (a : α) => (by haveI : Inhabited Nat := ⟨0⟩; exact a : α)
  let _check : ∀ (α : Prop), α → α := by exact F
  trivial

-- A term with no expected type at all is still flagged, via the type of the elaborated
-- term itself.
/--
info: trivial : True
---
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
#check (haveI : Inhabited Nat := ⟨0⟩; trivial)

-- `theorem` and `instance` commands, whose bodies may be elaborated asynchronously, are
-- linted like `example`s.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
theorem trivialTheorem : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
instance subsingletonInstance : Subsingleton PUnit := by
  haveI : Inhabited Nat := ⟨0⟩
  exact ⟨fun _ _ => rfl⟩

-- Within a single command, each `haveI`/`letI` is judged independently: here only the
-- second one (with a propositional goal) is flagged, not the first (which constructs
-- data).
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  let f : Nat → Nat := by
    haveI : Inhabited Bool := ⟨true⟩
    exact id
  haveI : Inhabited Nat := ⟨0⟩
  trivial

-- A hole in the value produces an extra (data) goal *after* the `haveI` runs; the goal of
-- the `haveI` itself is still the proposition, so it is flagged.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨?_⟩
  · trivial
  exact 0

-- `have` and `let` themselves are of course not flagged.
#guard_msgs in
example : True := by
  have : Inhabited Nat := ⟨0⟩
  let _i : Inhabited Bool := ⟨true⟩
  trivial

-- With the linter explicitly disabled, nothing is flagged, and scoped `set_option`
-- re-enabling works. (The linter is also off by default.)
set_option linter.style.haveILetI false

#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference.

Hint: Use 'have' instead:
  haveI̵

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
set_option linter.style.haveILetI true in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial
