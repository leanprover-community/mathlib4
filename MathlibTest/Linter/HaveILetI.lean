import Mathlib.Tactic.Linter.HaveILetI

set_option linter.style.haveILetI true

/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'let' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  letI : Inhabited Nat := ⟨0⟩
  trivial

-- Other forms of the `haveI`/`letI` declaration are flagged too: a named hypothesis...
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI h : 0 < 1 := Nat.one_pos
  trivial

-- ... and the bare anonymous form.
/--
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'let' instead.

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
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
def oneAsSubtype : {n : Nat // 0 < n} :=
  ⟨1, by haveI : Inhabited Nat := ⟨0⟩; exact Nat.one_pos⟩

-- Instances of `Prop`-valued classes are proofs of propositions, so they are flagged too.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : Subsingleton PUnit := by
  haveI : Inhabited Nat := ⟨0⟩
  exact ⟨fun _ _ => rfl⟩

-- The term-mode `haveI`/`letI` are not (yet) linted.
#guard_msgs in
example : True :=
  haveI : Inhabited Nat := ⟨0⟩
  trivial

#guard_msgs in
example : True :=
  letI : Inhabited Nat := ⟨0⟩
  trivial

/-- A tactic macro producing a `haveI`, to check that the linter only flags syntax that
the user actually wrote. -/
macro "aux_haveI" : tactic => `(tactic| haveI : Inhabited Nat := ⟨0⟩)

-- Macro-generated `haveI` is not flagged.
#guard_msgs in
example : True := by
  aux_haveI
  trivial

-- Several `haveI`/`letI` in one proof are each flagged once.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
---
warning: 'letI' only differs from 'let' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'let' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  letI : Inhabited Bool := ⟨true⟩
  trivial

-- A `haveI` that is run on several goals by a combinator is only reported once.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ⟨?_, ?_⟩ <;> haveI : Inhabited Nat := ⟨0⟩ <;> trivial

-- With mixed goals, a combinator-run `haveI` is reported (once) as long as at least one
-- of the goals it runs against is a proposition, even if a data goal comes first.
/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
example : PProd Nat True := by
  constructor <;> haveI : Inhabited Nat := ⟨0⟩
  · exact 0
  · trivial

-- `have` and `let` themselves are of course not flagged.
#guard_msgs in
example : True := by
  have : Inhabited Nat := ⟨0⟩
  let _i : Inhabited Bool := ⟨true⟩
  trivial

-- The linter is off by default, and scoped `set_option` enabling works.
set_option linter.style.haveILetI false

#guard_msgs in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial

/--
warning: 'haveI' only differs from 'have' in that it inlines its value into the proof term; in the proof of a proposition this makes no difference, so please use 'have' instead.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
-/
#guard_msgs in
set_option linter.style.haveILetI true in
example : True := by
  haveI : Inhabited Nat := ⟨0⟩
  trivial
