import Mathlib.Tactic.Subsingleton

private axiom test_sorry : ∀ {α}, α

/-!
Basic subsingleton instances
-/
example (x y : Unit) : x = y := by subsingleton

example (x y : Empty) : x = y := by subsingleton

example {α : Type} [Subsingleton α] (x y : α) : x = y := by subsingleton

/-!
Proof irrelevance
-/

example (p : Prop) (h h' : p) : h = h' := by subsingleton

/-!
HEq proof irrelevance
-/
example (p q : Prop) (h : p) (h' : q) : HEq h h' := by subsingleton

/-!
Does intros.
-/
example : ∀ {α : Type} [Subsingleton α] (x y : α), x = y := by subsingleton

/-!
Does intros, and turns HEq into Eq if possible.
-/
example : ∀ {α : Type} [Subsingleton α] (x y : α), HEq x y := by subsingleton

section AvoidSurprise

/--
error: tactic 'subsingleton' could not prove equality since it could not synthesize
  Subsingleton α
-/
#guard_msgs in
example (α : Sort _) (x y : α) : x = y := by subsingleton

example (α : Sort _) (x y : α) : x = y := by apply Subsingleton.elim

end AvoidSurprise

/-!
Handles `BEq` instances if there are `LawfulBEq` instances for each.
-/
example (α : Type) (inst1 inst2 : BEq α) [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  subsingleton

/-!
Using `subsingleton` to turn a `HEq` into an `Eq` of the underlying types.
-/
example (p q : Prop) (h : p = q) (instp : Decidable p) (instq : Decidable q) :
    HEq instp instq := by
  subsingleton
  guard_target =ₛ Decidable p = Decidable q
  exact congrArg Decidable h

/-!
Can't apply `Subsingleton.helim`
-/
/--
error: tactic 'subsingleton' could not synthesize either
  Subsingleton α
or
  Subsingleton β
to make progress on `HEq` goal using `Subsingleton.helim`
-/
#guard_msgs in
example (α β : Type) (x : α) (y : β) : HEq x y := by
  subsingleton

/-!
`Subsingleton.helim` with left argument
-/
example (α β : Type) (h : α = β) [Subsingleton α] (x : α) (y : β) : HEq x y := by
  subsingleton
  guard_target =ₛ α = β
  exact h

/-!
`Subsingleton.helim` with right argument
-/
example (α β : Type) (h : α = β) [Subsingleton β] (x : α) (y : β) : HEq x y := by
  subsingleton
  guard_target =ₛ α = β
  exact h

/-!
`subsingleton` suggests `rfl` when it fails
-/
/-- info: Try this: rfl -/
#guard_msgs in
example : 1 + 1 = 2 := by
  subsingleton

/-!
`subsingleton` does not itself try `rfl` if it's not in error recovery mode
-/
example : 1 + 1 = 2 := by
  try subsingleton
  guard_target =ₛ 1 + 1 = 2
  rfl

/-- info: Try this: (intros; rfl) -/
#guard_msgs in
example : ∀ (n : Nat), n = n := by
  subsingleton

/-!
Passing subsingleton instances to the tactic.
-/
example {α : Type} (x y : α) : x = y := by
  subsingleton [(test_sorry : Subsingleton α)]

/-!
No linting yet for unused instances.
-/
#guard_msgs in
example {α : Type} (x y : α) : x = y := by
  subsingleton [(test_sorry : Subsingleton α), (test_sorry : Subsingleton α)]

/-!
Abstraction, with specified universe levels.
-/
example {α : Type} (x y : α) : x = y := by
  subsingleton [(test_sorry : Subsingleton.{1} _)]

/-!
Abstraction, with unspecified universe levels.
-/
#guard_msgs in
example {α : Type} (x y : α) : x = y := by
  subsingleton [(test_sorry : Subsingleton _)]

/-!
Not an instance.
-/
/--
error: Not an instance. Term has type
  Bool
-/
#guard_msgs in
example {α : Type} (x y : α) : x = y := by
  subsingleton [true]

/-!
When abstracting, metavariables become instance implicit if they're for classes.
-/
example {α : Type} [BEq α] (f : BEq α → Subsingleton α) (x y : α) : x = y := by
  subsingleton [f _]

/-!
This too abstracts some metavariables and ensures that `BEq` is instance implicit.
-/
example {α : Type} [BEq α] (f : ∀ {β : Type} [BEq β], Subsingleton β) (x y : α) : x = y := by
  subsingleton [f]

/-!
The same, but now there's a universe level metavariable.
-/
def fdef : ∀ {β : Type _} [BEq β], Subsingleton β := test_sorry

example {α : Type} [BEq α] (x y : α) : x = y := by
  subsingleton [fdef]
