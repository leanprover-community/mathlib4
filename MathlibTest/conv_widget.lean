import Mathlib.Tactic.Widget.Conv
import Lean.Elab.Tactic.ElabTerm

/-!
Instead of testing `conv?` directly, we test the `insertEnterSyntax` function.
This has the advantage of not having to run javascript in the tests,
and not having to invoke the parser.
-/

private axiom test_sorry.{u} {α : Sort u} : α

open Lean Meta Elab Tactic SubExpr

syntax "test" str ("at" ident)? : tactic

elab_rules : tactic
  | `(tactic| test%$stx $t:str $[at $h?:ident]?) =>
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let pos := Pos.fromString! t.getString
    let loc ← do
      match h? with
      | none => pure <| GoalLocation.target pos
      | some h => pure <| GoalLocation.hypType (← getFVarId h) pos
    let locs := #[{ mvarId := goal, loc := loc }]
    let conv ← Mathlib.Tactic.Conv.insertEnterSyntax locs goalType
    let insert ← conv.replaceM fun stx =>
      match stx with
      | `(Lean.Parser.Tactic.Conv.skip| skip) =>
        some <$> `(Lean.Parser.Tactic.Conv.convTrace_state| trace_state)
      | _ => pure none
    evalTactic insert
    let some range := (← getFileMap).lspRangeOfStx? stx | failure
    let interactive ← Lean.Widget.goalToInteractive goal
    let params : SelectInsertParams := {
      pos := range.start
      goals := #[interactive]
      selectedLocations := locs
      replaceRange := range
    }
    let (_, text, _) ← Mathlib.Tactic.Conv.insertEnter locs goalType params
    logInfo m!"`conv?` would output:\n{text}"

elab "mdata% " e:term : term => do
  let e ← Term.elabTerm e none
  return .mdata {} e

set_option linter.unusedVariables false

/--
info: `conv?` would output:
conv at h =>
    enter [1, 1]
    skip
---
trace: h : 1 + 2 = 5
| 1
-/
#guard_msgs in
example (h : 1 + 2 = 5) : id 3 = 4 := by
  -- go to `1`
  test "/0/1/0/1" at h
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 1, 2]
    skip
---
trace: | 3
-/
#guard_msgs in
example : (∀ (h : 7 < 3), [0, 1, 2][7] = 7) = True := by
  -- go to `3`
  test "/0/1/0/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, x, 5]
    skip
---
trace: case h
x : False
| true
-/
#guard_msgs in
example : (fun _ : False => id id id id id true) = (fun _ : False => false) := by
  -- go to `true`
  test "/0/1/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 0]
    skip
---
trace: s t : False → Bool
x : False
| s
-/
#guard_msgs in
example (s t : False → Bool) (x : False) : s x = t x := by
  -- go to `s`
  test "/0/1/0"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 0, x, 1]
    skip
---
trace: case h
x : Unit
| false
-/
#guard_msgs in
example : (fun _ : Unit => !false) () = true := by
  -- go to `false`
  test "/0/1/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [a]
    skip
---
trace: a : False
| True
-/
#guard_msgs in
example : False → True := by
  -- go to `True`
  test "/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 2, 1]
    skip
---
trace: | 4
-/
#guard_msgs in
example : 1 = Nat.log2 4 → False := by
  -- go to `4`
  test "/0/1/1"
  exact test_sorry

set_option pp.mvars.anonymous false in
/--
info: `conv?` would output:
conv =>
    enter [1, 1, 2]
    skip
---
trace: | False

⊢ Decidable (True ≠ ?_)
-/
#guard_msgs in
example : decide (True ≠ False) = decide True := by
  -- go to `False`
  test "/0/1/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, @2, @4]
    skip
---
trace: inst : Decidable (True ∧ False)
| instDecidableFalse
-/
#guard_msgs in
example (inst : Decidable (True ∧ False)) :
    (clear% inst; inferInstanceAs (Decidable (True ∧ False))) = inst := by
  -- go to `instDecidableFalse`
  test "/0/1/1/1"
  exact test_sorry

set_option pp.natLit true in
/--
info: `conv?` would output:
conv =>
    enter [1, 4, @3]
    skip
---
trace: | instOfNatNat (nat_lit 0)
-/
#guard_msgs in
example : #[].foldl Nat.gcd 17 = 17 := by
  -- go to `instOfNatNat (nat_lit 0)`
  test "/0/1/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv at c =>
    enter [1]
    skip
---
trace: a : Nat := 2
c : Fin a := 1
d : Fin ↑c := 0
b : Fin ↑c
| a
-/
#guard_msgs in
example : let a := 2; let c : Fin a := 1; let d : Fin c := (0 : Fin 1); ∀ b, b = d := by
  intro a c d b
  -- go to `a`
  test "/1" at c
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [a, b, c, 2]
    skip
---
trace: a : Nat
b c : Fin a
| c
-/
#guard_msgs in
example : let a := 1; ∀ (b c : Fin a), b = c := by
  -- go to `c`
  test "/2/1/1/1"
  exact test_sorry

set_option pp.proofs true in
/--
info: `conv?` would output:
conv =>
    enter [1, 2, 1, 2, 0]
    skip
---
trace: k : Nat
l : List Nat
h : ∃ h, k < l.length → l[k] = 0
| h.2
-/
#guard_msgs in
example (k : Nat) (l : List Nat) (h : ∃ (h : k < l.length), k < l.length → l[k] = 0) :
    Fin.mk (l[k]'h.1) ((congrArg (· < 1) (h.2 h.1)).mpr Nat.zero_lt_one) = 0 := by
  -- go to `h.2`
  test "/0/1/1/0/1/1/0"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    fun
    fun
    fun
    skip
---
trace: | id id (id id id)
-/
#guard_msgs in
example : id id (id id id) (id id (id id) id id (id (id id))) id (id (id (id id)) True) := by
  -- go to `id id (id id id)`
  test "/0/0/0"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [2, 1, 1]
    skip
---
trace: | 0
-/
#guard_msgs in
example : mdata% 1 = id 0 + 1 := by
  -- go to `0`
  test "/1/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [2, 1, 1]
    skip
---
trace: | 0
-/
#guard_msgs in
example : (mdata% Eq) 1 (id 0 + 1) := by
  -- go to `0`
  test "/1/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [0, 0]
    skip
---
trace: | @Eq
-/
#guard_msgs in
example : (mdata% Eq 1) (id 0 + 1) := by
  -- go to `@Eq`
  test "/0/0/0"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [2, @2]
    skip
---
trace: h : False → {x : True} → False → Bool
k : False
| trivial
-/
#guard_msgs in
example (h : False → mdata% ∀ {_ : True}, False → Bool) (k : False) : k.elim = @h k trivial k := by
  -- go to `trivial`
  test "/1/0/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 2, 2]
    skip
---
trace: f : ∀ {a : Nat} ⦃b : Nat⦄, optParam (0 < 1) Nat.zero_lt_one → ∀ (c : Nat), 1 < 0
| 17
-/
#guard_msgs in
example (f : ∀ {a : Nat} ⦃b : Nat⦄ (_ : 0 < 1 := Nat.zero_lt_one) (c : Nat), 1 < 0) :
    Fin.elim0.{1} ⟨1, @f 0 1 Nat.zero_lt_one 17⟩ := by
  -- go to `17`
  test "/1/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [k, 1, 1]
    skip
---
trace: k : Nat
| k
-/
#guard_msgs in
example : have k : Nat := 1; Subsingleton (Fin k) := by
  -- go to `k`
  test "/2/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv at h =>
    enter [n, 2, 1]
    skip
---
trace: f : Nat → Nat
h : ∀ (n : Nat), n ≠ f n - 1
n : Nat
| f n
-/
#guard_msgs in
example (f : Nat → Nat) (h : ∀ n, n ≠ f n - 1) : 1 < f 0 := by
  -- go to `f n`
  test "/1/1/0/1" at h
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 0, x0, x1, x2, 2]
    skip
---
trace: case h.h.h
x0 x1 x2 : Bool → Nat
| x2 true
-/
#guard_msgs in
example : (fun x0 x1 x2 : Bool → Nat => x0 true + x1 false + x2 true)
    (fun b => bif b then 0 else 1) (fun b => bif b then 3 else 2) (fun _ => 17) = 19 := by
  -- go to `x2 true`
  test "/0/1/0/0/0/1/1/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv =>
    enter [1, 1, @4, @2]
    skip
---
trace: | instAddNat
-/
#guard_msgs in
example : (3 + 3 = 6) = True := by
  -- go to `instAddNat`
  test "/0/1/0/1/0/0/1/1"
  exact test_sorry

/--
info: `conv?` would output:
conv at f =>
    enter [1, 1]
    skip
---
trace: m n : Nat
f : ∀ (a : Fin (m + n)), m = n
k : Fin (n + m)
| m + n
-/
#guard_msgs in
example {m n : Nat} (f : Fin (m + n) → m = n) (k : Fin (n + m)) : m = n := by
  -- go to `m + n`
  test "/0/1" at f
  exact test_sorry

/--
info: `conv?` would output:
conv at c =>
    enter [1]
    skip
---
trace: b : Nat := 1
c : Fin b := ⟨0, Nat.zero_lt_one⟩
| b
-/
#guard_msgs in
example : let b := 1; let c : Fin b := ⟨0, Nat.zero_lt_one⟩; b = c + 1 := by
  intro b c
  -- go to `b`
  test "/1" at c
  exact test_sorry
