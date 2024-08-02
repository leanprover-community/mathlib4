import Mathlib.Tactic.ExtractLets

example (h : let x := 1; x = x) : True := by
  extract_lets y at h
  fail_if_success extract_lets a at h
  extract_lets at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y
  trivial

example : True := by
  let h : (let x := 1; x = x) := rfl
  extract_lets y at h
  guard_hyp y : Nat := 1
  guard_hyp h :ₛ y = y := rfl
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets x y at h
  guard_hyp x : Nat := 1
  guard_hyp y : Nat := 2
  guard_hyp h :ₛ x + 1 = y
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets at h
  rename_i a b
  guard_hyp a : Nat := 1
  guard_hyp b : Nat := 2
  guard_hyp h :ₛ a + 1 = b
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : True := by
  extract_lets x at h
  intros
  guard_hyp x : Nat := 1
  guard_hyp h :ₛ let y := 2; x + 1 = y
  trivial

example (h : let x := 1; let y := 2; x + 1 = y) : let _z := 3; ∀ (_ : Nat), True := by
  extract_lets at *
  guard_hyp h : _ + 1 = _
  fail_if_success extract_lets x at h
  guard_target =ₛ ∀ (_ : Nat), True
  intro
  trivial

-- extract local defs from goal and hyp.
example (h : let x := 1; let y := 2; x + 1 = y) :
    let _z := 3
    let _z₂ := 5
    ∀ (_ : Nat), True := by
  extract_lets at h ⊢
  guard_hyp h : _ + 1 = _
  fail_if_success extract_lets x at h
  guard_target =ₛ ∀ (_ : Nat), True
  intro
  trivial

-- extract local defs from goal only
example (h : let x := 1; let y := 2; x + 1 = y) :
    let _z := 3
    let _z₂ := 5
    ∀ (_ : Nat), True := by
  extract_lets
  fail_if_success extract_lets x
  guard_hyp h : let x := 1; let y := 2; x + 1 = y
  guard_target =ₛ ∀ (_ : Nat), True
  intro
  trivial

-- naming new local def
example (h : let x := 1; let y := 2; x + 1 = y) : let _z := 3; ∀ (_ : Nat), True := by
  extract_lets u
  guard_hyp u : Nat := 3
  fail_if_success extract_lets x
  guard_target =ₛ ∀ (_ : Nat), True
  guard_hyp h : let x := 1; let y := 2; x + 1 = y
  intro
  trivial

/-!
Issue reported at https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60extract_lets.60.20fails.20in.20a.20hypothesis.20if.20the.20name.20is.20unused/near/439675718
Unused 'let' bindings were being miscounted.
-/

/--
info: ok✝ : Prop := True
_also_ok✝ : Prop := True
_not_ok✝ : Prop := True
h : ok✝
⊢ True
-/
#guard_msgs in
def a (h : let ok := True; let _not_ok := True; ok) : let _also_ok := True; True := by
  extract_lets _ at h
  extract_lets _
  extract_lets _ at h
  trace_state
  trivial
