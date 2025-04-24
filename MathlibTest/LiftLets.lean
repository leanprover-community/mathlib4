import Mathlib.Tactic.LiftLets

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true

example : (let x := 1; x) = 1 := by
  lift_lets
  guard_target =ₛ let x := 1; x = 1
  intro _x
  rfl

example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets
  guard_target =ₛ let x := 1; x = x
  intro _x
  rfl

example : (let x := 1; x) = (let y := 1; y) := by
  lift_lets (config := {merge := false})
  guard_target =ₛ let x := 1; let y := 1; x = y
  intros _x _y
  rfl

example : (let x := (let y := 1; y + 1); x + 1) = 3 := by
  lift_lets
  guard_target =ₛ let y := 1; let x := y + 1; x + 1 = 3
  intros _y _x
  rfl

example : (fun x => let a := x; let y := 1; a + y) 2 = 2 + 1 := by
  lift_lets
  guard_target =ₛ let y := 1; (fun x ↦ let a := x; a + y) 2 = 2 + 1
  intro _y
  rfl

example : (fun (_ : let ty := Nat; ty) => Nat) (2 : Nat) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (fun (_ : ty) ↦ Nat) (2 : Nat)
  exact 0

example : (fun (x : let ty := Nat; ty) => Fin x) (2 : Nat) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (fun (x : ty) ↦ Fin x) (2 : Nat)
  exact 0


example : (id : Nat → Nat) = (fun (x : let ty := Nat; ty) => x) := by
  lift_lets
  guard_target =ₛ let ty := Nat; (id: Nat → Nat) = fun (x : ty) ↦ x
  rfl

example : (x : let ty := Nat; ty) → let y := (1 : Nat); Fin (y + Nat.succ x) := by
  lift_lets
  guard_target =ₛ let ty := Nat; let y := 1; (x : ty) → Fin (y + Nat.succ x)
  intro ty y x
  rw [Nat.add_succ, Nat.succ_eq_add_one]
  exact 0

example : (x : Nat) → (y : Nat) → let z := x + 1; let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp [w, z]
  exact 0

example : (x : Nat) → let z := x + 1; (y : Nat) → let w := 3; Fin (z + w) := by
  lift_lets
  guard_target =ₛ let w := 3; (x : Nat) → let z := x + 1; Nat → Fin (z + w)
  intro w x z _y
  simp [w, z]
  exact 0

example : (let x := 1; x) = (let x := 1; x) := by
  lift_lets
  guard_target =ₛ let x := 1; x = x
  rfl

example : (let x := 2; x) = (let y := 1; y + 1) := by
  lift_lets
  guard_target =ₛ let x := 2; let y := 1; x = y + 1
  rfl

example (h : (let x := 1; x) = y) : True := by
  lift_lets at h
  guard_hyp h :ₛ let x := 1; x = y
  trivial

example (h : (let x := 1; x) = y) : True := by
  revert h
  lift_lets
  intro x h
  guard_hyp x : Nat := 1
  guard_hyp h :ₛ x = y
  trivial

example : let x := 1; ∀ n, let y := 1; x + n = y + n := by
  lift_lets
  guard_target =ₛ let x := 1; ∀ n, x + n = x + n
  intros x n
  rfl

example (m : Nat) (h : ∃ n, n + 1 = m) (x : Fin m) (y : Fin _) :
    cast (let h' := h.choose_spec.symm; congrArg Fin h') x = y := by
  lift_lets (config := {proofs := true})
  intro h'
  clear_value h'
  guard_hyp h' : m = Exists.choose h + 1
  exact test_sorry
