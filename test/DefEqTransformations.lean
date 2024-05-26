import Mathlib.Tactic.DefEqTransformations
import Mathlib.Init.Logic

set_option autoImplicit true

private axiom test_sorry : ∀ {α}, α
namespace Tests

example : id (1 = 1) := by
  with_reducible whnf
  guard_target =ₛ id (1 = 1)
  whnf
  guard_target =ₛ 1 = 1
  rfl

example : (fun x => 1 + x) 1 = 2 := by
  beta_reduce
  guard_target =ₛ 1 + 1 = 2
  rfl

example : (fun x => 1 + x) 2 = (fun y => 2 + y) 3 := by
  conv =>
    lhs
    beta_reduce
    guard_target =ₛ 1 + 2
  guard_target =ₛ 1 + 2 = (fun y => 2 + y) 3
  exact test_sorry

example : 1 + 2 * 3 = 7 := by
  reduce
  guard_target =ₛ nat_lit 7 = nat_lit 7
  rfl

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  unfold_let x
  guard_target =ₛ 1 + y = y + 1
  let z := 3
  have h : z - 3 = 0 := rfl
  unfold_let z at h
  guard_hyp h :ₛ 3 - 3 = 0
  unfold_let y
  guard_target =ₛ 1 + 2 = 2 + 1
  rfl

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  unfold_let x y
  guard_target =ₛ 1 + 2 = 2 + 1
  rfl

example : let x := 1; let y := 2; x + y = y + x := by
  intro x y
  unfold_let
  guard_target =ₛ 1 + 2 = 2 + 1
  rfl

example : let x := 1; let y := 2 + x; y = 3 := by
  intro x y
  unfold_let x
  guard_target =ₛ y = 3
  unfold_let y
  guard_target =ₛ 2 + x = 3
  unfold_let x
  guard_target =ₛ 2 + 1 = 3
  rfl

example : let x := 1; let y := 2 + x; y = 3 := by
  intro x y
  unfold_let x y
  guard_target =ₛ 2 + 1 = 3
  rfl

/-!
Do not reorder hypotheses. (`unfold_let` makes a change)
-/
example : let ty := Int; ty → Nat → Nat := by
  intro _ a a
  unfold_let at *
  exact a

/-!
Do not reorder hypotheses. (`unfold_let` does not make a change)
-/
set_option linter.unusedVariables false in
example (a : Int) (a : Nat) : Nat := by
  unfold_let at *
  exact a

example : 1 + 2 = 2 + 1 := by
  unfold_projs
  guard_target =ₛ Nat.add (nat_lit 1) (nat_lit 2) = Nat.add (nat_lit 2) (nat_lit 1)
  rfl

example (m n : Nat) : (m == n) = true := by
  unfold_projs
  guard_target =ₛ Nat.beq m n = true
  exact test_sorry

example {α : Type u} (f : α → α) (a : α) :
    (fun x => (fun x => f x) x) a = f a := by
  eta_reduce
  guard_target =ₛ f a = f a
  rfl

example (f : Nat → Nat) : (fun a => f a) = (fun a => f (f a)) := by
  eta_expand
  guard_target =ₛ (fun a => f a) = (fun a => f (f a))
  eta_reduce
  guard_target =ₛ f = fun a => f (f a)
  eta_expand
  guard_target =ₛ (fun a => f a) = (fun a => f (f a))
  exact test_sorry

example : (fun (a b : Nat) => a + b) = (· + ·) := by
  eta_reduce
  guard_target =ₛ (HAdd.hAdd : Nat → Nat → Nat) = HAdd.hAdd
  eta_expand
  guard_target =ₛ (fun (a b : Nat) => a + b) = fun a b => a + b
  rfl

example : (fun (a : Nat) => 1 + a) = (1 + ·) := by
  eta_reduce
  guard_target =ₛ (HAdd.hAdd 1) = HAdd.hAdd 1
  eta_expand
  guard_target =ₛ (fun a ↦ 1 + a) = fun a ↦ 1 + a
  rfl

example (f : Nat → Nat → Nat) : (fun x => f 1 x) 2 = 3 := by
  eta_expand
  guard_target =ₛ f 1 2 = 3
  exact test_sorry

example : (fun (a : Nat) => 1 + a) 2 = (1 + ·) 2 := by
  eta_expand
  guard_target =ₛ 1 + 2 = 1 + 2
  rfl

example (p : Nat × Nat) : (p.1, p.2) = (p.2, p.1) := by
  eta_struct
  guard_target =ₛ p = (p.2, p.1)
  exact test_sorry

example (p : Nat × Nat) : ((p.1, p.2).1, (p.1, p.2).2) = ((p.1, p.2).2, (p.1, p.2).1) := by
  eta_struct
  guard_target =ₛ p = (p.2, p.1)
  exact test_sorry

example (n : Fin 5) : n = ⟨n.1, n.2⟩ := by
  eta_struct
  guard_target =ₛ n = n
  rfl

abbrev _root_.Fin.val2 : Fin n → Nat := Fin.val
abbrev _root_.Fin.prop2 (x : Fin n) : (x : Nat) < n := x.isLt

example (n : Fin 5) : n = ⟨n.val2, n.prop2⟩ := by
  eta_struct
  guard_target =ₛ n = n
  rfl
