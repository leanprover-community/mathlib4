import Mathlib.Tactic.Congr!
import Std.Tactic.GuardExpr
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.List.Defs

theorem ex1 (a b c : Nat) (h : a = b) : a + c = b + c := by
  congr!

theorem ex2 (a b : Nat) (h : a = b) : ∀ c, a + c = b + c := by
  congr!

theorem ex3 (a b : Nat) (h : a = b) : (fun c => a + c) = (fun c => b + c) := by
  congr!

theorem ex4 (a b : Nat) : Fin (a + b) = Fin (b + a) := by
  congr! 1
  guard_target = a + b = b + a
  apply Nat.add_comm

theorem ex5 : ((a : Nat) → Fin (a + 1)) = ((a : Nat) → Fin (1 + a)) := by
  congr!  2
  rename_i a
  guard_target = a + 1 = 1 + a
  apply Nat.add_comm

theorem ex6 : ((a : Nat) × Fin (a + 1)) = ((a : Nat) × Fin (1 + a)) := by
  congr! 3
  rename_i a
  guard_target = a + 1 = 1 + a
  apply Nat.add_comm

theorem ex7 (p : Prop) (h1 h2 : p) : h1 = h2 := by
  congr!

theorem ex8 (p q : Prop) (h1 : p) (h2 : q) : HEq h1 h2 := by
  congr!

theorem ex9 (a b : Nat) (h : a = b) : a + 1 ≤ b + 1 := by
  congr!

theorem ex10 (x y : Unit) : x = y := by
  congr!

theorem ex11 (p q r : Nat → Prop) (h : q = r) : (∀ n, p n → q n) ↔ (∀ n, p n → r n) := by
  congr!

theorem ex12 (p q : Prop) (h : p ↔ q) : p = q := by
  congr!

theorem ex13 (x y : α) (h : x = y) (f : α → Nat) : f x = f y := by
  congr!

theorem ex14 {α : Type} (f : Nat → Nat) (h : ∀ x, f x = 0) (z : α) (hz : HEq z 0) :
    HEq f (fun (_ : α) => z) := by
  congr!
  · guard_target = Nat = α
    exact type_eq_of_heq hz.symm
  next n x _ =>
    guard_target = HEq (f n) z
    rw [h]
    exact hz.symm

def MySet (α : Type _) := α → Prop
def MySet.image (f : α → β) (s : MySet α) : MySet β := fun y => ∃ x, s x ∧ f x = y

-- Testing for equality between what are technically partially applied functions
example (s t : MySet α) (f g : α → β) (h1 : s = t) (h2 : f = g) :
    MySet.image f s = MySet.image g t := by
  congr!


example (c : Prop → Prop → Prop → Prop) (x x' y z z' : Prop)
    (h₀ : x ↔ x') (h₁ : z ↔ z') : c x y z ↔ c x' y z' := by
  congr!

example {α β γ δ} {F : ∀{α β}, (α → β) → γ → δ} {f g : α → β} {s : γ} (h : ∀ (x : α), f x = g x) :
    F f s = F g s := by
  congr!
  funext
  apply h

example {α β} {f : _ → β} {x y : {x : {x : α // x = x} // x = x} } (h : x.1 = y.1) :
    f x = f y := by
  congr! 1
  ext1
  exact h

example {α β} {F : _ → β} {f g : {f : α → β // f = f} }
    (h : ∀ x : α, (f : α → β) x = (g : α → β) x) :
    F f = F g := by
  congr!
  ext x
  apply h

example {ls : List ℕ} :
    ls.map (fun x => (ls.map (fun y => 1 + y)).sum + 1) =
      ls.map (fun x => (ls.map (fun y => Nat.succ y)).sum + 1) := by
  congr!
  rename_i y
  guard_target = 1 + y = y.succ
  rw [Nat.add_comm]

example {ls : List ℕ} {f g : ℕ → ℕ} {h : ∀ x, f x = g x} :
    ls.map (fun x => f x + 3) = ls.map (fun x => g x + 3) := by
  congr! 3 -- it's a little too powerful and will get to `f = g`
  rename_i x
  exact h x

-- succeed when either `ext` or `congr` can close the goal
example : () = () := by congr!
example : 0 = 0 := by congr!

example {α} (a : α) : a = a := by congr!

example {α} (a b : α) (h : false) : a = b := by
  fail_if_success { congr! }
  cases h
