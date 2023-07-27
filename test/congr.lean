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
  congr! 2 with a
  guard_target = a + 1 = 1 + a
  apply Nat.add_comm

theorem ex6 : ((a : Nat) × Fin (a + 1)) = ((a : Nat) × Fin (1 + a)) := by
  congr! 3 with a
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

theorem ex15 (p q : Nat → Prop) :
    (∀ ε > 0, p ε) ↔ ∀ ε > 0, q ε := by
  congr! 2 with ε hε
  guard_hyp hε : ε > 0
  guard_target = p ε ↔ q ε
  sorry

/-- Generating type equalities is OK if it's possible they're the same type. -/
example (s t : Set α) : (ℕ × Subtype s) = (ℕ × Subtype t) := by
  congr! 1
  guard_target = Subtype s = Subtype t
  congr! 1
  guard_target = s = t
  sorry

/-- Generating type equalities is not OK if they're not likely to be the same type. -/
example (s : Set α) (t : Set β) : (ℕ × Subtype s) = (ℕ × Subtype t) := by
  congr!
  guard_target = (ℕ × Subtype s) = (ℕ × Subtype t)
  sorry

/-- Congruence here is OK since `Fin m = Fin n` is plausible to prove. -/
example (m n : Nat) (h : m = n) (x : Fin m) (y : Fin n) : HEq (x + x) (y + y) := by
  congr!
  guard_target = HEq x y
  sorry
  guard_target = HEq x y
  sorry

/-- Props are types, but prop equalities are totally plausible. -/
example (p q r : Prop) : p ∧ q ↔ p ∧ r := by
  congr!
  guard_target = q ↔ r
  sorry

/-- Congruence here is not OK by default since `α = β` is not generally plausible. -/
example (α β) [inst1 : Add α] [inst2 : Add β] (x : α) (y : β) : HEq (x + x) (y + y) := by
  congr!
  guard_target = HEq (x + x) (y + y)
  -- But with typeEqs we can get it to generate the congruence anyway:
  have : α = β := sorry
  have : HEq inst1 inst2 := sorry
  congr! (config := { typeEqs := true })
  guard_target = HEq x y
  sorry
  guard_target = HEq x y
  sorry

example (prime : Nat → Prop) (n : Nat) :
    prime (2 * n + 1) = prime (n + n + 1) := by
  congr!
  · guard_target = (HMul.hMul : Nat → Nat → Nat) = HAdd.hAdd
    sorry
  · guard_target = 2 = n
    sorry

example (prime : Nat → Prop) (n : Nat) :
    prime (2 * n + 1) = prime (n + n + 1) := by
  congr! 2
  guard_target = 2 * n = n + n
  sorry

example (prime : Nat → Prop) (n : Nat) :
    prime (2 * n + 1) = prime (n + n + 1) := by
  congr! (config := .unfoldSameFun)
  guard_target = 2 * n = n + n
  sorry

opaque partiallyApplied (p : Prop) [Decidable p] : Nat → Nat

-- Partially applied dependent functions
example : partiallyApplied (True ∧ True) = partiallyApplied True := by
  congr!
  decide

inductive walk (α : Type) : α → α → Type
  | nil (n : α) : walk α n n

def walk.map (f : α → β) (w : walk α x y) : walk β (f x) (f y) :=
  match x, y, w with
  | _, _, .nil n => .nil (f n)

example (w : walk α x y) (w' : walk α x' y') (f : α → β) : HEq (w.map f) (w'.map f) := by
  congr!
  guard_target = x = x'
  sorry
  guard_target = y = y'
  sorry
  -- get x = y and y = y' in context for `HEq w w'` goal.
  have : x = x' := by assumption
  have : y = y' := by assumption
  guard_target = HEq w w'
  sorry

example (w : walk α x y) (w' : walk α x' y') (f : α → β) : HEq (w.map f) (w'.map f) := by
  congr! with rfl rfl
  guard_target = x = x'
  sorry
  guard_target = y = y'
  sorry
  guard_target = w = w'
  sorry

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
  congr! 6 with - y
  guard_target = 1 + y = y.succ
  rw [Nat.add_comm]

example {ls : List ℕ} {f g : ℕ → ℕ} {h : ∀ x, f x = g x} :
    ls.map (fun x => f x + 3) = ls.map (fun x => g x + 3) := by
  congr! 3 with x -- it's a little too powerful and will get to `f = g`
  exact h x

-- succeed when either `ext` or `congr` can close the goal
example : () = () := by congr!
example : 0 = 0 := by congr!

example {α} (a : α) : a = a := by congr!

example {α} (a b : α) (h : false) : a = b := by
  fail_if_success { congr! }
  cases h

def g (x : Nat) : Nat := x + 1

example (x y z : Nat) (h : x = z) (hy : y = 2) : 1 + x + y = g z + 2 := by
  congr!
  guard_target = HAdd.hAdd 1 = g
  funext
  simp [g, Nat.add_comm]

example (Fintype : Type → Type)
    (α β : Type) (inst : Fintype α) (inst' : Fintype β) : HEq inst inst' := by
  congr!
  guard_target = HEq inst inst'
  sorry

example (Fintype : Type → Type) [∀ γ, Subsingleton (Fintype γ)]
    (α β : Type) (inst : Fintype α) (inst' : Fintype β) : HEq inst inst' := by
  congr!
  guard_target = Fintype α = Fintype β
  congr! (config := { typeEqs := true })
  guard_target = α = β
  sorry

example : n = m → 3 + n = m + 3 := by
  congr! 0 with rfl
  guard_target = 3 + n = n + 3
  apply add_comm

example (x y x' y' : Nat) (hx : x = x') (hy : y = y') : x + y = x' + y' := by
  congr! (config := { closePre := false, closePost := false })
  exact hx
  exact hy

example (x y x' : Nat) (hx : id x = id x') : x + y = x' + y := by
  congr!

example (x y x' : Nat) (hx : id x = id x') : x + y = x' + y := by
  congr! (config := { closePost := false })
  exact hx

example : { f : Nat → Nat // f = id } :=
  ⟨?_, by
    -- prevents `rfl` from solving for `?m` in `?m = id`:
    congr! (config := { closePre := false, closePost := false })
    ext x
    exact Nat.zero_add x⟩

-- Regression test. From fixing a "declaration has metavariables" bug
example (h : z = y) : (x = y ∨ x = z) → x = y := by
  congr! with (rfl|rfl)
