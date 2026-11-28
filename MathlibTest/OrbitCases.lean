import Mathlib.Tactic.OrbitCases
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Action.End

set_option linter.unreachableTactic false

/-! Goals are checked with `guard_target`/`guard_hyp` rather than `#guard_msgs`: the latter does
not reliably capture messages logged after an `evalExpr` (as `orbit_cases` does). -/

/-! The whole group, enumerated: `Equiv.Perm Bool` has one orbit on `Bool`. -/

example (S : Bool → Prop) (h : ∀ b, S b) (b : Bool) : S b := by
  orbit_cases b using Equiv.Perm Bool with
  | inv =>
    guard_target = ∀ (g : Equiv.Perm Bool) (x : Bool), S x → S (g • x)
    exact fun _ _ _ ↦ h _
  | _ => exact h _

/-! `generated_by?` leaves the same goals as without it, and suggests generators. -/

example (S : Bool → Prop) (h : ∀ b, S b) (b : Bool) : S b := by
  orbit_cases b using Equiv.Perm Bool generated_by? with
  | inv => exact fun _ _ _ ↦ h _
  | _ => exact h _

/-! A pattern in local hypotheses: they are replaced by the projections of a variable, and what
depends on them is carried along. -/

example (S : Bool → Prop) (h : ∀ y₁ y₂, S y₁ → S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂) :
    ∀ y₁, S y₁ → ∀ y₂, S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂ := by
  intro y₁ hy₁ y₂ hy₂
  orbit_cases hys : (y₁, y₂) using Equiv.Perm (Bool × Bool)
      generated_by [Equiv.prodComm Bool Bool] with
  | inv =>
    guard_target = ∀ g ∈ [Equiv.prodComm Bool Bool], ∀ (x : Bool × Bool),
      (S x.1 → S x.2 → x.1 = x.2 ∨ x.1 ≠ x.2) →
        S (g • x).1 → S (g • x).2 → (g • x).1 = (g • x).2 ∨ (g • x).1 ≠ (g • x).2
    exact fun _ _ _ _ ↦ h _ _
  | rep (true, false) =>
    guard_hyp hys : (y₁, y₂) = (true, false)
    guard_hyp hy₁ : S y₁
    guard_target = y₁ = y₂ ∨ y₁ ≠ y₂
    exact h _ _ hy₁ hy₂
  | _ => exact h _ _ hy₁ hy₂

example (S : Bool → Prop) (h : ∀ y₁ y₂, S y₁ → S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂) :
    ∀ y₁, S y₁ → ∀ y₂, S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂ := by
  intro y₁ hy₁ y₂ hy₂
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool)
      generated_by [Equiv.prodComm Bool Bool] with
  | inv => exact fun _ _ _ _ ↦ h _ _
  | rep (true, false) =>
    guard_hyp hy₁ : S true
    guard_target = true = false ∨ true ≠ false
    exact h _ _ hy₁ hy₂
  | _ => exact h _ _ hy₁ hy₂

/-- The representatives are reduced by `dsimp only`: `Fin`'s product enumeration lists
`((fun i => i) ⟨0, ⋯⟩, (fun i => i) ⟨1, ⋯⟩)`. -/
example (S : Fin 3 → Prop) (h : ∀ y₁ y₂, S y₁ → S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂) :
    ∀ y₁, S y₁ → ∀ y₂, S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂ := by
  intro y₁ hy₁ y₂ hy₂
  orbit_cases hys : (y₁, y₂) using Equiv.Perm (Fin 3 × Fin 3)
      generated_by [Equiv.prodComm (Fin 3) (Fin 3)] with
  | inv => exact fun _ _ _ _ ↦ h _ _
  | rep_1 =>
    guard_hyp hys :ₛ (y₁, y₂) = (0, 1)
    exact h _ _ hy₁ hy₂
  | _ => exact h _ _ hy₁ hy₂

/-- `let` variables in the group and the generators are unfolded for the computation, but kept in
the goals. -/
example (S : Bool → Prop) (h : ∀ y₁ y₂, S y₁ → S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂) (y₁ y₂ : Bool)
    (hy₁ : S y₁) (hy₂ : S y₂) : y₁ = y₂ ∨ y₁ ≠ y₂ := by
  let β := Bool × Bool
  let π : Equiv.Perm β := Equiv.prodComm Bool Bool
  orbit_cases (y₁, y₂) using Equiv.Perm β generated_by [π] with
  | inv =>
    guard_target = ∀ g ∈ [π], ∀ (x : Bool × Bool),
      (S x.1 → S x.2 → x.1 = x.2 ∨ x.1 ≠ x.2) →
        S (g • x).1 → S (g • x).2 → (g • x).1 = (g • x).2 ∨ (g • x).1 ≠ (g • x).2
    exact fun _ _ _ _ ↦ h _ _
  | rep (true, false) => exact h _ _ hy₁ hy₂
  | _ => exact h _ _ hy₁ hy₂

/-- error: orbit_cases: the action of
  Equiv.Perm (Bool × Bool)
on
  Bool × Bool
and the generators [π]
must not depend on local hypotheses (other than `let` variables) or metavariables -/
#guard_msgs in
example (S : Bool → Prop) (y₁ y₂ : Bool) (π : Equiv.Perm (Bool × Bool)) : S y₁ := by
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool) generated_by [π]

/-! A term with blanks is a pattern: `rep t` names every representative that `t` unifies with,
except those taken by earlier alternatives. -/

example (S : Bool → Prop) (h : ∀ y₁ y₂, S y₁ → S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂) :
    ∀ y₁, S y₁ → ∀ y₂, S y₂ → y₁ = y₂ ∨ y₁ ≠ y₂ := by
  intro y₁ hy₁ y₂ hy₂
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool) generated_by [Equiv.prodComm Bool Bool] with
  | inv => exact fun _ _ _ _ ↦ h _ _
  -- `(true, true)` and `(true, false)`
  | rep (true, _) =>
    guard_hyp hy₁ : S true
    exact h _ _ hy₁ hy₂
  -- only `(false, false)` is left
  | rep (_, _) =>
    guard_hyp hy₁ : S false
    guard_hyp hy₂ : S false
    exact h _ _ hy₁ hy₂

/-- error: orbit_cases: redundant alternative (earlier alternatives take all that it matches) -/
#guard_msgs in
example (S : Bool → Prop) (y₁ y₂ : Bool) : S y₁ := by
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool) generated_by [Equiv.prodComm Bool Bool] with
  | rep (_, _) => sorry
  | rep (true, false) => sorry

/-! As for `induction`, the variables of the target cannot be named by `generalizing`, and what
depends on them need not be. -/

/-- error: Variable `y₂` cannot be generalized because the `orbit_cases` target depends on it -/
#guard_msgs in
example (S : Bool → Prop) (y₁ y₂ : Bool) : S y₁ := by
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool) generated_by [Equiv.prodComm Bool Bool]
    generalizing y₂

/--
error: Unnecessary `generalizing` argument: Variable `hy₁` is generalized automatically
---
error: unsolved goals
case inv
S : Bool → Prop
⊢ ∀ g ∈ [Equiv.prodComm Bool Bool], ∀ (x : Bool × Bool), (S x.1 → S x.1) → S (g • x).1 → S (g • x).1
-/
#guard_msgs in
example (S : Bool → Prop) (y₁ y₂ : Bool) (hy₁ : S y₁) : S y₁ := by
  orbit_cases (y₁, y₂) using Equiv.Perm (Bool × Bool) generated_by [Equiv.prodComm Bool Bool]
    generalizing hy₁ with
  | rep_0 | rep_1 | rep_2 => exact hy₁
