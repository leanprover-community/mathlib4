import Std.Tactic.GuardMsgs
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Lattice

section PiNotation
variable (P : Nat → Prop) (α : Nat → Type) (s : Set ℕ)

/-- info: ∀ x > 0, P x : Prop -/
#guard_msgs in
#check ∀ x, x > 0 → P x

/-- info: ∀ x > 0, P x : Prop -/
#guard_msgs in
#check ∀ x > 0, P x

/-- info: ∀ x ≥ 0, P x : Prop -/
#guard_msgs in
#check ∀ x, x ≥ 0 → P x

/-- info: ∀ x ≥ 0, P x : Prop -/
#guard_msgs in
#check ∀ x ≥ 0, P x

/-- info: ∀ x < 0, P x : Prop -/
#guard_msgs in
#check ∀ x < 0, P x

/-- info: ∀ x < 0, P x : Prop -/
#guard_msgs in
#check ∀ x, x < 0 → P x

/-- info: ∀ x ≤ 0, P x : Prop -/
#guard_msgs in
#check ∀ x ≤ 0, P x

/-- info: ∀ x ≤ 0, P x : Prop -/
#guard_msgs in
#check ∀ x, x ≤ 0 → P x

/-- info: ∀ x ∈ s, P x : Prop -/
#guard_msgs in
#check ∀ x ∈ s, P x

/-- info: ∀ x ∈ s, P x : Prop -/
#guard_msgs in
#check ∀ x, x ∈ s → P x

/-- info: ∀ x ∉ s, P x : Prop -/
#guard_msgs in
#check ∀ x ∉ s,P x

/-- info: ∀ x ∉ s, P x : Prop -/
#guard_msgs in
#check ∀ x, x ∉ s → P x

variable (Q : Set ℕ → Prop)

/-- info: ∀ t ⊆ s, Q t : Prop -/
#guard_msgs in
#check ∀ t ⊆ s, Q t

/-- info: ∀ t ⊆ s, Q t : Prop -/
#guard_msgs in
#check ∀ t, t ⊆ s → Q t

/-- info: ∀ t ⊂ s, Q t : Prop -/
#guard_msgs in
#check ∀ t ⊂ s, Q t

/-- info: ∀ t ⊂ s, Q t : Prop -/
#guard_msgs in
#check ∀ t, t ⊂ s → Q t

/-- info: ∀ t ⊇ s, Q t : Prop -/
#guard_msgs in
#check ∀ t ⊇ s, Q t

/-- info: ∀ t ⊇ s, Q t : Prop -/
#guard_msgs in
#check ∀ t, t ⊇ s → Q t

/-- info: ∀ t ⊃ s, Q t : Prop -/
#guard_msgs in
#check ∀ t ⊃ s, Q t

/-- info: ∀ t ⊃ s, Q t : Prop -/
#guard_msgs in
#check ∀ t, t ⊃ s → Q t

/-- info: (x : ℕ) → α x : Type -/
#guard_msgs in
#check (x : Nat) → α x

open PiNotation

/-- info: Π (x : ℕ), α x : Type -/
#guard_msgs in
#check (x : Nat) → α x

/-- info: ∀ (x : ℕ), P x : Prop -/
#guard_msgs in
#check (x : Nat) → P x

end PiNotation

section UnionInter
variable (s : ℕ → Set ℕ) (u : Set ℕ) (p : ℕ → Prop)

/-- info: ⋃ n ∈ u, s n : Set ℕ -/
#guard_msgs in
#check ⋃ n ∈ u, s n

/-- info: ⋂ n ∈ u, s n : Set ℕ -/
#guard_msgs in
#check ⋂ n ∈ u, s n

end UnionInter

section CompleteLattice
/-- info: ⨆ i ∈ Set.univ, (i = i) : Prop -/
#guard_msgs in
#check ⨆ (i : Nat) (_ : i ∈ Set.univ), (i = i)

/-- info: ⨅ i ∈ Set.univ, (i = i) : Prop -/
#guard_msgs in
#check ⨅ (i : Nat) (_ : i ∈ Set.univ), (i = i)

end CompleteLattice

section existential

/-- info: ∃ i ≥ 3, i = i : Prop -/
#guard_msgs in
#check ∃ (i : Nat), i ≥ 3 ∧ i = i

/-- info: ∃ i > 3, i = i : Prop -/
#guard_msgs in
#check ∃ (i : Nat), i > 3 ∧ i = i

/-- info: ∃ i ≤ 3, i = i : Prop -/
#guard_msgs in
#check ∃ (i : Nat), i ≤ 3 ∧ i = i

/-- info: ∃ i < 3, i = i : Prop -/
#guard_msgs in
#check ∃ (i : Nat), i < 3 ∧ i = i

variable (s : Set ℕ) (P : ℕ → Prop) (Q : Set ℕ → Prop)

/-- info: ∃ x ∉ s, P x : Prop -/
#guard_msgs in
#check ∃ x ∉ s, P x

/-- info: ∃ x ∉ s, P x : Prop -/
#guard_msgs in
#check ∃ x, x ∉ s ∧ P x

variable (Q : Set ℕ → Prop)

/-- info: ∃ t ⊆ s, Q t : Prop -/
#guard_msgs in
#check ∃ t ⊆ s, Q t

/-- info: ∃ t ⊆ s, Q t : Prop -/
#guard_msgs in
#check ∃ t, t ⊆ s ∧ Q t

/-- info: ∃ t ⊂ s, Q t : Prop -/
#guard_msgs in
#check ∃ t ⊂ s, Q t

/-- info: ∃ t ⊂ s, Q t : Prop -/
#guard_msgs in
#check ∃ t, t ⊂ s ∧ Q t

/-- info: ∃ t ⊇ s, Q t : Prop -/
#guard_msgs in
#check ∃ t ⊇ s, Q t

/-- info: ∃ t ⊇ s, Q t : Prop -/
#guard_msgs in
#check ∃ t, t ⊇ s ∧ Q t

/-- info: ∃ t ⊃ s, Q t : Prop -/
#guard_msgs in
#check ∃ t ⊃ s, Q t

/-- info: ∃ t ⊃ s, Q t : Prop -/
#guard_msgs in
#check ∃ t, t ⊃ s ∧ Q t

/-- info: ∃ n k, n = k : Prop -/
#guard_msgs in
#check ∃ n k, n = k

/-- info: ∃ n k, n = k : Prop -/
#guard_msgs in
#check ∃ n, ∃ k, n = k

end existential

section prod

variable (x : ℕ × ℕ)

/-- info: x.1 : ℕ -/
#guard_msgs in
#check x.1

variable (p : (ℕ → ℕ) × (ℕ → ℕ))

/-- info: p.1 22 : ℕ -/
#guard_msgs in
#check p.1 22

end prod
