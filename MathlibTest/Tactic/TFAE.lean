import Mathlib.Tactic.TFAE
import Mathlib.Tactic.SuccessIfFailWithMsg

open List
set_option autoImplicit true

/-! # 'Old-style' `tfae` (`tfae_have`/`tfae_finish`) -/

section zeroOne

example : TFAE []  := by tfae_finish
example : TFAE [P] := by tfae_finish

end zeroOne

/- Note: can't use `variable` otherwise these are present in the local context, and get caught by
`tfae_finish`. -/
axiom P : Prop
axiom Q : Prop
axiom pq : P → Q
axiom qp : Q → P

axiom R : Prop
axiom qr : Q → R
axiom rp : R → P

/-! Old-style `have` -/

example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · exact pq
  tfae_have 2 → 3
  · exact qr
  tfae_have 3 → 1
  · exact rp
  tfae_finish

example : TFAE [P, Q, R] := by
  tfae_have 1 ↔ 2
  · exact Iff.intro pq (rp ∘ qr)
  tfae_have 3 ↔ 2
  · exact Iff.intro (pq ∘ rp) qr
  tfae_finish

example : TFAE [P, Q, R] := by
  tfae_have 1 → 2 := pq
  tfae_have 2 → 1
  · exact rp ∘ qr
  tfae_have 2 ↔ 3
  · exact Iff.intro qr (pq ∘ rp)
  tfae_finish

/-! The following tests test both `tfae_have` and the `tfae` block tactic. -/

section seven

axiom P₁ : Prop
axiom P₂ : Prop
axiom P₃ : Prop
axiom P₄ : Prop
axiom P₅ : Prop
axiom P₆ : Prop
axiom P₇ : Prop
axiom h₁ : P₁ ↔ P₂
axiom h₂ : P₁ → P₆
axiom h₃ : P₆ → P₇
axiom h₄ : P₇ → P₄
axiom h₅ : P₄ → P₅
axiom h₆ : P₅ → P₃
axiom h₇ : P₃ → P₂

example : TFAE [P₁, P₂, P₃, P₄, P₅, P₆, P₇] := by
  tfae_have 1 ↔ 2 := h₁
  tfae_have 1 → 6 := h₂
  tfae_have 6 → 7 := h₃
  tfae_have 7 → 4 := h₄
  tfae_have 4 → 5 := h₅
  tfae_have 5 → 3 := h₆
  tfae_have 3 → 2 := h₇
  tfae_finish

example : TFAE [P₁, P₂, P₃, P₄, P₅, P₆, P₇] := by
  tfae
    1 ↔ 2 := h₁
    1 → 6 := h₂
    6 → 7 := h₃
    7 → 4 := h₄
    4 → 5 := h₅
    5 → 3 := h₆
    3 → 2 := h₇

end seven

section context

example (n : ℕ) : List.TFAE [n = 1, n + 1 = 2] := by
  generalize n = m
  tfae 1 ↔ 2 := by simp

example (h₁ : P → Q) (h₂ : Q → P) : TFAE [P, Q] := by
  tfae_finish

end context

section naming

example : TFAE [P, Q] := by
  tfae_have h : 1 → 2 := pq
  guard_hyp h : P → Q
  tfae_have _ : 1 ← 2 := qp
  tfae_finish

example : TFAE [P, Q] := by
  have n : ℕ := 4
  tfae_have 1 → 2 := by
    guard_hyp n : ℕ -- hypotheses are accessible (context is correct)
    guard_target =ₛ P → Q -- expected type is known
    exact pq
  tfae_have 1 ← 2 := qp
  tfae_finish

section refine

-- check `have := f ?a` feature works for `tfae_have`, and occurs check succeeds
example : TFAE [P, Q] := by
  have n : ℕ := 3
  tfae_have 2 ← 1 := fun p => ?Qgoal
  case Qgoal => exact pq p
  refine ?a
  fail_if_success (tfae_have 1 ← 2 := ((?a).out 1 2 sorry sorry).mpr)
  tfae_have 2 → 1 := qp
  tfae_finish

end refine

section matching

example : TFAE [P, Q] := by
  tfae_have 1 → 2
  | p => pq p
  tfae_have 2 → 1
  | q => qp q
  tfae_finish

example : TFAE [P, Q] := by
  tfae
    1 → 2
    | p => pq p
    2 → 1
    | q => qp q

example : TFAE [P, ∀(_ : Nat), Q] := by
  tfae
    1 → 2
    | p, _ => pq p
    2 → 1
    | q => qp (q 0)

example : TFAE [P, Q] := by
  tfae ⟨mp, mpr⟩ : 1 ↔ 2 := ⟨pq, qp⟩

/--
error: type mismatch
  [false]
has type
  List Bool : Type
but is expected to have type
  P₂ : Prop
---
error: couldn't prove P₂ → P₁
-/
#guard_msgs in
example : TFAE [P₁, P₂] := by
  tfae
    1 → 2
    | p => [false]

end matching
