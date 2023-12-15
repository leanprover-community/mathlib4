import Mathlib.Tactic.TFAE

open List
set_option autoImplicit true

section zeroOne

example : TFAE []  := by tfae_finish
example : TFAE [P] := by tfae_finish

end zeroOne

namespace two

axiom P : Prop
axiom Q : Prop
axiom pq : P → Q
axiom qp : Q → P

example : TFAE [P, Q] := by
  tfae_have 1 → 2
  · exact pq
  tfae_have 2 → 1
  · exact qp
  tfae_finish

example : TFAE [P, Q] := by
  tfae_have 1 ↔ 2
  · exact Iff.intro pq qp
  tfae_finish

example : TFAE [P, Q] := by
  tfae_have 2 ← 1
  · exact pq
  tfae_have 1 ← 2
  · exact qp
  tfae_finish

end two

namespace three

axiom P : Prop
axiom Q : Prop
axiom R : Prop
axiom pq : P → Q
axiom qr : Q → R
axiom rp : R → P

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
  tfae_have 1 → 2
  · exact pq
  tfae_have 2 → 1
  · exact rp ∘ qr
  tfae_have 2 ↔ 3
  · exact Iff.intro qr (pq ∘ rp)
  tfae_finish

end three

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
  tfae_have 1 ↔ 2
  · exact h₁
  tfae_have 1 → 6
  · exact h₂
  tfae_have 6 → 7
  · exact h₃
  tfae_have 7 → 4
  · exact h₄
  tfae_have 4 → 5
  · exact h₅
  tfae_have 5 → 3
  · exact h₆
  tfae_have 3 → 2
  · exact h₇
  tfae_finish

end seven

section context

example (n : ℕ) : List.TFAE [n = 1, n + 1 = 2] := by
  generalize n = m
  tfae_have 1 ↔ 2; simp
  tfae_finish

example (h₁ : P → Q) (h₂ : Q → P) : TFAE [P, Q] := by
  tfae_finish

end context
