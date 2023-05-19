import Mathlib.Tactic.TFAE

open List

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
  { exact pq }
  tfae_have 2 → 1
  { exact qp }
  tfae_finish

example : TFAE [P, Q] := by
  tfae_have 1 ↔ 2
  { exact Iff.intro pq qp }
  tfae_finish

example : TFAE [P, Q] := by
  tfae_have 2 ← 1
  { exact pq }
  tfae_have 1 ← 2
  { exact qp }
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
  { exact pq }
  tfae_have 2 → 3
  { exact qr }
  tfae_have 3 → 1
  { exact rp }
  tfae_finish

example : TFAE [P, Q, R] := by
  tfae_have 1 ↔ 2
  { exact Iff.intro pq (rp ∘ qr) }
  tfae_have 3 ↔ 2
  { exact Iff.intro (pq ∘ rp) qr }
  tfae_finish

example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  { exact pq }
  tfae_have 2 → 1
  { exact rp ∘ qr }
  tfae_have 2 ↔ 3
  { exact Iff.intro qr (pq ∘ rp) }
  tfae_finish

end three

section context

example (h₁ : P → Q) (h₂ : Q → P) : TFAE [P, Q] := by
  tfae_finish

end context
