import Mathlib.Data.Matrix.Rank
import Mathlib.Tactic.Order

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

example (a b c d e : Nat) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : b ≠ d) :
    a < e := by
  order

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  order

example (a b : Int) (h1 : ¬(a < b)) (h2 : ¬(b < a)) : a = b := by
  order

example {α : Type} [LinearOrder α] (a b : α) (h1 : ¬(a < b)) (h2 : ¬(b < a)) : a = b := by
  order

example {α : Type} [PartialOrder α] (a b c d e : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : b ≠ d) :
    a < e := by
  order

example {α : Type} [PartialOrder α] (s t x y : α) (h1 : s ≤ x) (h2 : x ≤ t) (h3 : s ≤ y)
    (h4 : y ≤ t) (h5 : x ≠ y) :
    s < t := by
  order

example {α : Type} [PartialOrder α] (a b c d : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : ¬(a < c))
    (h4 : a ≤ d) :
    c ≤ d := by
  order

example {α : Type} [PartialOrder α] (a : α) :
    ¬ (a < a) := by
  order

example {α : Type} [Preorder α] (a b c d : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : ¬(a < c))
    (h4 : a ≤ d) :
    c ≤ d := by
  order

example {α : Type} [Preorder α] (a b : α) (h1 : a < b) : b > a := by
  order

example {α : Type} [Preorder α] (a b : α) (h1 : a > b) : b < a := by
  order

example {n : Nat} (A B C : Matrix (Fin n) (Fin n) ℚ) : (A * B * C).rank ≤ A.rank ⊓ C.rank := by
  have h1 := Matrix.rank_mul_le A B
  have h2 := Matrix.rank_mul_le (A * B) C
  have h3 : A.rank ⊓ B.rank ≤ A.rank := inf_le_left
  have h4 : (A * B).rank ⊓ C.rank ≤ (A * B).rank := inf_le_left
  have h5 : (A * B).rank ⊓ C.rank ≤ C.rank := inf_le_right
  simp
  constructor
  · order
  · order

-- worst case for the current algorithm
example {α : Type u} [PartialOrder α]
    (x1 y1 : α)
    (x2 y2 : α)
    (x3 y3 : α)
    (x4 y4 : α)
    (x5 y5 : α)
    (x6 y6 : α)
    (x7 y7 : α)
    (x8 y8 : α)
    (x9 y9 : α)
    (x10 y10 : α)
    (x11 y11 : α)
    (x12 y12 : α)
    (x13 y13 : α)
    (x14 y14 : α)
    (x15 y15 : α)
    (x16 y16 : α)
    (x17 y17 : α)
    (x18 y18 : α)
    (x19 y19 : α)
    (x20 y20 : α)
    (x21 y21 : α)
    (x22 y22 : α)
    (x23 y23 : α)
    (x24 y24 : α)
    (x25 y25 : α)
    (x26 y26 : α)
    (x27 y27 : α)
    (x28 y28 : α)
    (x29 y29 : α)
    (x30 y30 : α)
    (h0 : y1 ≤ x1)
    (h1 : ¬(y1 < x1)) (h2 : y2 ≤ x1) (h3 : y1 ≤ x2)
    (h4 : ¬(y2 < x2)) (h5 : y3 ≤ x2) (h6 : y2 ≤ x3)
    (h7 : ¬(y3 < x3)) (h8 : y4 ≤ x3) (h9 : y3 ≤ x4)
    (h10 : ¬(y4 < x4)) (h11 : y5 ≤ x4) (h12 : y4 ≤ x5)
    (h13 : ¬(y5 < x5)) (h14 : y6 ≤ x5) (h15 : y5 ≤ x6)
    (h16 : ¬(y6 < x6)) (h17 : y7 ≤ x6) (h18 : y6 ≤ x7)
    (h19 : ¬(y7 < x7)) (h20 : y8 ≤ x7) (h21 : y7 ≤ x8)
    (h22 : ¬(y8 < x8)) (h23 : y9 ≤ x8) (h24 : y8 ≤ x9)
    (h25 : ¬(y9 < x9)) (h26 : y10 ≤ x9) (h27 : y9 ≤ x10)
    (h28 : ¬(y10 < x10)) (h29 : y11 ≤ x10) (h30 : y10 ≤ x11)
    (h31 : ¬(y11 < x11)) (h32 : y12 ≤ x11) (h33 : y11 ≤ x12)
    (h34 : ¬(y12 < x12)) (h35 : y13 ≤ x12) (h36 : y12 ≤ x13)
    (h37 : ¬(y13 < x13)) (h38 : y14 ≤ x13) (h39 : y13 ≤ x14)
    (h40 : ¬(y14 < x14)) (h41 : y15 ≤ x14) (h42 : y14 ≤ x15)
    (h43 : ¬(y15 < x15)) (h44 : y16 ≤ x15) (h45 : y15 ≤ x16)
    (h46 : ¬(y16 < x16)) (h47 : y17 ≤ x16) (h48 : y16 ≤ x17)
    (h49 : ¬(y17 < x17)) (h50 : y18 ≤ x17) (h51 : y17 ≤ x18)
    (h52 : ¬(y18 < x18)) (h53 : y19 ≤ x18) (h54 : y18 ≤ x19)
    (h55 : ¬(y19 < x19)) (h56 : y20 ≤ x19) (h57 : y19 ≤ x20)
    (h58 : ¬(y20 < x20)) (h59 : y21 ≤ x20) (h60 : y20 ≤ x21)
    (h61 : ¬(y21 < x21)) (h62 : y22 ≤ x21) (h63 : y21 ≤ x22)
    (h64 : ¬(y22 < x22)) (h65 : y23 ≤ x22) (h66 : y22 ≤ x23)
    (h67 : ¬(y23 < x23)) (h68 : y24 ≤ x23) (h69 : y23 ≤ x24)
    (h70 : ¬(y24 < x24)) (h71 : y25 ≤ x24) (h72 : y24 ≤ x25)
    (h73 : ¬(y25 < x25)) (h74 : y26 ≤ x25) (h75 : y25 ≤ x26)
    (h76 : ¬(y26 < x26)) (h77 : y27 ≤ x26) (h78 : y26 ≤ x27)
    (h79 : ¬(y27 < x27)) (h80 : y28 ≤ x27) (h81 : y27 ≤ x28)
    (h82 : ¬(y28 < x28)) (h83 : y29 ≤ x28) (h84 : y28 ≤ x29)
    (h85 : ¬(y29 < x29)) (h86 : y30 ≤ x29) (h87 : y29 ≤ x30)
    (h88 : ¬(y30 < x30)) : x30 = y30 := by
  order
