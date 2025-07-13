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

variable {α : Type*}

example [LinearOrder α] (a b : α) (h1 : ¬(a < b)) (h2 : ¬(b < a)) : a = b := by
  order

example [PartialOrder α] (a b c d e : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) (h4 : d ≤ e) (h5 : b ≠ d) :
    a < e := by
  order

example [PartialOrder α] (s t x y : α) (h1 : s ≤ x) (h2 : x ≤ t) (h3 : s ≤ y)
    (h4 : y ≤ t) (h5 : x ≠ y) :
    s < t := by
  order

example [PartialOrder α] (a b c d : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : ¬(a < c))
    (h4 : a ≤ d) :
    c ≤ d := by
  order

example [PartialOrder α] (a : α) :
    ¬ (a < a) := by
  order

example [Preorder α] (a b c d : α) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : ¬(a < c))
    (h4 : a ≤ d) :
    c ≤ d := by
  order

example [Preorder α] (a b : α) (h1 : a < b) : b > a := by
  order

example [Preorder α] (a b : α) (h1 : a > b) : b < a := by
  order

example [PartialOrder α] [OrderTop α] (a : α) (h1 : ⊤ ≤ a) : a = ⊤ := by
  order

example [Preorder α] [OrderTop α] (a : α) (h1 : a > ⊤) : a < a := by
  order

example [Preorder α] [OrderBot α] [OrderTop α] : (⊥ : α) ≤ ⊤ := by
  order

example (a b : α) [PartialOrder α] [OrderBot α] [OrderTop α] (h : (⊥ : α) = ⊤) : a = b := by
  order

example (a b : α) [SemilatticeSup α] : a ≤ a ⊔ b := by
  order

example (a b c : α) [SemilatticeSup α] (h1 : a ≤ c) (h2 : b ≤ c) : a ⊔ b ≤ c := by
  order

example (a b c : α) [SemilatticeSup α] (h1 : a ≤ b) : a ⊔ c ≤ b ⊔ c := by
  order

example (a b : α) [Lattice α] : a ⊓ b ≤ a ⊔ b := by
  order

example (a b : α) [Lattice α] : a ⊓ b ≤ a ⊔ b := by
  order

example (a b : α) [Lattice α] : a ⊔ b = b ⊔ a := by
  order

example (a b c : α) [Lattice α] : a ⊓ (b ⊔ c) ≥ (a ⊓ b) ⊔ (a ⊓ c) := by
  order

set_option trace.order true in
/--
error: No contradiction found.

Additional diagnostic information may be available using the `set_option trace.order true` command.
---
trace:
[order] Working on type α (partial order)
[order] Collected atoms:
    #0 := a ⊓ (b ⊔ c)
    #1 := a
    #2 := b ⊔ c
    #3 := b
    #4 := c
    #5 := a ⊓ b ⊔ a ⊓ c
    #6 := a ⊓ b
    #7 := a ⊓ c
[order] Collected facts:
    #2 := #3 ⊔ #4
    #0 := #1 ⊓ #2
    #6 := #1 ⊓ #3
    #7 := #1 ⊓ #4
    #5 := #6 ⊔ #7
    ¬ #0 ≤ #5
[order] Processed facts:
    #3 ≤ #2
    #4 ≤ #2
    #2 := #3 ⊔ #4
    #0 ≤ #1
    #0 ≤ #2
    #0 := #1 ⊓ #2
    #6 ≤ #1
    #6 ≤ #3
    #6 := #1 ⊓ #3
    #7 ≤ #1
    #7 ≤ #4
    #7 := #1 ⊓ #4
    #6 ≤ #5
    #7 ≤ #5
    #5 := #6 ⊔ #7
    #0 ≠ #5
    ¬ #0 < #5
[order] Working on type ℕ (linear order)
[order] Collected atoms:
    #0 := x
    #1 := y
[order] Collected facts:
    #0 < #1
[order] Processed facts:
    #0 ≠ #1
    #0 ≤ #1
-/
#guard_msgs in
example (a b c : α) (x y : Nat) (h : x < y) [Lattice α] : a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c) := by
  order

-- This used to work when a different matching strategy was used in `order`.
-- This example is now considered outside the scope of the `order` tactic.
/--
error: No contradiction found.

Additional diagnostic information may be available using the `set_option trace.order true` command.
-/
#guard_msgs in
example (a b c : Set α) : a ∩ (b ∪ c) ≥ (a ∩ b) ∪ (a ∩ c) := by
  order

example {n : Nat} (A B C : Matrix (Fin n) (Fin n) ℚ) : (A * B * C).rank ≤ A.rank ⊓ C.rank := by
  have h1 := Matrix.rank_mul_le A B
  have h2 := Matrix.rank_mul_le (A * B) C
  order

-- worst case for the current algorithm
example [PartialOrder α]
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

-- Tests for linear order with lattice operations

example {α : Type*} [LinearOrder α] {a b c : α} (hab : a < b)
    (habc : min a b ≤ c) (hcba : min c b ≤ a) : a = c := by
  order

example {α : Type*} [LinearOrder α] {a b : α} (h : a ≠ max a b) : b = max a b := by
  order

example {α : Type*} [LinearOrder α] {a b : α} (h1 : min a b ≠ a) (h2 : max a b ≠ a) : False := by
  order

-- Note: `order` does not use distributivity in general
example {α : Type*} [LinearOrder α] {a b c : α} : max a (min b c) = min (max a b) (max a c) := by
  order

example {α : Type*} [LinearOrder α] [BoundedOrder α] {a b : α} (h1 : a ⊔ b = ⊤)
    (h2 : b ≠ ⊤) : a = ⊤ := by
  order

example {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α] {a b c d : α} (h1 : a ⊓ b = ⊥)
    (h2 : c ⊓ d = ⊥) (h3 : a ⊔ c = ⊤) (h4 : b ⊔ d = ⊤) (h5 : a ⊔ d = ⊤) (h6 : b ⊔ c = ⊤) : False := by
  have : (⊥ : α) < ⊤ := bot_lt_top -- TODO: detect `Nontrivial` instance in `order` and add this
  -- fact automatically
  order

example
    (x₀ x₁ y₀ y₁ t f : ℤ)
    (htf : f < t)
    (hxf : x₀ ⊓ x₁ ≤ f)
    (hyf : y₀ ⊓ y₁ ≤ f)
    (c1 : x₁ ⊔ y₁ ≥ t)
    (c2 : x₁ ⊔ y₀ ≥ t)
    (c3 : x₀ ⊔ y₁ ≥ t)
    (c4 : x₀ ⊔ y₀ ≥ t)
    : False := by
  omega

example {α : Type*} [LinearOrder α]
    (x₀ x₁ y₀ y₁ t f : α)
    (htf : f < t)
    (hxf : x₀ ⊓ x₁ ≤ f)
    (hyf : y₀ ⊓ y₁ ≤ f)
    (c1 : x₁ ⊔ y₁ ≥ t)
    (c2 : x₁ ⊔ y₀ ≥ t)
    (c3 : x₀ ⊔ y₁ ≥ t)
    (c4 : x₀ ⊔ y₀ ≥ t)
    : False := by
  order
