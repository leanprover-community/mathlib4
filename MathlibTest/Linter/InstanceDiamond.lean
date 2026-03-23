import Mathlib.Tactic.Linter.InstanceDiamond

/-! # Tests for the instance diamond linter

Note: For classes declared with `class ... extends B, C`, Lean's structure elaborator
guarantees that diamond paths are definitionally equal by construction. The linter
serves as a safety net for cases where this might fail (e.g., bugs in instance
wrapping, `inferInstanceAs`, or `deriving`).
-/

namespace InstanceDiamondTest

-- Simple diamond hierarchy
class A (α : Type _) where a : α
class B (α : Type _) extends A α where b : α
class C (α : Type _) extends A α where c : α
class D (α : Type _) extends B α, C α

-- Deeper diamond (depth 3): F → D' → B → A and F → E → C → A
class D' (α : Type _) extends B α where d : α
class E (α : Type _) extends C α where e : α
class F (α : Type _) extends D' α, E α

-- Instances — all consistent by construction, no linter warnings expected
instance : D Nat where a := 0; b := 1; c := 2
instance : F Nat where a := 0; b := 1; c := 2; d := 3; e := 4

end InstanceDiamondTest
