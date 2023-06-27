import Mathlib.Tactic.CheckInstances
import Std.Tactic.GuardMsgs

/--
info: ✅: resynthesized HAdd Nat Nat Nat
---
info: ✅: resynthesized Add Nat
---
info: ✅: resynthesized OfNat Nat 1
---
info: ✅: resynthesized OfNat Nat 1
---
info: ✅: resynthesized OfNat Nat 2
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  check_instances
  rfl

inductive Two | one | two

/--
info: 💥: failed to resynthesize Inhabited Two
-/
#guard_msgs in
example : @Inhabited.default Two ⟨.one⟩ = .one := by
  check_instances
  rfl

instance : Inhabited Two := ⟨.one⟩
/--
info: ❌: resynthesized Inhabited Two, but found
  instInhabitedTwo != { default := Two.two }
-/
#guard_msgs in
example : @default Two ⟨.two⟩ = .two := by
  check_instances
  rfl

def Two.one' := Two.one
/--
info: 🟡: resynthesized Inhabited Two, up to defeq
  instInhabitedTwo vs { default := Two.one' }
-/
#guard_msgs in
example : @default Two ⟨.one'⟩ = .one := by
  check_instances
  rfl

attribute [reducible] Two.one'
/--
info: ✅: resynthesized Inhabited Two, up to reducible defeq:
  instInhabitedTwo vs { default := Two.one' }
-/
#guard_msgs in
example : @default Two ⟨.one'⟩ = .one := by
  check_instances
  rfl
