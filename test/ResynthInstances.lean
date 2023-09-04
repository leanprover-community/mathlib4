import Mathlib.Tactic.Classical
import Mathlib.Tactic.ResynthInstances
import Std.Tactic.GuardExpr
import Std.Tactic.GuardMsgs

set_option autoImplicit true

-- On command line, tests format functions with => rather than ↦ without this.
set_option pp.unicode.fun true

/--
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for α : Type inst : DecidableEq α x y : α ⊢ Decidable (x = y)
-/
#guard_msgs in
example : ∀ (α : Type) [DecidableEq α] (x y : α), if x = y then True else True := by
  resynth_instances?
  intros; split <;> trivial

/--
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for x y : Nat ⊢ Decidable (x = y)
-/
#guard_msgs in
example : ∀ (x y : Nat), if x = y then True else True := by
  resynth_instances?
  intros; split <;> trivial

/--
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for α : Type inst : DecidableEq α x y : α ⊢ Decidable (x = y)
-/
#guard_msgs in
example : ∀ (α : Type) [DecidableEq α] (x y : α), if x = y then True else True := by
  resynth_instances?
  intros; split <;> trivial

/--
info: ❌ resynthesis is non-defeq for
  α : Type
  x y : α
  em : (a : Prop) → Decidable a
  ⊢ Decidable (x = y)
---
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for α : Type x y : α em : (a : Prop) → Decidable a ⊢ Decidable (x = y)
-/
#guard_msgs in
example : ∀ (α : Type) [DecidableEq α] (x y : α), if x = y then True else True := by
  intros α inst x y
  classical!
  resynth_instances?
  clear inst
  rename_i em
  revert α em
  resynth_instances?
  intros; split <;> trivial

/--
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for
  ⊢ OfNat Nat 2
---
✅ resynthesis is defeq for
  ⊢ OfNat Nat 1
---
✅ resynthesis is defeq for ⊢ HAdd Nat Nat Nat
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  resynth_instances?
  rfl

/--
info: resynthesis results in the same expression
---
✅ resynthesis is defeq for
  ⊢ OfNat Nat 2
---
✅ resynthesis is defeq for
  ⊢ OfNat Nat 1
---
✅ resynthesis is defeq for ⊢ HAdd Nat Nat Nat
---
error: unsolved goals
_x : Nat
h : 1 + 1 = 2
⊢ True
-/
#guard_msgs in
example (h : 1 + 1 = 2) (_x : Nat) : True := by
  resynth_instances? at h
  done

inductive Two | one | two

/--
info: resynthesis results in the same expression
---
💥 failed to resynthesize ⊢ Inhabited Two
-/
#guard_msgs in
example : @Inhabited.default Two ⟨.one⟩ = .one := by
  resynth_instances?
  rfl

instance : Inhabited Two := ⟨.one⟩

/--
info: ❌ resynthesis is non-defeq for
  ⊢ Inhabited Two
---
error: type mismatch
  rfl
has type
  default = default : Prop
but is expected to have type
  default = Two.two : Prop
-/
#guard_msgs in
example : @default Two ⟨.two⟩ = .two := by
  resynth_instances?
  exact rfl

def Two.one' := Two.one

/--
info: ❌ resynthesis is non-defeq for
  ⊢ Inhabited Two
-/
#guard_msgs in
example : @default Two ⟨.one'⟩ = .one := by
  resynth_instances?
  rfl

attribute [reducible] Two.one'

/--
info: ✅ resynthesis is defeq for
  ⊢ Inhabited Two
-/
#guard_msgs in
example : @default Two ⟨.one'⟩ = .one := by
  resynth_instances?
  rfl

/--
info: ❌ resynthesis is non-defeq for
  ⊢ Inhabited Nat
---
✅ resynthesis is defeq for
  ⊢ Inhabited Nat
---
✅ resynthesis is defeq for ⊢ OfNat (Fin (0 + 1)) 0
---
error: resynthesis results in a type-incorrect expression
-/
#guard_msgs in
example :
    let inst : Inhabited Nat := ⟨1⟩; let x : Nat := default; (0 : Fin x) = 0 := by
  resynth_instances? -- "results in a type incorrect expression"

/--
info: resynthesis results in the same expression
---
info: ✅ resynthesis is defeq for
  ⊢ Inhabited Nat
---
error: unsolved goals
inst✝ : Inhabited Nat := { default := 2 }
inst : Inhabited Nat := inst✝
⊢ True
-/
#guard_msgs in
example : True := by
  let inst : Inhabited Nat := ⟨2⟩
  resynth_instances? at inst
  done
