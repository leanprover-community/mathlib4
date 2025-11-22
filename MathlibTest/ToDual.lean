import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation

-- test that we can translate between structures, reordering the arguments of the fields
class SemilatticeInf (α : Type) extends PartialOrder α, Min α where
  le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

class SemilatticeSup (α : Type) extends PartialOrder α, Max α where
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c

attribute [to_dual] SemilatticeInf
attribute [to_dual (reorder := 3 4 5)] SemilatticeSup.sup_le

@[to_dual]
lemma SemilatticeInf.le_inf' {α : Type} [SemilatticeInf α] (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
  SemilatticeInf.le_inf a b c

@[to_dual]
lemma SemilatticeSup.sup_le' {α : Type} [SemilatticeSup α] (a b c : α) : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  SemilatticeSup.sup_le a b c

-- we still cannot reorder arguments of arguments, so `SemilatticeInf.mk` is not tranlatable
/--
error: @[to_dual] failed. The translated value is not type correct. For help, see the docstring of `to_additive`, section `Troubleshooting`. Failed to add declaration
instSemilatticeSupOfForallLeForallMax:
Application type mismatch: The argument
  le_inf
has type
  ∀ (a b c : α), b ≤ a → c ≤ a → b ⊔ c ≤ a
but is expected to have type
  ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c
in the application
  { toPartialOrder := inst✝¹, toMax := inst✝, sup_le := le_inf }
-/
#guard_msgs in
@[to_dual]
instance {α : Type} [PartialOrder α] [Min α]
    (le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c) : SemilatticeInf α where
  le_inf
