import Mathlib.Tactic.FastInstance
import Mathlib.Algebra.Group.InjSurj

variable (α : Type*)

structure Wrapped where
  val : α

theorem val_injective : Function.Injective (Wrapped.val (α := α)) :=
  fun ⟨_⟩ ⟨_⟩ h => congr_arg _ h

instance [Zero α] : Zero (Wrapped α) where zero := ⟨0⟩

instance [Add α] : Add (Wrapped α) where add m n := ⟨m.1 + n.1⟩

instance instAddSemigroup [AddSemigroup α] : AddSemigroup (Wrapped α) :=
  fast_instance% Function.Injective.addSemigroup _ (val_injective _) (fun _ _ => rfl)

instance instAddCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Wrapped α) :=
  fast_instance% Function.Injective.addCommSemigroup _ (val_injective _) (fun _ _ => rfl)

/--
info: def instAddSemigroup.{u_1} : (α : Type u_1) → [inst : AddSemigroup α] → AddSemigroup (Wrapped α) :=
fun α [inst : AddSemigroup α] => @AddSemigroup.mk (Wrapped α) (@instAddWrapped α (@AddSemigroup.toAdd α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instAddSemigroup
/--
info: def instAddCommSemigroup.{u_1} : (α : Type u_1) → [inst : AddCommSemigroup α] → AddCommSemigroup (Wrapped α) :=
fun α [inst : AddCommSemigroup α] =>
  @AddCommSemigroup.mk (Wrapped α) (@instAddSemigroup α (@AddCommSemigroup.toAddSemigroup α inst)) ⋯
-/
#guard_msgs in
set_option pp.explicit true in
#print instAddCommSemigroup
