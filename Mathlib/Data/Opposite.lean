/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Small.Defs

/-!
# Opposites

In this file we define a structure `Opposite α` containing a single field of type `α` and
two bijections `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. If `α` is a category, then `αᵒᵖ` is the
opposite category, with all arrows reversed.

-/


universe v u

-- morphism levels before object levels. See note [category theory universes].
variable (α : Sort u)

/-- The type of objects of the opposite of `α`; used to define the opposite category.

Now that Lean 4 supports definitional eta equality for records,
both `unop (op X) = X` and `op (unop X) = X` are definitional equalities.
-/
structure Opposite where
  /-- The canonical map `α → αᵒᵖ`. -/
  op ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop : α

attribute [pp_nodot] Opposite.unop

/-- Make sure that `Opposite.op a` is pretty-printed as `op a` instead of `{ unop := a }` or
`⟨a⟩`. -/
@[app_unexpander Opposite.op]
protected def Opposite.unexpander_op : Lean.PrettyPrinter.Unexpander
  | s => pure s

@[inherit_doc]
notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `Presheaf Cᵒᵖ` parses as `Presheaf (Cᵒᵖ)` and not `(Presheaf C)ᵒᵖ`.
α "ᵒᵖ" => Opposite α

namespace Opposite

variable {α}

theorem op_injective : Function.Injective (op : α → αᵒᵖ) := fun _ _ => congr_arg Opposite.unop

theorem unop_injective : Function.Injective (unop : αᵒᵖ → α) := fun ⟨_⟩⟨_⟩ => by simp

@[simp]
theorem op_unop (x : αᵒᵖ) : op (unop x) = x :=
  rfl

theorem unop_op (x : α) : unop (op x) = x :=
  rfl

-- We could prove these by `Iff.rfl`, but that would make these eligible for `dsimp`. That would be
-- a bad idea because `Opposite` is irreducible.
theorem op_inj_iff (x y : α) : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
theorem unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

/-- The type-level equivalence between a type and its opposite. -/
def equivToOpposite : α ≃ αᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop

theorem op_surjective : Function.Surjective (op : α → αᵒᵖ) := equivToOpposite.surjective

theorem unop_surjective : Function.Surjective (unop : αᵒᵖ → α) := equivToOpposite.symm.surjective

@[simp]
theorem equivToOpposite_coe : (equivToOpposite : α → αᵒᵖ) = op :=
  rfl

@[simp]
theorem equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ → α) = unop :=
  rfl

theorem op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y :=
  equivToOpposite.apply_eq_iff_eq_symm_apply

theorem unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y :=
  equivToOpposite.symm.apply_eq_iff_eq_symm_apply

instance [Inhabited α] : Inhabited αᵒᵖ :=
  ⟨op default⟩

instance [Nonempty α] : Nonempty αᵒᵖ := Nonempty.map op ‹_›

instance [Subsingleton α] : Subsingleton αᵒᵖ := unop_injective.subsingleton

/-- A deprecated alias for `Opposite.rec`. -/
@[deprecated Opposite.rec (since := "2025-04-04")]
protected def rec' {F : αᵒᵖ → Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)

/-- If `X` is `u`-small, also `Xᵒᵖ` is `u`-small. -/
instance small {X : Type v} [Small.{u} X] : Small.{u} Xᵒᵖ := by
  obtain ⟨S, ⟨e⟩⟩ := Small.equiv_small (α := X)
  exact ⟨S, ⟨equivToOpposite.symm.trans e⟩⟩

end Opposite
