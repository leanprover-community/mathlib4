/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Separation
import Mathlib.Topology.ContinuousFunction.Basic

/-!
# Specialization order

This file defines a type synonym for a topological space considered with its specialisation order.
-/


/-- Type synonym for a topological space considered with its specialisation order. -/
def Specialization (α : Type*) := α

namespace Specialization
variable {α β γ : Type*}

/-- `toEquiv` is the "identity" function to the `Specialization` of a type. -/
@[match_pattern] def toEquiv : α ≃ Specialization α := Equiv.refl _

/-- `ofEquiv` is the identity function from the `Specialization` of a type.  -/
@[match_pattern] def ofEquiv : Specialization α ≃ α := Equiv.refl _

@[simp] lemma toEquiv_symm : (@toEquiv α).symm = ofEquiv := rfl
@[simp] lemma ofEquiv_symm : (@ofEquiv α).symm = toEquiv := rfl
@[simp] lemma toEquiv_ofEquiv (a : Specialization α) : toEquiv (ofEquiv a) = a := rfl
@[simp] lemma ofEquiv_toEquiv (a : α) : ofEquiv (toEquiv a) = a := rfl
-- The following two are eligible for `dsimp`
@[simp, nolint simpNF] lemma toEquiv_inj {a b : α} : toEquiv a = toEquiv b ↔ a = b := Iff.rfl
@[simp, nolint simpNF] lemma ofEquiv_inj {a b : Specialization α} : ofEquiv a = ofEquiv b ↔ a = b :=
Iff.rfl

/-- A recursor for `Specialization`. Use as `induction x using Specialization.rec`. -/
protected def rec {β : Specialization α → Sort*} (h : ∀ a, β (toEquiv a)) (a : α) : β a :=
h (ofEquiv a)

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

instance instPreorder : Preorder (Specialization α) := specializationPreorder α
instance instPartialOrder [T0Space α] : PartialOrder (Specialization α) := specializationOrder α

@[simp] lemma toEquiv_le_toEquiv {a b : α} : toEquiv a ≤ toEquiv b ↔ b ⤳ a := Iff.rfl
@[simp] lemma ofEquiv_specializes_ofEquiv {a b : Specialization α} :
  ofEquiv a ⤳ ofEquiv b ↔ b ≤ a := Iff.rfl

/-- A continuous map between topological spaces induces a monotone map between their specialization
orders. -/
def map (f : C(α, β)) : Specialization α →o Specialization β where
  toFun := toEquiv ∘ f ∘ ofEquiv
  monotone' := f.continuous.specialization_monotone

@[simp] lemma map_id : map (ContinuousMap.id α) = OrderHom.id := rfl
@[simp] lemma map_comp (g : C(β, γ)) (f : C(α, β)) : map (g.comp f) = (map g).comp (map f) := rfl

end Specialization
