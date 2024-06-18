/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Algebra.Group.ULift

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGroupCat.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGroupCat`, `AddGroupCat`
and `GroupCat`.

-/

universe u

open CategoryTheory Opposite

namespace MonoidHom

/-- The equivalence `(β →* γ) ≃ (α →* γ)` obtained by precomposition with
a multiplicative equivalence `e : α ≃* β`. -/
@[simps]
def precompEquiv {α β : Type*} [Monoid α] [Monoid β] (e : α ≃* β) (γ : Type*) [Monoid γ] :
    (β →* γ) ≃ (α →* γ) where
  toFun f := f.comp e
  invFun g := g.comp e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The equivalence `(Multiplicative ℤ →* α) ≃ α` for any group `α`. -/
@[simps]
def fromMultiplicativeIntEquiv (α : Type u) [Group α] : (Multiplicative ℤ →* α) ≃ α where
  toFun φ := φ (Multiplicative.ofAdd 1)
  invFun x := zpowersHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- The equivalence `(ULift (Multiplicative ℤ) →* α) ≃ α` for any group `α`. -/
@[simps!]
def fromULiftMultiplicativeIntEquiv (α : Type u) [Group α] :
    (ULift.{u} (Multiplicative ℤ) →* α) ≃ α :=
  (precompEquiv (MulEquiv.ulift.symm) _).trans (fromMultiplicativeIntEquiv α)

end MonoidHom

namespace AddMonoidHom

/-- The equivalence `(β →+ γ) ≃ (α →+ γ)` obtained by precomposition with
an additive equivalence `e : α ≃+ β`. -/
@[simps]
def precompEquiv {α β : Type*} [AddMonoid α] [AddMonoid β] (e : α ≃+ β) (γ : Type*) [AddMonoid γ] :
    (β →+ γ) ≃ (α →+ γ) where
  toFun f := f.comp e
  invFun g := g.comp e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- The equivalence `(ℤ →+ α) ≃ α` for any additive group `α`. -/
@[simps]
def fromIntEquiv (α : Type u) [AddGroup α] : (ℤ →+ α) ≃ α where
  toFun φ := φ 1
  invFun x := zmultiplesHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- The equivalence `(ULift ℤ →+ α) ≃ α` for any additive group `α`. -/
@[simps!]
def fromULiftIntEquiv (α : Type u) [AddGroup α] : (ULift.{u} ℤ →+ α) ≃ α :=
  (precompEquiv (AddEquiv.ulift.symm) _).trans (fromIntEquiv α)

end AddMonoidHom

/-- The forget functor `GroupCat.{u} ⥤ Type u` is corepresentable. -/
def GroupCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget GroupCat.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))

/-- The forget functor `CommGroupCat.{u} ⥤ Type u` is corepresentable. -/
def CommGroupCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGroupCat.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))

/-- The forget functor `AddGroupCat.{u} ⥤ Type u` is corepresentable. -/
def AddGroupCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGroupCat.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))

/-- The forget functor `AddCommGroupCat.{u} ⥤ Type u` is corepresentable. -/
def AddCommGroupCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGroupCat.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))

instance GroupCat.forget_corepresentable :
    (forget GroupCat.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨GroupCat.coyonedaObjIsoForget⟩⟩

instance CommGroupCat.forget_corepresentable :
    (forget CommGroupCat.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨CommGroupCat.coyonedaObjIsoForget⟩⟩

instance AddGroupCat.forget_corepresentable :
    (forget AddGroupCat.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨AddGroupCat.coyonedaObjIsoForget⟩⟩

instance AddCommGroupCat.forget_corepresentable :
    (forget AddCommGroupCat.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨AddCommGroupCat.coyonedaObjIsoForget⟩⟩
