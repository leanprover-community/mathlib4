/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.CategoryTheory.Yoneda

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrp.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrp`, `AddGrp`
and `Grp`.

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

/-- The forget functor `Grp.{u} ⥤ Type u` is corepresentable. -/
def Grp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget Grp.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))

/-- The forget functor `CommGrp.{u} ⥤ Type u` is corepresentable. -/
def CommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrp.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeIntEquiv M.α).toIso))

/-- The forget functor `AddGrp.{u} ⥤ Type u` is corepresentable. -/
def AddGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrp.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))

/-- The forget functor `AddCommGrp.{u} ⥤ Type u` is corepresentable. -/
def AddCommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrp.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftIntEquiv M.α).toIso))

instance Grp.forget_corepresentable :
    (forget Grp.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨Grp.coyonedaObjIsoForget⟩⟩

instance CommGrp.forget_corepresentable :
    (forget CommGrp.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨CommGrp.coyonedaObjIsoForget⟩⟩

instance AddGrp.forget_corepresentable :
    (forget AddGrp.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨AddGrp.coyonedaObjIsoForget⟩⟩

instance AddCommGrp.forget_corepresentable :
    (forget AddCommGrp.{u}).Corepresentable where
  has_corepresentation := ⟨_, ⟨AddCommGrp.coyonedaObjIsoForget⟩⟩
