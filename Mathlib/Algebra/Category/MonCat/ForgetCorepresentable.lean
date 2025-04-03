/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Data.Nat.Cast.Basic

/-!
# The forget functor is corepresentable

The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable
by `ULift ℕ`. Similar results are obtained for the variants `CommMonCat`, `AddMonCat`
and `MonCat`.

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

/-- The equivalence `(Multiplicative ℕ →* α) ≃ α` for any monoid `α`. -/
@[simps]
def fromMultiplicativeNatEquiv (α : Type u) [Monoid α] : (Multiplicative ℕ →* α) ≃ α where
  toFun φ := φ (Multiplicative.ofAdd 1)
  invFun x := powersHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- The equivalence `(ULift (Multiplicative ℕ) →* α) ≃ α` for any monoid `α`. -/
@[simps!]
def fromULiftMultiplicativeNatEquiv (α : Type u) [Monoid α] :
    (ULift.{u} (Multiplicative ℕ) →* α) ≃ α :=
  (precompEquiv (MulEquiv.ulift.symm) _).trans (fromMultiplicativeNatEquiv α)

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
def fromNatEquiv (α : Type u) [AddMonoid α] : (ℕ →+ α) ≃ α where
  toFun φ := φ 1
  invFun x := multiplesHom α x
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- The equivalence `(ULift ℕ →+ α) ≃ α` for any additive monoid `α`. -/
@[simps!]
def fromULiftNatEquiv (α : Type u) [AddMonoid α] : (ULift.{u} ℕ →+ α) ≃ α :=
  (precompEquiv (AddEquiv.ulift.symm) _).trans (fromNatEquiv α)

end AddMonoidHom

/-- The forgetful functor `MonCat.{u} ⥤ Type u` is corepresentable. -/
def MonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget MonCat.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeNatEquiv M.α).toIso))


/-- The forgetful functor `CommMonCat.{u} ⥤ Type u` is corepresentable. -/
def CommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget CommMonCat.{u} :=
  (NatIso.ofComponents (fun M => (MonoidHom.fromULiftMultiplicativeNatEquiv M.α).toIso))

/-- The forgetful functor `AddMonCat.{u} ⥤ Type u` is corepresentable. -/
def AddMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddMonCat.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftNatEquiv M.α).toIso))

/-- The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable. -/
def AddCommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddCommMonCat.{u} :=
  (NatIso.ofComponents (fun M => (AddMonoidHom.fromULiftNatEquiv M.α).toIso))

instance MonCat.forget_isCorepresentable :
    (forget MonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget

instance CommMonCat.forget_isCorepresentable :
    (forget CommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget

instance AddMonCat.forget_isCorepresentable :
    (forget AddMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget

instance AddCommMonCat.forget_isCorepresentable :
    (forget AddCommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget
