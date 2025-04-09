/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Basic
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
  (NatIso.ofComponents (fun M => (ConcreteCategory.homEquiv.trans
    (MonoidHom.fromULiftMultiplicativeIntEquiv M.carrier)).toIso))

/-- The forget functor `CommGrp.{u} ⥤ Type u` is corepresentable. -/
def CommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrp.{u} :=
  (NatIso.ofComponents (fun M => (ConcreteCategory.homEquiv.trans
    (MonoidHom.fromULiftMultiplicativeIntEquiv M.carrier)).toIso))

/-- The forget functor `AddGrp.{u} ⥤ Type u` is corepresentable. -/
def AddGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrp.{u} :=
  (NatIso.ofComponents (fun M => (ConcreteCategory.homEquiv.trans
    (AddMonoidHom.fromULiftIntEquiv M.carrier)).toIso))

/-- The forget functor `AddCommGrp.{u} ⥤ Type u` is corepresentable. -/
def AddCommGrp.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrp.{u} :=
  (NatIso.ofComponents (fun M => (ConcreteCategory.homEquiv.trans
    (AddMonoidHom.fromULiftIntEquiv M.carrier)).toIso))

instance Grp.forget_isCorepresentable :
    (forget Grp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' Grp.coyonedaObjIsoForget

instance CommGrp.forget_isCorepresentable :
    (forget CommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrp.coyonedaObjIsoForget

instance AddGrp.forget_isCorepresentable :
    (forget AddGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrp.coyonedaObjIsoForget

instance AddCommGrp.forget_isCorepresentable :
    (forget AddCommGrp.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrp.coyonedaObjIsoForget
