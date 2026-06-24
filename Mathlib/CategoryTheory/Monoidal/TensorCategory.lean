import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.JordanHolder

universe v u

open CategoryTheory MonoidalCategory Limits

variable {C : Type u} [Category.{v} C]

instance [Preadditive C] [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalClosed C] {X : C} :
    (tensorLeft X).Additive :=
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
  Functor.additive_of_preservesBinaryBiproducts ..

instance [Preadditive C] [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] {X : C} : (tensorRight X).Additive :=
  (tensorLeft X).additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)

instance [Preadditive C] [HasBinaryBiproducts C] [MonoidalCategory C] [MonoidalClosed C]
    [BraidedCategory C] :
  MonoidalPreadditive C where
    whiskerLeft_zero {X} := (tensorLeft X).map_zero ..
    zero_whiskerRight {X} := (tensorRight X).map_zero ..
    whiskerLeft_add {X _ _ _ _} := (tensorLeft X).map_add
    add_whiskerRight {X _ _ _ _} := (tensorRight X).map_add

instance [MonoidalCategory C] [RigidCategory C] : MonoidalClosed C :=
  monoidalClosedOfLeftRigidCategory C

/-- A weak tensor category over a field `k` (does not require that `C` is locally finite,
  i.e. that hom spaces are finite dimensional and finite length objects) -/
class WeakTensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v, u} C] [Abelian C]
    [MonoidalCategory C] [RigidCategory C] [MonoidalPreadditive C]
    [Linear k C] [MonoidalLinear k C] : Prop where
  /-- The endomorphism algebra of the monoidal unit is isomorphic to the base field `k` -/
  end_unit_iso : Nonempty (End (𝟙_ C) ≃ₐ[k] k)

class PreTannakian (k : Type*) [Field k] (C : Type u) [Category.{v, u} C] [Abelian C]
    [MonoidalCategory C] [SymmetricCategory C] [RigidCategory C] [Linear k C] [MonoidalLinear k C]
     : Prop extends WeakTensorCategory k C where
  /-- Every object `X` in `C` has finite length. That is, there exists a composition series
    for `X`. -/
  finite_length : ∀ (X : C), Nonempty (CompositionSeries (Subobject X))
