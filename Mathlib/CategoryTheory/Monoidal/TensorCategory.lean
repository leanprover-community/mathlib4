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

/-- Avoids `MonoidalPreadditive` in `PreTannakian`. -/
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
  i.e., hom spaces are finite dimensional and objects have finite length). -/
class WeakTensorCategory (k : Type*) [Field k] (C : Type u) [Category.{v, u} C] [Abelian C]
    [MonoidalCategory C] [RigidCategory C] [MonoidalPreadditive C]
    [Linear k C] [MonoidalLinear k C] : Prop where
  /-- The endomorphism algebra of the monoidal unit is isomorphic to the base field `k`. -/
  end_unit_iso : Nonempty (End (𝟙_ C) ≃ₐ[k] k)

/-- A length series for `X : C` in an abelian category `C` is a composition series which starts at
  `0` and ends at `X`. -/
structure Abelian.LengthSeries [Abelian C] (X : C) where
  s : CompositionSeries (Subobject X)
  head : s.head = ⊥ := by cat_disch
  last : s.last = ⊤ := by cat_disch

noncomputable
def Abelian.LengthSeries.trivial [Abelian C] (X : C) [IsSimpleSubobject X] :
    LengthSeries X where
  s := {
    length := 1
    toFun := fun i ↦ if i = 0 then ⊥ else ⊤
    step := by
      simp only [Nat.reduceAdd, Fin.isValue, Fin.castSucc_eq_zero_iff, Fin.succ_ne_zero, ↓reduceIte,
        Set.mem_setOf_eq, Fin.forall_fin_one]
      constructor
      · exact bot_lt_top
      · simp }

class PreTannakian (k : Type*) [Field k] (C : Type u) [Category.{v, u} C] [Abelian C]
    [MonoidalCategory C] [SymmetricCategory C] [RigidCategory C] [Linear k C] [MonoidalLinear k C]
     : Prop extends WeakTensorCategory k C where
  /-- Every object `X` in `C` has finite length, i.e., admits a composition series which starts
    at `⊥` and ends at `⊤`. -/
  finite_length : ∀ (X : C), Nonempty (Abelian.LengthSeries X)

section

open scoped MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

def tensorPower (X : C) : ℕ → C
  | 0 => 𝟙_ C -- junk value
  | n + 1 => Nat.rec X (fun _ Y => X ⊗ Y) n

scoped notation:80 X " ^⊗ " n:80 => tensorPower X n

end CategoryTheory.MonoidalCategory

end

noncomputable
def Abelian.length [Abelian C] : C → ℕ∞ := fun X ↦ ⨆ (S : LengthSeries X), S.s.length

class Abelian.HasModerateGrowth [Abelian C] [MonoidalCategory C] (X : C) where
  c : ℕ
  bounded (n : ℕ) : length (X^⊗n) ≤ c ^ n

class Abelian.ModerateGrowth [Abelian C] [MonoidalCategory C] where
  moderate_growth (X : C) : HasModerateGrowth X := by infer_instance
