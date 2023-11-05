/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.InvIsos

#align_import category_theory.closed.monoidal from "leanprover-community/mathlib"@"0caf3701139ef2e69c215717665361cda205a90b"

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/


universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

-- Note that this class carries a particular choice of right adjoint,
-- (which is only unique up to isomorphism),
-- not merely the existence of such, and
-- so definitional properties of instances may be important.
/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a left adjoint for `tensorLeft X` -/
  isAdj : IsLeftAdjoint (tensorLeft X)

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed : ∀ X : C, Closed X

attribute [instance 100] MonoidalClosed.closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X ⊗ Y) where
  isAdj := by
    haveI := hX.isAdj
    haveI := hY.isAdj
    exact Adjunction.leftAdjointOfNatIso (MonoidalCategory.tensorLeftTensor _ _).symm

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unitClosed : Closed (𝟙_ C) where
  isAdj :=
    { right := 𝟭 C
      adj :=
        Adjunction.mkOfHomEquiv
          { homEquiv := fun X _ =>
              { toFun := fun a => (leftUnitor X).inv ≫ a
                invFun := fun a => (leftUnitor X).hom ≫ a
                left_inv := by aesop_cat
                right_inv := by aesop_cat }
            homEquiv_naturality_left_symm := fun f g => by
              dsimp
              rw [leftUnitor_naturality_assoc]
            -- This used to be automatic before leanprover/lean4#2644
            homEquiv_naturality_right := by  -- aesop failure
              dsimp
              simp }}

variable (A B : C) {X X' Y Y' Z : C}

variable [Closed A]

/-- This is the internal hom `A ⟶[C] -`.
-/
def ihom : C ⥤ C :=
  (@Closed.isAdj _ _ _ A _).right

namespace ihom

/-- The adjunction between `A ⊗ -` and `A ⟹ -`. -/
def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.isAdj.adj

/-- The evaluation natural transformation. -/
def ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihom.adjunction A).counit

/-- The coevaluation natural transformation. -/
def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A :=
  (ihom.adjunction A).unit

@[simp]
theorem ihom_adjunction_counit : (ihom.adjunction A).counit = ev A :=
  rfl

@[simp]
theorem ihom_adjunction_unit : (ihom.adjunction A).unit = coev A :=
  rfl

@[reassoc (attr := simp)]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    (𝟙 A ⊗ (ihom A).map f) ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[reassoc (attr := simp)]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (𝟙 A ⊗ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the internal hom from `A` to `B` -/
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

@[reassoc (attr := simp)]
theorem ev_coev : (𝟙 A ⊗ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  Adjunction.left_triangle_components (ihom.adjunction A)

@[reassoc (attr := simp)]
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A)

end ihom

open CategoryTheory.Limits

instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjointPreservesColimits

variable {A}

-- Wrap these in a namespace so we don't clash with the core versions.
namespace MonoidalClosed

/-- Currying in a monoidal closed category. -/
def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X) :=
  (ihom.adjunction A).homEquiv _ _

/-- Uncurrying in a monoidal closed category. -/
def uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X) :=
  ((ihom.adjunction A).homEquiv _ _).symm

-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f :=
  rfl

-- This lemma has always been bad, but the linter only noticed after lean4#2644.
@[simp, nolint simpNF]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
    ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry ((𝟙 _ ⊗ f) ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihom _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
    uncurry (f ≫ g) = (𝟙 _ ⊗ f) ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.isAdj.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (𝟙 A ⊗ g) ≫ (ihom.ev A).app X :=
  Adjunction.homEquiv_counit _

theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  Adjunction.homEquiv_unit _

theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
  (Closed.isAdj.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
  (Closed.isAdj.adj.homEquiv _ _).symm.injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  rw [uncurry_eq, tensor_id, id_comp]

theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X := by
  rw [curry_eq, (ihom A).map_id (A ⊗ _)]
  apply comp_id

section Pre

variable {A B} [Closed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  transferNatTransSelf (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    (𝟙 B ⊗ (pre f).app X) ≫ (ihom.ev B).app X = (f ⊗ 𝟙 (A ⟶[C] X)) ≫ (ihom.ev A).app X :=
  transferNatTransSelf_counit _ _ ((tensoringLeft C).map f) X

@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = (f ⊗ 𝟙 _) ≫ (ihom.ev A).app X := by
  rw [uncurry_eq, id_tensor_pre_app_comp_ev]

@[reassoc (attr := simp)]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihom.coev B).app X ≫ (ihom B).map (f ⊗ 𝟙 _) :=
  unit_transferNatTransSelf _ _ ((tensoringLeft C).map f) X

@[simp]
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ := by
  simp only [pre, Functor.map_id]
  dsimp
  simp

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, transferNatTransSelf_comp, (tensoringLeft C).map_comp]

theorem pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C
    where
  obj X := ihom X.unop
  map f := pre f.unop

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

/-- Transport the property of being monoidal closed across a monoidal equivalence of categories -/
noncomputable def ofEquiv (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor]
    [h : MonoidalClosed D] : MonoidalClosed C where
  closed X :=
    { isAdj := by
        haveI q : Closed (F.obj X) := inferInstance
        haveI : IsLeftAdjoint (tensorLeft (F.obj X)) := q.isAdj
        have i := compInvIso (MonoidalFunctor.commTensorLeft F X)
        exact Adjunction.leftAdjointOfNatIso i }

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting currying map `Hom(X ⊗ Y, Z) → Hom(Y, (X ⟶[C] Z))`. (`X ⟶[C] Z` is defined to be
`F⁻¹(F(X) ⟶[D] F(Z))`, so currying in `C` is given by essentially conjugating currying in
`D` by `F.`) -/
theorem ofEquiv_curry_def (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor]
    [MonoidalClosed D] {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    @MonoidalClosed.curry _ _ _ _ _ _ ((MonoidalClosed.ofEquiv F).1 _) f =
      (F.1.1.adjunction.homEquiv Y ((ihom _).obj _))
        (MonoidalClosed.curry
          (F.1.1.inv.adjunction.homEquiv (F.1.1.obj X ⊗ F.1.1.obj Y) Z
            ((compInvIso (F.commTensorLeft X)).hom.app Y ≫ f))) :=
  rfl

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting uncurrying map `Hom(Y, (X ⟶[C] Z)) → Hom(X ⊗ Y ⟶ Z)`. (`X ⟶[C] Z` is
defined to be `F⁻¹(F(X) ⟶[D] F(Z))`, so uncurrying in `C` is given by essentially conjugating
uncurrying in `D` by `F.`) -/
theorem ofEquiv_uncurry_def (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor]
    [MonoidalClosed D] {X Y Z : C}
    (f : Y ⟶ (@ihom _ _ _ X <| (MonoidalClosed.ofEquiv F).1 X).obj Z) :
    @MonoidalClosed.uncurry _ _ _ _ _ _ ((MonoidalClosed.ofEquiv F).1 _) f =
      (compInvIso (F.commTensorLeft X)).inv.app Y ≫
        (F.1.1.inv.adjunction.homEquiv (F.1.1.obj X ⊗ F.1.1.obj Y) Z).symm
          (MonoidalClosed.uncurry
            ((F.1.1.adjunction.homEquiv Y ((ihom (F.1.1.obj X)).obj (F.1.1.obj Z))).symm f)) :=
  rfl
end OfEquiv

end MonoidalClosed
attribute [nolint simpNF] CategoryTheory.MonoidalClosed.homEquiv_apply_eq
  CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq
end CategoryTheory
