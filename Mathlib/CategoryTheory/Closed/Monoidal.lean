/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates

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
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed (X : C) : Closed X := by infer_instance

attribute [instance 100] MonoidalClosed.closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- If `X` and `Y` are closed then `X ⊗ Y` is.
This isn't an instance because it's not usually how we want to construct internal homs,
we'll usually prove all objects are closed uniformly.
-/
def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X ⊗ Y) where
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

/-- The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unitClosed : Closed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

variable (A B : C) {X X' Y Y' Z : C}
variable [Closed A]

/-- This is the internal hom `A ⟶[C] -`.
-/
def ihom : C ⥤ C :=
  Closed.rightAdj (X := A)

namespace ihom

/-- The adjunction between `A ⊗ -` and `A ⟹ -`. -/
def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.adj

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
    A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[reassoc (attr := simp)]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (A ◁ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the internal hom from `A` to `B` -/
notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

@[reassoc (attr := simp)]
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A) _

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
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g :=
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
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

-- I don't think these two should be simp.
theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (A ◁ g) ≫ (ihom.ev A).app X := by
  rfl

theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  rfl

theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
  (Closed.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  simp [uncurry_eq]

theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X := by
  rw [curry_eq, (ihom A).map_id (A ⊗ _)]
  apply comp_id

section Pre

variable {A B}
variable [Closed B]

/-- Pre-compose an internal hom with an external hom. -/
def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihom.ev A).app X := by
  simp [uncurry_eq]

@[reassoc (attr := simp)]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihom.coev B).app X ≫ (ihom B).map (f ▷ _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[simp]
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre, Functor.map_id]
  apply conjugateEquiv_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, (tensoringLeft C).map_comp]

theorem pre_comm_ihom_map {W X Y Z : C} [Closed W] [Closed X] (f : W ⟶ X) (g : Y ⟶ Z) :
    (pre f).app Y ≫ (ihom W).map g = (ihom X).map g ≫ (pre f).app Z := by simp

end Pre

/-- The internal hom functor given by the monoidal closed structure. -/
@[simps]
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihom X.unop
  map f := pre f.unop

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable (F : MonoidalFunctor C D) {G : D ⥤ C} (adj : F.toFunctor ⊣ G)
  [F.IsEquivalence] [MonoidalClosed D]
/-- Transport the property of being monoidal closed across a monoidal equivalence of categories -/
noncomputable def ofEquiv : MonoidalClosed C where
  closed X :=
    { rightAdj := F.toFunctor ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (MonoidalFunctor.commTensorLeft F X)) }

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting currying map `Hom(X ⊗ Y, Z) → Hom(Y, (X ⟶[C] Z))`. (`X ⟶[C] Z` is defined to be
`F⁻¹(F(X) ⟶[D] F(Z))`, so currying in `C` is given by essentially conjugating currying in
`D` by `F.`) -/
theorem ofEquiv_curry_def {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    letI := ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X ⊗ F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (MonoidalFunctor.commTensorLeft F X)).hom.app Y ≫ f))) := by
  -- This whole proof used to be `rfl` before #16317.
  change ((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _ _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- Suppose we have a monoidal equivalence `F : C ≌ D`, with `D` monoidal closed. We can pull the
monoidal closed instance back along the equivalence. For `X, Y, Z : C`, this lemma describes the
resulting uncurrying map `Hom(Y, (X ⟶[C] Z)) → Hom(X ⊗ Y ⟶ Z)`. (`X ⟶[C] Z` is
defined to be `F⁻¹(F(X) ⟶[D] F(Z))`, so uncurrying in `C` is given by essentially conjugating
uncurrying in `D` by `F.`) -/
theorem ofEquiv_uncurry_def {X Y Z : C} :
    letI := ofEquiv F adj
    ∀ (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (MonoidalFunctor.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalClosed.uncurry ((adj.homEquiv _ _).symm f)) := by
  intro f
  -- This whole proof used to be `rfl` before #16317.
  change (((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _).symm _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

end OfEquiv

end MonoidalClosed
attribute [nolint simpNF] CategoryTheory.MonoidalClosed.homEquiv_apply_eq
  CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq
end CategoryTheory
