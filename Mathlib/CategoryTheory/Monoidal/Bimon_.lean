/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Some form of Tannaka reconstruction:
  given a monoidal functor `F : C ⥤ D` into a braided category `D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped Mon_Class Comon_Class

/--
A bimonoid object in a braided category `C` is a object that is simultaneously monoid and comonoid
objects, and structure morphisms of them satisfy appropriate consistency conditions.
-/
class Bimon_Class (M : C) extends Mon_Class M, Comon_Class M where
  mul_comul (M) : μ[M] ≫ Δ[M] = (Δ[M] ⊗ₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ₘ μ[M]) := by cat_disch
  one_comul (M) : η[M] ≫ Δ[M] = η[M ⊗ M] := by cat_disch
  mul_counit (M) : μ[M] ≫ ε[M] = ε[M ⊗ M] := by cat_disch
  one_counit (M) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by cat_disch

namespace Bimon_Class

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end Bimon_Class

/-- The property that a morphism between bimonoid objects is a bimonoid morphism. -/
class IsBimon_Hom {M N : C} [Bimon_Class M] [Bimon_Class N] (f : M ⟶ N) : Prop extends
    IsMon_Hom f, IsComon_Hom f

variable (C) in
/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_ := Comon_ (Mon_ C)

namespace Bimon_

instance : Category (Bimon_ C) := inferInstanceAs (Category (Comon_ (Mon_ C)))

@[ext] lemma ext {X Y : Bimon_ C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_.Hom.ext (Mon_.Hom.ext w)

@[simp] theorem id_hom' (M : Bimon_ C) : Comon_.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_ C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon_ : Bimon_ C ⥤ Mon_ C := Comon_.forget (Mon_ C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_ C ⥤ C := toMon_ C ⋙ Mon_.forget C

@[simp]
theorem toMon_forget : toMon_ C ⋙ Mon_.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon_ : Bimon_ C ⥤ Comon_ C := (Mon_.forget C).mapComon

@[simp]
theorem toComon_forget : toComon_ C ⋙ Comon_.forget C = forget C := rfl

variable {C} in
/-- The object level part of the forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_obj (M : Bimon_ C) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  mon :=
    { one := .mk' η[M.X.X]
      mul :=
        { hom := μ[M.X.X]
          is_comon_hom :=
            { hom_comul := by simp } } }

/-- The forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_ : Bimon_ C ⥤ Mon_ (Comon_ C) where
  obj := toMon_Comon_obj
  map f := .mk' ((toComon_ C).map f)

variable {C}

/-- Auxiliary definition for `ofMon_Comon_Obj`. -/
@[simps! X]
def ofMon_Comon_ObjX (M : Mon_ (Comon_ C)) : Mon_ C := (Comon_.forget C).mapMon.obj M

@[simp]
theorem ofMon_Comon_ObjX_one (M : Mon_ (Comon_ C)) :
    η[(ofMon_Comon_ObjX M).X] = 𝟙 (𝟙_ C) ≫ η[M.X].hom :=
  rfl

@[simp]
theorem ofMon_Comon_ObjX_mul (M : Mon_ (Comon_ C)) :
    μ[(ofMon_Comon_ObjX M).X] = 𝟙 (M.X.X ⊗ M.X.X) ≫ μ[M.X].hom :=
  rfl

attribute [local simp] Mon_Class.tensorObj.one_def Mon_Class.tensorObj.mul_def tensorμ in
/-- The object level part of the backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_Obj (M : Mon_ (Comon_ C)) : Bimon_ C where
  X := ofMon_Comon_ObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

variable (C) in
/-- The backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_ : Mon_ (Comon_ C) ⥤ Bimon_ C where
  obj := ofMon_Comon_Obj
  map f := .mk' ((Comon_.forget C).mapMon.map f)

@[simp]
theorem toMon_Comon_ofMon_Comon_obj_one (M : Bimon_ C) :
    η[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

@[simp]
theorem toMon_Comon_ofMon_Comon_obj_mul (M : Bimon_ C) :
    μ[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

/-- Auxiliary definition for `equivMon_Comon_UnitIsoApp`. -/
@[simps!]
def equivMon_Comon_UnitIsoAppXAux (M : Bimon_ C) :
    M.X.X ≅ ((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X :=
  Iso.refl _

instance (M : Bimon_ C) : IsMon_Hom (equivMon_Comon_UnitIsoAppXAux M).hom where

/-- Auxiliary definition for `equivMon_Comon_UnitIsoApp`. -/
@[simps!]
def equivMon_Comon_UnitIsoAppX (M : Bimon_ C) :
    M.X ≅ ((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X :=
  Mon_.mkIso (equivMon_Comon_UnitIsoAppXAux M)

instance (M : Bimon_ C) : IsComon_Hom (equivMon_Comon_UnitIsoAppX M).hom where

/-- The unit for the equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)`. -/
@[simps!]
def equivMon_Comon_UnitIsoApp (M : Bimon_ C) :
    M ≅ (toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M :=
  Comon_.mkIso' (equivMon_Comon_UnitIsoAppX M)

@[simp]
theorem ofMon_Comon_toMon_Comon_obj_counit (M : Mon_ (Comon_ C)) :
    ε[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem ofMon_Comon_toMon_Comon_obj_comul (M : Mon_ (Comon_ C)) :
    Δ[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

/-- Auxiliary definition for `equivMon_Comon_CounitIsoApp`. -/
@[simps!]
def equivMon_Comon_CounitIsoAppXAux (M : Mon_ (Comon_ C)) :
    ((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

instance (M : Mon_ (Comon_ C)) : IsComon_Hom (equivMon_Comon_CounitIsoAppXAux M).hom where

/-- Auxiliary definition for `equivMon_Comon_CounitIsoApp`. -/
@[simps!]
def equivMon_Comon_CounitIsoAppX (M : Mon_ (Comon_ C)) :
    ((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X ≅ M.X :=
  Comon_.mkIso' (equivMon_Comon_CounitIsoAppXAux M)

instance (M : Mon_ (Comon_ C)) : IsMon_Hom (equivMon_Comon_CounitIsoAppX M).hom where

/-- The counit for the equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)`. -/
@[simps!]
def equivMon_Comon_CounitIsoApp (M : Mon_ (Comon_ C)) :
    (ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M ≅ M :=
  Mon_.mkIso <| (equivMon_Comon_CounitIsoAppX M)

/-- The equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def equivMon_Comon_ : Bimon_ C ≌ Mon_ (Comon_ C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents equivMon_Comon_UnitIsoApp
  counitIso := NatIso.ofComponents equivMon_Comon_CounitIsoApp

/-! # The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
def trivial : Bimon_ C := Comon_.trivial (Mon_ C)

/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
def trivialTo (A : Bimon_ C) : trivial C ⟶ A :=
  .mk' (default : Mon_.trivial C ⟶ A.X)

/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
def toTrivial (A : Bimon_ C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon_ (Mon_ C)) _ A (Comon_.trivial (Mon_ C)))

/-! # Additional lemmas -/

theorem Bimon_ClassAux_counit (M : Bimon_ C) :
    ε[((toComon_ C).obj M).X] = ε[M.X].hom :=
  Category.comp_id _

theorem Bimon_ClassAux_comul (M : Bimon_ C) :
    Δ[((toComon_ C).obj M).X] = Δ[M.X].hom :=
  Category.comp_id _

instance (M : Bimon_ C) : Bimon_Class M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← Bimon_ClassAux_counit, ← Bimon_ClassAux_comul, Comon_Class.counit_comul]
  comul_counit := by
    rw [← Bimon_ClassAux_counit, ← Bimon_ClassAux_comul, Comon_Class.comul_counit]
  comul_assoc := by
    simp_rw [← Bimon_ClassAux_comul, Comon_Class.comul_assoc]

attribute [local simp] Mon_Class.tensorObj.one_def in
@[reassoc]
theorem one_comul (M : C) [Bimon_Class M] :
    η[M] ≫ Δ[M] = (λ_ _).inv ≫ (η[M] ⊗ₘ η[M]) := by
  simp

@[reassoc]
theorem mul_counit (M : C) [Bimon_Class M] :
    μ[M] ≫ ε[M] = (ε[M] ⊗ₘ ε[M]) ≫ (λ_ _).hom := by
  simp

/-- Compatibility of the monoid and comonoid structures, in terms of morphisms in `C`. -/
@[reassoc (attr := simp)] theorem compatibility (M : C) [Bimon_Class M] :
    (Δ[M] ⊗ₘ Δ[M]) ≫
      (α_ _ _ (M ⊗ M)).hom ≫ M ◁ (α_ _ _ _).inv ≫
      M ◁ (β_ M M).hom ▷ M ≫
      M ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (μ[M] ⊗ₘ μ[M]) =
    μ[M] ≫ Δ[M] := by
  simp only [Bimon_Class.mul_comul, tensorμ, Category.assoc]

/-- Auxiliary definition for `Bimon_.mk'`. -/
@[simps X]
def mk'X (X : C) [Bimon_Class X] : Mon_ C := { X := X }

/-- Construct an object of `Bimon_ C` from an object `X : C` and `Bimon_Class X` instance. -/
@[simps X]
def mk' (X : C) [Bimon_Class X] : Bimon_ C where
  X := mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X ⊗ X) }

end Bimon_
