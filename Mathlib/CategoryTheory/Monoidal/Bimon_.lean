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

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
A bimonoid object in a braided category `C` is an object that is simultaneously monoid and comonoid
objects, and structure morphisms of them satisfy appropriate consistency conditions.
-/
class BimonObj (M : C) extends MonObj M, ComonObj M where
  mul_comul (M) : μ[M] ≫ Δ[M] = (Δ[M] ⊗ₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ₘ μ[M]) := by cat_disch
  one_comul (M) : η[M] ≫ Δ[M] = η[M ⊗ M] := by cat_disch
  mul_counit (M) : μ[M] ≫ ε[M] = ε[M ⊗ M] := by cat_disch
  one_counit (M) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by cat_disch

@[deprecated (since := "2025-09-09")] alias Bimon_Class := BimonObj

namespace BimonObj

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end BimonObj

/-- The property that a morphism between bimonoid objects is a bimonoid morphism. -/
class IsBimonHom {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N) : Prop extends
    IsMonHom f, IsComonHom f

@[deprecated (since := "2025-09-15")] alias IsBimon_Hom := IsBimonHom

variable (C) in
/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon := Comon (Mon C)

@[deprecated (since := "2025-09-15")] alias Bimon_ := Bimon

namespace Bimon

instance : Category (Bimon C) := inferInstanceAs (Category (Comon (Mon C)))

@[ext] lemma ext {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon.Hom.ext (Mon.Hom.ext w)

@[simp] theorem id_hom' (M : Bimon C) : Comon.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon : Bimon C ⥤ Mon C := Comon.forget (Mon C)

@[deprecated (since := "2025-09-15")] alias toMon_ := toMon

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon C ⥤ C := toMon C ⋙ Mon.forget C

@[simp]
theorem toMon_forget : toMon C ⋙ Mon.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon : Bimon C ⥤ Comon C := (Mon.forget C).mapComon

@[deprecated (since := "2025-09-15")] alias toComon_ := toComon

@[simp]
theorem toComon_forget : toComon C ⋙ Comon.forget C = forget C := rfl

variable {C} in
/-- The object level part of the forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def toMonComonObj (M : Bimon C) : Mon (Comon C) where
  X := (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

@[deprecated (since := "2025-09-15")] alias toMon_Comon_obj := toMonComonObj

/-- The forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def toMonComon : Bimon C ⥤ Mon (Comon C) where
  obj := toMonComonObj
  map f := .mk' ((toComon C).map f)

@[deprecated (since := "2025-09-15")] alias toMon_Comon_ := toMonComon

variable {C}

/-- Auxiliary definition for `ofMonComonObj`. -/
@[simps! X]
def ofMonComonObjX (M : Mon (Comon C)) : Mon C := (Comon.forget C).mapMon.obj M

@[deprecated (since := "2025-09-15")] alias ofMon_Comon_ObjX := ofMonComonObjX

@[simp]
theorem ofMonComonObjX_one (M : Mon (Comon C)) :
    η[(ofMonComonObjX M).X] = 𝟙 (𝟙_ C) ≫ η[M.X].hom :=
  rfl

@[deprecated (since := "2025-09-15")] alias ofMon_Comon_ObjX_one := ofMonComonObjX_one

@[simp]
theorem ofMonComonObjX_mul (M : Mon (Comon C)) :
    μ[(ofMonComonObjX M).X] = 𝟙 (M.X.X ⊗ M.X.X) ≫ μ[M.X].hom :=
  rfl

@[deprecated (since := "2025-09-15")] alias ofMon_Comon_ObjX_mul := ofMonComonObjX_mul

attribute [local instance] ComonObj.instTensorUnit in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def tensorμ in
/-- The object level part of the backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def ofMonComonObj (M : Mon (Comon C)) : Bimon C where
  X := ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

@[deprecated (since := "2025-09-15")] alias ofMon_Comon_Obj := ofMonComonObj

@[deprecated (since := "2025-09-09")] alias Mon_Class.tensorObj.mul_def := MonObj.tensorObj.mul_def

variable (C) in
/-- The backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def ofMonComon : Mon (Comon C) ⥤ Bimon C where
  obj := ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

@[deprecated (since := "2025-09-15")] alias ofMon_Comon_ := ofMonComon

@[simp]
theorem toMonComon_ofMonComon_obj_one (M : Bimon C) :
    η[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

@[deprecated (since := "2025-09-15")]
alias toMon_Comon_ofMon_Comon_obj_one := toMonComon_ofMonComon_obj_one

@[simp]
theorem toMonComon_ofMonComon_obj_mul (M : Bimon C) :
    μ[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

@[deprecated (since := "2025-09-15")]
alias toMon_Comon_ofMon_Comon_obj_mul := toMonComon_ofMonComon_obj_mul

/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
def equivMonComonUnitIsoAppXAux (M : Bimon C) :
    M.X.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X.X :=
  Iso.refl _

@[deprecated (since := "2025-09-15")]
alias equivMon_Comon_UnitIsoAppXAux := equivMonComonUnitIsoAppXAux

instance (M : Bimon C) : IsMonHom (equivMonComonUnitIsoAppXAux M).hom where

/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
def equivMonComonUnitIsoAppX (M : Bimon C) :
    M.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X :=
 Mon.mkIso (equivMonComonUnitIsoAppXAux M)

@[deprecated (since := "2025-09-15")] alias equivMon_Comon_UnitIsoAppX := equivMonComonUnitIsoAppX

instance (M : Bimon C) : IsComonHom (equivMonComonUnitIsoAppX M).hom where

/-- The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
def equivMonComonUnitIsoApp (M : Bimon C) :
    M ≅ (toMonComon C ⋙ ofMonComon C).obj M :=
  Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[deprecated (since := "2025-09-15")] alias equivMon_Comon_UnitIsoApp := equivMonComonUnitIsoApp

@[simp]
theorem ofMonComon_toMonComon_obj_counit (M : Mon (Comon C)) :
    ε[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[deprecated (since := "2025-09-15")]
alias ofMon_Comon_toMon_Comon_obj_counit := ofMonComon_toMonComon_obj_counit

@[simp]
theorem ofMonComon_toMonComon_obj_comul (M : Mon (Comon C)) :
    Δ[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

@[deprecated (since := "2025-09-15")]
alias ofMon_Comon_toMon_Comon_obj_comul := ofMonComon_toMonComon_obj_comul

/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
def equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

@[deprecated (since := "2025-09-15")]
alias equivMon_Comon_CounitIsoAppXAux := equivMonComonCounitIsoAppXAux

instance (M : Mon (Comon C)) : IsComonHom (equivMonComonCounitIsoAppXAux M).hom where

/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
def equivMonComonCounitIsoAppX (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X ≅ M.X :=
  Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

@[deprecated (since := "2025-09-15")]
alias equivMon_Comon_CounitIsoAppX := equivMonComonCounitIsoAppX

instance (M : Mon (Comon C)) : IsMonHom (equivMonComonCounitIsoAppX M).hom where

/-- The counit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
def equivMonComonCounitIsoApp (M : Mon (Comon C)) :
    (ofMonComon C ⋙ toMonComon C).obj M ≅ M :=
 Mon.mkIso <| (equivMonComonCounitIsoAppX M)

@[deprecated (since := "2025-09-15")] alias equivMon_Comon_CounitIsoApp := equivMonComonCounitIsoApp

/-- The equivalence `Comon (Mon C) ≌ Mon (Comon C)` -/
def equivMonComon : Bimon C ≌ Mon (Comon C) where
  functor := toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

@[deprecated (since := "2025-09-15")] alias equivMon_Comon_ := equivMonComon

/-! # The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
def trivial : Bimon C := Comon.trivial (Mon C)

/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
def trivialTo (A : Bimon C) : trivial C ⟶ A :=
  .mk' (default : Mon.trivial C ⟶ A.X)

/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
def toTrivial (A : Bimon C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

/-! # Additional lemmas -/

theorem BimonObjAux_counit (M : Bimon C) :
    ε[((toComon C).obj M).X] = ε[M.X].hom :=
  Category.comp_id _

@[deprecated (since := "2025-09-09")] alias Bimon_ClassAux_counit := BimonObjAux_counit

theorem BimonObjAux_comul (M : Bimon C) :
    Δ[((toComon C).obj M).X] = Δ[M.X].hom :=
  Category.comp_id _

@[deprecated (since := "2025-09-09")] alias Bimon_ClassAux_comul := BimonObjAux_comul

instance (M : Bimon C) : BimonObj M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.counit_comul]
  comul_counit := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.comul_counit]
  comul_assoc := by
    simp_rw [← BimonObjAux_comul, ComonObj.comul_assoc]

attribute [local simp] MonObj.tensorObj.one_def in
@[reassoc]
theorem one_comul (M : C) [BimonObj M] :
    η[M] ≫ Δ[M] = (λ_ _).inv ≫ (η[M] ⊗ₘ η[M]) := by
  simp

@[reassoc]
theorem mul_counit (M : C) [BimonObj M] :
    μ[M] ≫ ε[M] = (ε[M] ⊗ₘ ε[M]) ≫ (λ_ _).hom := by
  simp

/-- Compatibility of the monoid and comonoid structures, in terms of morphisms in `C`. -/
@[reassoc (attr := simp)] theorem compatibility (M : C) [BimonObj M] :
    (Δ[M] ⊗ₘ Δ[M]) ≫
      (α_ _ _ (M ⊗ M)).hom ≫ M ◁ (α_ _ _ _).inv ≫
      M ◁ (β_ M M).hom ▷ M ≫
      M ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (μ[M] ⊗ₘ μ[M]) =
    μ[M] ≫ Δ[M] := by
  simp only [BimonObj.mul_comul, tensorμ, Category.assoc]

/-- Auxiliary definition for `Bimon.mk'`. -/
@[simps X]
def mk'X (X : C) [BimonObj X] : Mon C := { X := X }

/-- Construct an object of `Bimon C` from an object `X : C` and `BimonObj X` instance. -/
@[simps X]
def mk' (X : C) [BimonObj X] : Bimon C where
  X := mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X ⊗ X) }

end Bimon
end CategoryTheory
