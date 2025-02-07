/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_Class
import Mathlib.Tactic.Widget.StringDiagram

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Define Hopf monoids, which in a cartesian monoidal category are exactly group objects,
  and use this to define group schemes.
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

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable [BraidedCategory C]

open scoped Mon_Class Comon_Class

namespace copy

class Bimon_Class (M : C) extends Mon_Class M, Comon_Class M where
  mul_comul : μ ≫ Δ = (Δ[M] ⊗ Δ[M]) ≫ tensor_μ M M M M ≫ (μ ⊗ μ) := by aesop_cat
  one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := by aesop_cat
  mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := by aesop_cat
  one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_Class

-- show_panel_widgets [local Mathlib.Tactic.Widget.StringDiagram]
attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end Bimon_Class

variable (M : C) [Bimon_Class M]

-- @[reassoc (attr := simp)]
-- theorem mul_comul : μ ≫ Δ = (Δ ⊗ Δ) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := mul_comul'

-- @[reassoc (attr := simp)]
-- theorem one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := one_comul'

-- @[reassoc (attr := simp)]
-- theorem mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := mul_counit'

-- @[reassoc (attr := simp)]
-- theorem one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := one_counit'

/-- A morphism of comonoid objects. -/
@[ext]
structure Bimon_ClassHom (M N : C) [Bimon_Class M] [Bimon_Class N] extends
    Mon_ClassHom M N, Comon_ClassHom M N

attribute [reassoc (attr := simp)] Bimon_ClassHom.hom_counit Bimon_ClassHom.hom_comul

-- @[simps!? hom]
def Bimon_ClassHom.mk' {M N : C} [Bimon_Class M] [Bimon_Class N]
    (f : Mon_ClassHom M N) (f' : Comon_ClassHom M N) (hf : f.hom = f'.hom := by rfl) :
    Bimon_ClassHom M N where
  hom := f.hom
  one_hom := f.one_hom
  mul_hom := f.mul_hom
  hom_counit := hf ▸ f'.hom_counit
  hom_comul := hf ▸ f'.hom_comul

/-- The identity morphism on a monoid object. -/
@[simps]
def Bimon_ClassHom.id (M : C) [Bimon_Class M] : Bimon_ClassHom M M where
  hom := 𝟙 M

/-- Composition of morphisms of monoid objects. -/
@[simps]
def Bimon_ClassHom.comp {M N O : C} [Bimon_Class M] [Bimon_Class N] [Bimon_Class O]
    (f : Bimon_ClassHom M N) (g : Bimon_ClassHom N O) : Bimon_ClassHom M O where
  hom := f.hom ≫ g.hom

@[ext]
structure Bimon_ClassIso (M N : C) [Bimon_Class M] [Bimon_Class N] extends
    Mon_ClassIso M N, Comon_ClassIso M N where

initialize_simps_projections Bimon_ClassIso (-hom, -inv, +toIso)

attribute [reassoc (attr := simp)] Bimon_ClassIso.hom_counit Bimon_ClassIso.hom_comul

variable {M N : C} [Bimon_Class M] [Bimon_Class N]

@[simps]
def Bimon_ClassIso.mk'
    (iso : M ≅ N)
    (one_hom : η ≫ iso.hom = η := by aesop_cat)
    (mul_hom : μ ≫ iso.hom = (iso.hom ⊗ iso.hom) ≫ μ := by aesop_cat)
    (hom_counit : iso.hom ≫ ε = ε := by aesop_cat)
    (hom_comul : iso.hom ≫ Δ = Δ ≫ (iso.hom ⊗ iso.hom) := by aesop_cat) :
    Bimon_ClassIso M N where
  hom := iso.hom
  inv := iso.inv

@[simps!]
def Bimon_ClassIso.symm (f : Bimon_ClassIso M N) :
    Bimon_ClassIso N M where
  toMon_ClassIso := f.toMon_ClassIso.symm
  hom_counit := f.toComon_ClassIso.symm.hom_counit
  hom_comul := f.toComon_ClassIso.symm.hom_comul

@[simps]
def Bimon_ClassIso.toBimon_ClassHom (f : Bimon_ClassIso M N) : Bimon_ClassHom M N where
  hom := f.hom

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
structure Bimon_Cat (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C] where
  X : C
  [isBimon_Class : Bimon_Class X]

namespace Bimon_Cat

-- variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
-- variable [BraidedCategory C]

attribute [instance] Bimon_Cat.isBimon_Class

instance : Category (Bimon_Cat C) where
  Hom M N := Bimon_ClassHom M.X N.X
  id M := Bimon_ClassHom.id M.X
  comp f g := Bimon_ClassHom.comp f g

def mkHom (f : Bimon_ClassHom M N ) : mk M ⟶ mk N := f

@[simp]
theorem mkHom_hom (f : Bimon_ClassHom M N) : (mkHom f).hom = f.hom := rfl

@[ext] lemma ext {X Y : Bimon_Cat C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g :=
  Bimon_ClassHom.ext w

@[simp] theorem id_hom' (M : Bimon_Cat C) : (𝟙 M : Bimon_ClassHom M.X M.X).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_Cat C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[simps]
def mkIso {X Y : C} [Bimon_Class X] [Bimon_Class Y] (f : Bimon_ClassIso X Y) :
    mk X ≅ mk Y where
  hom := mkHom f.toBimon_ClassHom
  inv := mkHom f.symm.toBimon_ClassHom

@[simps!]
def mkIso' {X Y : Bimon_Cat C} (f : Bimon_ClassIso X.X Y.X) :
    X ≅ Y :=
  mkIso f

variable (C)

-- /-- The forgetful functor from bimonoid objects to monoid objects. -/
-- abbrev toMonCat : Comon_Cat (Mon_Cat C) ⥤ Mon_Cat C := Comon_Cat.forget (Mon_Cat C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_Cat C ⥤ C where
  obj M := M.X
  map f := f.hom

open scoped Mon_Class Comon_Class

def toComonCat : Bimon_Cat C ⥤ Comon_Cat C where
  obj M := { X := M.X }
  map f := { hom := f.hom }

@[simp]
theorem toComonCat_forget : toComonCat C ⋙ Comon_Cat.forget C = forget C := rfl

@[simps!]
instance (M : C) [Bimon_Class M] : Mon_Class (Comon_Cat.mk M) where
  one := { hom := (η : 𝟙_ C ⟶ M) }
  mul := { hom := (μ : M ⊗ M ⟶ M) }

instance (M : Bimon_Cat C) : Mon_Class ((toComonCat C).obj M) :=
  inferInstanceAs <| Mon_Class (Comon_Cat.mk M.X)

/-- The forward direction of `Bimon_Cat C ≌ Mon_Cat (Comon_Cat C)` -/
def toMonCatComonCat : Bimon_Cat C ⥤ Mon_Cat (Comon_Cat C) where
  obj M := { X := (toComonCat C).obj M }
  map f := { hom := Comon_Cat.mkHom f.toComon_ClassHom }

def toMonCat : Bimon_Cat C ⥤ Mon_Cat C where
  obj M := { X := M.X }
  map f := { hom := f.hom }

@[simp]
def toMonCatforget : toMonCat C ⋙ Mon_Cat.forget C = forget C := rfl

@[simps!]
instance (M : C) [Bimon_Class M] : Comon_Class (Mon_Cat.mk M) where
  counit := { hom := (ε : M ⟶ 𝟙_ C) }
  comul := { hom := (Δ : M ⟶ M ⊗ M) }

instance (M : Bimon_Cat C) : Comon_Class ((toMonCat C).obj M) :=
  inferInstanceAs <| Comon_Class (Mon_Cat.mk M.X)

/-- The forward direction of `Bimon_Cat C ≌ Comon_Cat (Mon_Cat C)` -/
def toComonCatMonCat : Bimon_Cat C ⥤ Comon_Cat (Mon_Cat C) where
  obj M := { X := (toMonCat C).obj M }
  map f := { hom := Mon_Cat.mkHom f.toMon_ClassHom }

@[simps!]
instance (M : Comon_Cat C) [Mon_Class M] : Mon_Class M.X :=
  inferInstanceAs (Mon_Class ((Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.obj M))

@[simps!]
instance (M : Mon_Cat C) [Comon_Class M] : Comon_Class M.X :=
  inferInstanceAs (Comon_Class ((Mon_Cat.forgetMonoidal C).toOplaxMonoidalFunctor.obj M))

instance (M : Mon_Cat (Comon_Cat C)) : Bimon_Class M.X.X where

instance (M : Comon_Cat (Mon_Cat C)) : Bimon_Class M.X.X where

-- @[simps! map]
def MonCatComonCatToMonCat : Mon_Cat (Comon_Cat C) ⥤ Mon_Cat C :=
  (Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMonCat

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
-- @[simps!? map]
def ComonCatMonCatToComonCat : Comon_Cat (Mon_Cat C) ⥤ Comon_Cat C :=
  (Mon_Cat.forgetMonoidal C).toOplaxMonoidalFunctor.mapComonCat

/-- The backward direction of `Bimon_Cat C ≌ Mon_Cat (Comon_Cat C)` -/
def ofMonCatComonCat : Mon_Cat (Comon_Cat C) ⥤ Bimon_Cat C where
  obj M := { X := M.X.X }
  map f := Bimon_Cat.mkHom <| Bimon_ClassHom.mk' ((MonCatComonCatToMonCat C).map f) f.hom
    -- hom := f.hom.hom
    -- one_hom := ((Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMonCat.map f).one_hom
    -- mul_hom := ((Comon_Cat.forgetMonoidal C).toLaxMonoidalFunctor.mapMonCat.map f).mul_hom }

/-- The backward direction of `Bimon_Cat C ≌ Comon_Cat (Mon_Cat C)` -/
def ofComonCatMonCat : Comon_Cat (Mon_Cat C) ⥤ Bimon_Cat C where
  obj M := { X := M.X.X }
  map f := Bimon_Cat.mkHom <| Bimon_ClassHom.mk' f.hom ((ComonCatMonCatToComonCat C).map f)
    -- hom := ((toComonCat C).map f).hom
    -- hom_counit := ((toComonCat C).map f).hom_counit
    -- hom_comul := ((toComonCat C).map f).hom_comul }

variable {C}

@[simp]
theorem toMonCatComonCat_ofMonCatComonCat_X_X (M : Mon_Cat (Comon_Cat C)) :
    ((toMonCatComonCat C).obj ((ofMonCatComonCat C).obj M)).X.X = M.X.X := by
  rfl

-- @[simp]
-- theorem toMonCatComonCat_ofMonCatComonCat_hom_hom (M N : Mon_Cat (Comon_Cat C)) (f : M ⟶ N) :
--     ((toMonCatComonCat C).map ((ofMonCatComonCat C).map f)).hom.hom = f.hom.hom := by
--   rfl

@[simp]
theorem toComonCatMonCat_ofComonCatMonCat_X_X (M : Comon_Cat (Mon_Cat C)) :
    ((toComonCatMonCat C).obj ((ofComonCatMonCat C).obj M)).X.X = M.X.X := by
  rfl

-- @[simp]
-- theorem toComonCatMonCat_ofComonCatMonCat_hom_hom (M N : Comon_Cat (Mon_Cat C)) (f : M ⟶ N) :
--     ((toComonCatMonCat C).map ((ofComonCatMonCat C).map f)).hom.hom = f.hom.hom := by
--   rfl

@[simps!]
def equivMonCatComonCatUnitIsoApp (M : Bimon_Cat C) :
    M ≅ (toMonCatComonCat C ⋙ ofMonCatComonCat C).obj M :=
  Bimon_Cat.mkIso' <| Bimon_ClassIso.mk' (Iso.refl M.X)

@[simps!]
def equivMonCatComonCatCounitIsoApp (M : Mon_Cat (Comon_Cat C)) :
    (ofMonCatComonCat C ⋙ toMonCatComonCat C).obj M ≅ M :=
  Mon_Cat.mkIso' <| Mon_ClassIso.mk (Iso.refl M.X)

variable (C) in
/-- The equivalence `Bimon_Cat C ≌ Mon_Cat (Comon_Cat C)` -/
def equivMonCatComonCat : Bimon_Cat C ≌ Mon_Cat (Comon_Cat C) where
  functor := toMonCatComonCat C
  inverse := ofMonCatComonCat C
  unitIso := NatIso.ofComponents equivMonCatComonCatUnitIsoApp
  counitIso := NatIso.ofComponents equivMonCatComonCatCounitIsoApp

@[simps!]
def equivComonCatMonCatUnitIsoApp (M : Bimon_Cat C) :
    M ≅ (toComonCatMonCat C ⋙ ofComonCatMonCat C).obj M :=
  Bimon_Cat.mkIso' <| Bimon_ClassIso.mk' (Iso.refl M.X)

@[simps!]
def equivComonCatMonCatCounitIsoApp (M : Comon_Cat (Mon_Cat C)) :
    (ofComonCatMonCat C ⋙ toComonCatMonCat C).obj M ≅ M :=
  Comon_Cat.mkIso' <| Comon_ClassIso.mk (Iso.refl M.X)

variable (C) in

/-- The equivalence `Bimon_Cat C ≌ Comon_Cat (Mon_Cat C)` -/
def equivComonCatMonCat : Bimon_Cat C ≌ Comon_Cat (Mon_Cat C) where
  functor := toComonCatMonCat C
  inverse := ofComonCatMonCat C
  unitIso := NatIso.ofComponents equivComonCatMonCatUnitIsoApp
  counitIso := NatIso.ofComponents equivComonCatMonCatCounitIsoApp

end Bimon_Cat

end copy
