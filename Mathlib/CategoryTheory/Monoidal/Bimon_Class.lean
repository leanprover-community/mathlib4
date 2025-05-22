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

class Bimon_Class (M : C) extends Mon_Class M, Comon_Class M where
  mul_comul : μ ≫ Δ = (Δ[M] ⊗ Δ[M]) ≫ tensorμ M M M M ≫ (μ ⊗ μ) := by aesop_cat
  one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := by aesop_cat
  mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := by aesop_cat
  one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_Class

-- show_panel_widgets [local Mathlib.Tactic.Widget.StringDiagram]

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

variable (M : C) [Bimon_Class M]

-- @[reassoc (attr := simp)]
-- theorem mul_comul : μ ≫ Δ = (Δ[M] ⊗ Δ[M]) ≫ tensor_μ C (M, M) (M, M) ≫ (μ ⊗ μ) := mul_comul'

-- @[reassoc (attr := simp)]
-- theorem one_comul : (η ≫ Δ : 𝟙_ C ⟶ M ⊗ M) = η := one_comul'

-- @[reassoc (attr := simp)]
-- theorem mul_counit : (μ ≫ ε : M ⊗ M ⟶ 𝟙_ C) = ε := mul_counit'

-- @[reassoc (attr := simp)]
-- theorem one_counit : (η : 𝟙_ C ⟶ M) ≫ ε = 𝟙 (𝟙_ C) := one_counit'

@[simps!]
instance (M : C) [Bimon_Class M] : Comon_Class (Mon_Cat.mk M) where
  counit := { hom := (ε : M ⟶ 𝟙_ C) }
  comul := { hom := (Δ : M ⟶ M ⊗ M) }

@[simps!]
instance (M : C) [Bimon_Class M] : Mon_Class (Comon_Cat.mk M) where
  one := { hom := (η : 𝟙_ C ⟶ M) }
  mul := { hom := (μ : M ⊗ M ⟶ M) }

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : C) [Bimon_Class M] [Bimon_Class N] where
  hom : M ⟶ N
  one_hom : η ≫ hom = η := by aesop_cat
  mul_hom : μ ≫ hom = (hom ⊗ hom) ≫ μ := by aesop_cat
  hom_counit : hom ≫ ε = ε := by aesop_cat
  hom_comul : hom ≫ Δ = Δ ≫ (hom ⊗ hom) := by aesop_cat

attribute [reassoc (attr := simp)] Hom.one_hom Hom.mul_hom Hom.hom_counit Hom.hom_comul

/-- The identity morphism on a monoid object. -/
@[simps]
def Hom.id (M : C) [Bimon_Class M] : Hom M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Bimon_Class M] : Inhabited (Hom M M) :=
  ⟨.id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def Hom.comp {M N O : C} [Bimon_Class M] [Bimon_Class N] [Bimon_Class O]
    (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

end Bimon_Class

variable (C)

/--
A bimonoid object in a braided category `C` is a comonoid object in the (monoidal)
category of monoid objects in `C`.
-/
def Bimon_Cat := Comon_Cat (Mon_Cat C)

namespace Bimon_Cat

variable {C}

instance : Category (Bimon_Cat C) := inferInstanceAs (Category (Comon_Cat (Mon_Cat C)))



def mk (M : C) [Bimon_Class M] : Bimon_Cat C where
  X := Mon_Cat.mk M

@[ext] lemma ext {X Y : Bimon_Cat C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon_ClassHom.ext (Mon_ClassHom.ext w)

@[simp] theorem id_hom' (M : Bimon_Cat C) : Comon_ClassHom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon_Cat C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMonCat : Bimon_Cat C ⥤ Mon_Cat C := Comon_Cat.forget (Mon_Cat C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Bimon_Cat C ⥤ C := toMonCat C ⋙ Mon_Cat.forget C

@[simp]
theorem toMonCatforget : toMonCat C ⋙ Mon_Cat.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComonCat : Bimon_Cat C ⥤ Comon_Cat C :=
  (Mon_Cat.forget C).mapComonCat

@[simp]
theorem toComonCat_forget : toComonCat C ⋙ Comon_Cat.forget C = forget C := rfl

open scoped Mon_Class Comon_Class

@[simps! (config := {isSimp := false})]
def Comon_ClassXX (M : Bimon_Cat C) : Comon_Class M.X.X :=
  inferInstanceAs (Comon_Class (((toComonCat C).obj M).X))

-- attribute [local instance] Comon_ClassXX in
-- theorem Comon_ClassXX_counit (M : Bimon_Cat C) : (ε : M.X.X ⟶ _) = (ε : M.X ⟶ _).hom := by
--   -- change _ = _ ≫ _
--   change _ ≫ _ = _
--   simp

-- @[simps?]
-- instance (M : Bimon_Cat C) : Comon_Class M.X.X where
--   counit := ε[M.X].hom
--   comul := Δ[M.X].hom
--   counit_comul' := by
--     rw [← Comon_ClassXX_counit, ← Comon_ClassXX_comul, Comon_Class.counit_comul]
--   comul_counit' := by
--     rw [← Comon_ClassXX_counit, ← Comon_ClassXX_comul, Comon_Class.comul_counit]
--   comul_assoc' := by
--     simp_rw [← Comon_ClassXX_comul, Comon_Class.comul_assoc]

-- attribute [local instance] Comon_ClassXX in
@[simps! (config := {isSimp := false}) comul counit]
-- attribute [local simp] Bimon_Cat.instComon_ClassXXMon_Cat in
instance isBimon_Class (M : Bimon_Cat C) : Bimon_Class M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← Comon_ClassXX_counit, ← Comon_ClassXX_comul]
    convert Comon_Class.counit_comul
  comul_counit := by
    rw [← Comon_ClassXX_counit, ← Comon_ClassXX_comul]
    convert Comon_Class.comul_counit
  comul_assoc := by
    simp_rw [← Comon_ClassXX_comul, Comon_Class.comul_assoc]
  -- one := _
  -- mul := _
  -- one_mul' := _
  -- mul_one' := _
  -- mul_assoc' := _
  -- __ := inferInstanceAs (Comon_Class (((toComonCat C).obj M).X))
  -- counit := ε[M.X.X]
  -- comul := _
  -- counit_comul' := _
  -- comul_counit' := _
  -- comul_assoc' := _
  -- mul_comul' := by
  --   simp
  -- one_comul' := _
  -- mul_counit' := _
  -- one_counit' := _

-- theorem aaaa (M : Bimon_Cat C) : (η : _ ⟶ M.X.X) = (η : _ ⟶ M.X.X) := by
-- change _ = _ ≫ _
--   rfl

/-- The object level part of the forward direction of
`Comon_Cat (Mon_Cat C) ≌ Mon_Cat (Comon_Cat C)` -/
@[simps!]
def toMonCatComonCatObj (M : C) [Bimon_Class M] : Mon_Cat (Comon_Cat C) where
  X := Comon_Cat.mk M

example {M N : Bimon_Cat C} (f : M ⟶ N) : ((toComonCat C).map f).hom = f.hom.hom := by
  rfl

variable {M N : Bimon_Cat C} (f : M ⟶ N)  in

-- set_option diagnostics true
-- example {M N : Bimon_Cat C} (f : M ⟶ N) : f.hom.hom ≫ ε = ε := by
--   simpa using ((toComonCat C).map f).hom_counit


-- #exit
-- attribute [simps!] toMonCatComonCatObj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_Cat (Mon_Cat C) ≌ Mon_Cat (Comon_Cat C)` -/
-- @[simps!? obj_X_X map_hom_hom]
def toMonCatComonCat : Bimon_Cat C ⥤ Mon_Cat (Comon_Cat C) where
  obj M := toMonCatComonCatObj C M.X.X
  map f := {
    hom := Comon_Cat.mkHom {
      hom := f.hom.hom
      hom_counit := by simpa [Comon_ClassXX_counit] using ((toComonCat C).map f).hom_counit
      hom_comul := by simpa [Comon_ClassXX_comul] using ((toComonCat C).map f).hom_comul } }

def toMonCatComonCatObjXX (M : Bimon_Cat C) : ((toMonCatComonCat C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

example {X₁ X₂ : Comon_Cat C} (f : X₁ ⟶ X₂) (X : Comon_Cat C) : (f ▷ X).hom = f.hom ▷ X.X := by
  rfl

-- set_option trace.profiler true in
@[simps! (config := {isSimp := false}) one mul]
instance (M : Comon_Cat C) [Mon_Class M] : Mon_Class M.X where
  one := η[M].hom
  mul := μ[M].hom
  one_mul := show ((η[M] ▷ M) ≫ μ[M]).hom = (λ_ M.X).hom from by rw [Mon_Class.one_mul]; simp
  mul_one := show (M ◁ η ≫ μ).hom = (ρ_ M.X).hom from by rw [Mon_Class.mul_one]; simp
  mul_assoc := show (μ ▷ M ≫ μ).hom = (α_ M.X M.X M.X).hom ≫ (M ◁ μ ≫ μ).hom from by
    rw [Mon_Class.mul_assoc]
    simp only [Comon_Class.instMonoidalCategoryComon_CatOfBraidedCategory_tensorObj_X,
      Comon_Cat.comp_hom',
      Comon_Class.instMonoidalCategoryComon_CatOfBraidedCategory_associator_hom_hom,
      Comon_Class.instMonoidalCategoryComon_CatOfBraidedCategory_whiskerLeft_hom]

attribute [local simp] instMon_ClassXOfComon_Cat_one instMon_ClassXOfComon_Cat_mul in
@[simps! (config := {isSimp := false}) mul one]
instance (M : Mon_Cat (Comon_Cat C)) : Bimon_Class M.X.X where

/-- The object level part of the backward direction of
`Comon_Cat (Mon_Cat C) ≌ Mon_Cat (Comon_Cat C)` -/
-- @[simps?]
def ofMonCatComonCatobj (M : C) [Bimon_Class M] : Bimon_Cat C where
  X := Mon_Cat.mk M

-- set_option diagnostics true
/-- The backward direction of `Comon_Cat (Mon_Cat C) ≌ Mon_Cat (Comon_Cat C)` -/
-- @[simps?! map]
def ofMonCatComonCat : Mon_Cat (Comon_Cat C) ⥤ Bimon_Cat C where
  obj M := ofMonCatComonCatobj C M.X.X
  map {M N} f :=
    { hom := Mon_Cat.mkHom {
        hom := f.hom.hom
        one_hom := by
          have := ((Comon_Cat.forget C).mapMonCat.map f).one_hom
          simp at this
          have : (𝟙 (𝟙_ C) ≫ η) ≫ f.hom.hom = 𝟙 (𝟙_ C) ≫ η :=
            ((Comon_Cat.forget C).mapMonCat.map f).one_hom
          simpa using this
        mul_hom := by
          have : (𝟙 _ ≫ μ) ≫ f.hom.hom = (f.hom.hom ⊗ f.hom.hom) ≫ 𝟙 _ ≫ μ :=
            ((Comon_Cat.forget C).mapMonCat.map f).mul_hom
          simpa using this }
      hom_comul := by aesop_cat
      hom_counit :=  by aesop_cat }
  map_id := by aesop_cat
  map_comp := by aesop_cat
  -- { hom := (Comon_Cat.forgetMonoidal C).mapMonCat.map f }

variable {C}

example (M : Bimon_Cat C) :
  (ε : ((toMonCatComonCat C).obj M).X.X ⟶ _) = (ε : M.X.X ⟶ 𝟙_ C) := by
  rfl

theorem extracted (M : Mon_Cat (Comon_Cat C)) : 𝟙 M.X.X ≫ ε = ε := by
  simp

@[simp]
theorem toMonCatComonCat_ofMonCatComonCat_X_X (M : Mon_Cat (Comon_Cat C)) :
    ((toMonCatComonCat C).obj ((ofMonCatComonCat C).obj M)).X.X = M.X.X := by
  rfl

@[simp]
theorem toComonCatMonCat_ofComonCatMonCat_X_X (M N : Mon_Cat (Comon_Cat C)) (f : M ⟶ N) :
    ((toMonCatComonCat C).map ((ofMonCatComonCat C).map f)).hom.hom = f.hom.hom := by
  rfl

@[simps!]
def equivMonCatComonCatUnitIsoAppX (M : Bimon_Cat C) :
    M.X ≅ ((toMonCatComonCat C ⋙ ofMonCatComonCat C).obj M).X :=
  Mon_Cat.mkIso' <| Mon_ClassIso.mk (Iso.refl M.X.X)

@[simps!]
def equivMonCatComonCatUnitIsoApp (M : Bimon_Cat C) :
    M ≅ (toMonCatComonCat C ⋙ ofMonCatComonCat C).obj M :=
  Comon_Cat.mkIso <| Comon_ClassIso.mk (equivMonCatComonCatUnitIsoAppX M)

@[simps!]
def equivMonCatComonCatCounitIsoAppX (M : Mon_Cat (Comon_Cat C)) :
    ((ofMonCatComonCat C ⋙ toMonCatComonCat C).obj M).X ≅ M.X :=
  Comon_Cat.mkIso' <| Comon_ClassIso.mk (Iso.refl M.X.X)
    -- (by simp)
    -- (by simp)

@[simps!]
def equivMonCatComonCatCounitIsoApp (M : Mon_Cat (Comon_Cat C)) :
    (ofMonCatComonCat C ⋙ toMonCatComonCat C).obj M ≅ M :=
  Mon_Cat.mkIso' <| Mon_ClassIso.mk (equivMonCatComonCatCounitIsoAppX M)

variable (C)

/-- The equivalence `Comon_Cat (Mon_Cat C) ≌ Mon_Cat (Comon_Cat C)` -/
def equivMonCatComonCat : Bimon_Cat C ≌ Mon_Cat (Comon_Cat C) where
  functor := toMonCatComonCat C
  inverse := ofMonCatComonCat C
  unitIso := NatIso.ofComponents equivMonCatComonCatUnitIsoApp
  counitIso := NatIso.ofComponents equivMonCatComonCatCounitIsoApp

end Bimon_Cat
