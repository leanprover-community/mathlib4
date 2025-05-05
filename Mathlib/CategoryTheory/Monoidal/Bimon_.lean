/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.Tactic.Widget.StringDiagram

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
  /- For the names of the conditions below, the unprimed names are reserved for the version where
  the argument `M` is explicit. -/
  mul_comul' : μ[M] ≫ Δ[M] = (Δ[M] ⊗ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ μ[M]) := by aesop_cat
  one_comul' : η[M] ≫ Δ[M] = η[M ⊗ M] := by aesop_cat
  mul_counit' : μ[M] ≫ ε[M] = ε[M ⊗ M] := by aesop_cat
  one_counit' : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by aesop_cat

namespace Bimon_Class

/- The simp attribute is reserved for the unprimed versions. -/
attribute [reassoc] mul_comul' one_comul' mul_counit' one_counit'

variable (M : C) [Bimon_Class M]

@[reassoc (attr := simp)]
theorem mul_comul (M : C) [Bimon_Class M] :
    μ[M] ≫ Δ[M] = (Δ[M] ⊗ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ μ[M]) :=
  mul_comul'

@[reassoc (attr := simp)]
theorem one_comul (M : C) [Bimon_Class M] : η[M] ≫ Δ[M] = η[M ⊗ M] := one_comul'

@[reassoc (attr := simp)]
theorem mul_counit (M : C) [Bimon_Class M] : μ[M] ≫ ε[M] = ε[M ⊗ M] := mul_counit'

@[reassoc (attr := simp)]
theorem one_counit (M : C) [Bimon_Class M] : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := one_counit'

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
def toMon_Comon_obj (M : Bimon_ C) : Mon_ (Comon_ C) where
  X := (toComon_ C).obj M
  one := { hom := η[M.X.X] }
  mul :=
  { hom := μ[M.X.X],
    hom_comul := by dsimp; simp [tensor_μ] }

attribute [simps] toMon_Comon_obj -- We add this after the fact to avoid a timeout.

/-- The forward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def toMon_Comon_ : Bimon_ C ⥤ Mon_ (Comon_ C) where
  obj := toMon_Comon_obj
  map f :=
  { hom := (toComon_ C).map f }

variable {C}

def toMonCatComonCatObjXX (M : Bimon_ C) : ((toMon_Comon_ C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

example {X₁ X₂ : Comon_ C} (f : X₁ ⟶ X₂) (X : Comon_ C) : (f ▷ X).hom = f.hom ▷ X.X := by
  rfl

-- set_option trace.profiler true in
@[simps! (config := {isSimp := false}) one mul]
instance (M : Comon_ C) [Mon_Class M] : Mon_Class M.X where
  one := η[M].hom
  mul := μ[M].hom
  one_mul' := show ((η[M] ▷ M) ≫ μ[M]).hom = (λ_ M.X).hom from by rw [Mon_Class.one_mul]; simp
  mul_one' := show (M ◁ η ≫ μ).hom = (ρ_ M.X).hom from by rw [Mon_Class.mul_one]; simp
  mul_assoc' := show (μ ▷ M ≫ μ).hom = (α_ M.X M.X M.X).hom ≫ (M ◁ μ ≫ μ).hom from by
    rw [Mon_Class.mul_assoc]
    simp

-- instance (M : Mon_ (Comon_ C)) : IsComon_Hom η[((Comon_.forget C).mapMon.obj M).X] where
  -- hom_counit := _
  -- hom_comul := _

-- attribute [local simp] instMon_ClassXOfComon_Cat_one instMon_ClassXOfComon_Cat_mul in
-- @[simps! (config := {isSimp := false}) mul one]
-- example (M : Mon_ (Comon_ C)) : Bimon_Class M.X.X where

def ofMon_Comon_objAux (M : Mon_ (Comon_ C)) : Bimon_Class M.X.X where
  -- one := η[M.X.X]
  -- mul := μ[M]
  -- comul := Δ[M.X.X]
  -- counit := ε[M.X.X]
  one_comul' := by
    dsimp
    simp [instMon_ClassXOfComon__one]
  mul_comul' := by dsimp [instMon_ClassXOfComon__mul]; simp
  mul_counit' := by dsimp [instMon_ClassXOfComon__mul]; simp
  one_counit' := by dsimp [instMon_ClassXOfComon__one]; simp

/-- The object level part of the backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_obj (M : Mon_ (Comon_ C)) : Bimon_ C where
  X := (Comon_.forget C).mapMon.obj M
  counit := {
    hom := ε[M.X.X]
    one_hom := by dsimp; simp only [Category.id_comp, IsComon_Hom.hom_counit,
      Comon_Class.instTensorUnit_counit]
     }
  comul :=
  { hom := Δ[M.X.X]
    mul_hom := by dsimp; simp [tensorμ] }

variable (C) in
/-- The backward direction of `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
@[simps]
def ofMon_Comon_ : Mon_ (Comon_ C) ⥤ Bimon_ C where
  obj := ofMon_Comon_obj
  map f :=
  { hom := (Comon_.forget C).mapMon.map f }

-- @[simp]
-- theorem toMon_Comon_ofMon_Comon_X_X (M : Mon_ (Comon_ C)) :
--     ((toMon_Comon_ C).obj ((ofMon_Comon_ C).obj M)).X.X = M.X.X := by
--   rfl

@[simp]
theorem toComon_MonCat_ofComon_Mon_X_X (M N : Mon_ (Comon_ C)) (f : M ⟶ N) :
    ((toMon_Comon_ C).map ((ofMon_Comon_ C).map f)).hom.hom = f.hom.hom := by
  rfl

-- instance (M : Bimon_ C) : IsMon_Hom (Iso.refl M.X.X).hom :=
--   inferInstanceAs (IsMon_Hom (𝟙 M.X.X))

@[simp]
theorem equivMon_Comon_UnitIsoAppX_aux_one (M : Bimon_ C) :
    η[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

@[simp]
theorem equivMon_Comon_UnitIsoAppX_aux_mul (M : Bimon_ C) :
    μ[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

@[simp]
theorem equivMon_Comon_UnitIsoAppX_aux_counit (M : Bimon_ C) :
    ε[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X].hom = ε[M.X].hom ≫ 𝟙 _ :=
  rfl

@[simp]
theorem equivMon_Comon_UnitIsoAppX_aux_comul (M : Bimon_ C) :
    Δ[((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X].hom = Δ[M.X].hom ≫ 𝟙 _ :=
  rfl

@[simps!]
def equivMon_Comon_UnitIsoAppXAux (M : Bimon_ C) :
    M.X.X ≅ ((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X.X :=
  Iso.refl _

instance (M : Bimon_ C) : IsMon_Hom (equivMon_Comon_UnitIsoAppXAux M).hom where

@[simps!]
def equivMon_Comon_UnitIsoAppX (M : Bimon_ C) :
    M.X ≅ ((toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M).X :=
  Mon_.mkIso' (equivMon_Comon_UnitIsoAppXAux M)

instance (M : Bimon_ C) : IsComon_Hom (equivMon_Comon_UnitIsoAppX M).hom where

@[simps!]
def equivMon_Comon_UnitIsoApp (M : Bimon_ C) :
    M ≅ (toMon_Comon_ C ⋙ ofMon_Comon_ C).obj M :=
  Comon_.mkIso' (equivMon_Comon_UnitIsoAppX M)
  -- Comon_ClassIso.mk (equivMon_Comon_UnitIsoAppX M)

@[simps!]
def equivMon_Comon_CounitIsoAppXAux (M : Mon_ (Comon_ C)) :
    ((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

@[simp]
theorem equivMon_Comon_CounitIsoAppXAux_one_hom (M : Mon_ (Comon_ C)) :
    η[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X].hom = 𝟙 _ ≫ η[M.X].hom :=
  rfl

@[simp]
theorem equivMon_Comon_CounitIsoAppXAux_mul_hom (M : Mon_ (Comon_ C)) :
    μ[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X].hom = 𝟙 _ ≫ μ[M.X].hom :=
  rfl

@[simp]
theorem equivMon_Comon_CounitIsoAppXAux_hom_counit (M : Mon_ (Comon_ C)) :
    ε[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem equivMon_Comon_CounitIsoAppXAux_hom_comul (M : Mon_ (Comon_ C)) :
    Δ[((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

instance (M : Mon_ (Comon_ C)) : IsComon_Hom (equivMon_Comon_CounitIsoAppXAux M).hom where

@[simps!]
def equivMon_Comon_CounitIsoAppX (M : Mon_ (Comon_ C)) :
    ((ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M).X ≅ M.X :=
  Comon_.mkIso' (equivMon_Comon_CounitIsoAppXAux M)
    -- (by simp)
    -- (by simp)

instance (M : Mon_ (Comon_ C)) : IsMon_Hom (equivMon_Comon_CounitIsoAppX M).hom where

@[simps!]
def equivMon_Comon_CounitIsoApp (M : Mon_ (Comon_ C)) :
    (ofMon_Comon_ C ⋙ toMon_Comon_ C).obj M ≅ M :=
  Mon_.mkIso' <| (equivMon_Comon_CounitIsoAppX M)

/-- The equivalence `Comon_ (Mon_ C) ≌ Mon_ (Comon_ C)` -/
def equivMon_Comon_ : Bimon_ C ≌ Mon_ (Comon_ C) where
  functor := toMon_Comon_ C
  inverse := ofMon_Comon_ C
  unitIso := NatIso.ofComponents (fun _ => equivMon_Comon_UnitIsoApp _)
  counitIso := NatIso.ofComponents (fun _ => equivMon_Comon_CounitIsoApp _)

/-! # The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
def trivial : Bimon_ C := Comon_.trivial (Mon_ C)

/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
def trivialTo (A : Bimon_ C) : trivial C ⟶ A :=
  { hom := (default : Mon_.trivial C ⟶ A.X), }

@[deprecated (since := "2024-12-07")] alias trivial_to := trivialTo
@[deprecated (since := "2024-12-07")] alias trivial_to_hom := trivialTo_hom

/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
def toTrivial (A : Bimon_ C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon_ (Mon_ C)) _ A (Comon_.trivial (Mon_ C)))

@[deprecated (since := "2024-12-07")] alias to_trivial := toTrivial
@[deprecated (since := "2024-12-07")] alias to_trivial_hom := toTrivial_hom

/-! # Additional lemmas -/

-- variable {C}

-- variable (C) in

-- /-- The forgetful functor from bimonoid objects to comonoid objects. -/
-- @[simps!]
-- def toComon : Bimon_ C ⥤ Comon_ C :=
--   (Mon_.forget C).mapComon

-- @[simp]
-- theorem toComonCat_forget : toComon C ⋙ Comon_.forget C = forget C := rfl

-- @[simps!? (config := {isSimp := false, fullyApplied := false})]
def Bimon_ClassAux (M : Bimon_ C) : Comon_Class M.X.X :=
  inferInstanceAs (Comon_Class (((toComon_ C).obj M).X))

theorem Bimon_ClassAux_counit (M : Bimon_ C) :
    letI : Comon_Class M.X.X := Bimon_ClassAux M
    ε[M.X.X] = ε[M.X].hom :=
  Category.comp_id _

theorem Bimon_ClassAux_comul (M : Bimon_ C) :
    letI : Comon_Class M.X.X := Bimon_ClassAux M
    Δ[M.X.X] = Δ[M.X].hom :=
  Category.comp_id _

@[simps!?]
instance (M : Bimon_ C) : Bimon_Class M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul' := by
    letI : Comon_Class M.X.X := Bimon_ClassAux M
    rw [← Bimon_ClassAux_counit, ← Bimon_ClassAux_comul, Comon_Class.counit_comul]
  comul_counit' := by
    letI : Comon_Class M.X.X := Bimon_ClassAux M
    rw [← Bimon_ClassAux_counit, ← Bimon_ClassAux_comul, Comon_Class.comul_counit]
  comul_assoc' := by
    simp_rw [← Bimon_ClassAux_comul, Comon_Class.comul_assoc]

@[reassoc]
theorem one_comul (M : C) [Bimon_Class M] :
    η[M] ≫ Δ[M] = (λ_ _).inv ≫ (η[M] ⊗ η[M]) := by
  simp only [Bimon_Class.one_comul, Mon_Class.instTensorObj_one]

@[reassoc]
theorem mul_counit (M : C) [Bimon_Class M] :
    μ[M] ≫ ε[M] = (ε[M] ⊗ ε[M]) ≫ (λ_ _).hom := by
  simp only [Bimon_Class.mul_counit, Comon_.instComon_ClassTensorObj_counit]

/-- Compatibility of the monoid and comonoid structures, in terms of morphisms in `C`. -/
@[reassoc (attr := simp)] theorem compatibility (M : C) [Bimon_Class M] :
    (Δ[M] ⊗ Δ[M]) ≫
      (α_ _ _ (M ⊗ M)).hom ≫ M ◁ (α_ _ _ _).inv ≫
      M ◁ (β_ M M).hom ▷ M ≫
      M ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (μ[M] ⊗ μ[M]) =
    μ[M] ≫ Δ[M] := by
  simp only [Bimon_Class.mul_comul, tensorμ, Category.assoc]

set_option linter.hashCommand false in
#string_diagram compatibility

end Bimon_
