/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

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

@[expose] public section

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

namespace BimonObj

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end BimonObj

/-- The property that a morphism between bimonoid objects is a bimonoid morphism. -/
class IsBimonHom {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N) : Prop extends
    IsMonHom f, IsComonHom f

attribute [local instance] ComonObj.instTensorUnit in
instance : BimonObj (𝟙_ C) where
  mul_comul := by
    simp only [MonObj.mul_def, ComonObj.instTensorUnit_comul, tensorμ, braiding_tensorUnit_right]
    monoidal_coherence
  one_comul := by
    simp only [MonObj.one_def, ComonObj.instTensorUnit_comul, Category.id_comp,
    MonObj.tensorObj.one_def]
    monoidal_coherence
  mul_counit := by simp
  one_counit := by simp

variable (C) in
/--
The category of bimonoid objects in a braided category `C`.
-/
structure Bimon where
  /-- The underlying object in the ambient braided category -/
  X : C
  [bimon : BimonObj X]

attribute [instance] Bimon.bimon

namespace Bimon

variable (C) in
/-- The trivial bimonoid object. We later show this is initial in `Bimon C`.
-/
@[simps!]
def trivial : Bimon C := mk (𝟙_ C)

instance : Inhabited (Bimon C) :=
  ⟨trivial C⟩

/-- A morphism of monoid objects. -/
@[ext]
structure Hom (M N : Bimon C) where
  /-- The underlying morphism -/
  hom : M.X ⟶ N.X
  [isBimonHom_hom : IsBimonHom hom]

attribute [instance] Bimon.Hom.isBimonHom_hom

/-- Construct a morphism `M ⟶ N` of `Mon C` from a map `f : M ⟶ N` and a `IsMonHom f` instance. -/
abbrev Hom.mk' {M N : Bimon C} (f : M.X ⟶ N.X)
    (one_f : η ≫ f = η := by cat_disch)
    (mul_f : μ ≫ f = (f ⊗ₘ f) ≫ μ := by cat_disch)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) : Hom M N :=
  have : IsMonHom f := ⟨one_f, mul_f⟩
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  have : IsBimonHom f := ⟨⟩
  .mk f

instance (X : C) [BimonObj X] : IsBimonHom (𝟙 X) := ⟨⟩
instance (X Y Z : C) [BimonObj X] [BimonObj Y] [BimonObj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsBimonHom f] [IsBimonHom g] : IsBimonHom (f ≫ g) := ⟨⟩

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Bimon C) : Hom M M := ⟨𝟙 M.X⟩

instance homInhabited (M : Bimon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Bimon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom

instance : Category (Bimon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g

/-- Construct a morphism `Bimon.mk G ⟶ Bimon.mk H` from a  map `f : G ⟶ H` and a `IsBimonHom f`
instance. -/
@[simps!]
def ofHom {A B : C} [BimonObj A] [BimonObj B] (f : A ⟶ B) [IsBimonHom f] :
    Bimon.mk A ⟶ Bimon.mk B := .mk f

@[ext] lemma ext {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w

@[simp] theorem id_hom' (M : Bimon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

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

end Bimon

/-! ### Functoriality -/

namespace Functor

variable {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]

open OplaxMonoidal MonObj ComonObj BimonObj IsComonHom

/-- The image of a bimonoid object under an braided functor is a bimonoid object. -/
abbrev obj.instBimonObj (A : C) [BimonObj A] (F : C ⥤ D) [F.Braided] : BimonObj (F.obj A) where
  __ := obj.instComonObj A F
  __ := monObjObj A
  mul_comul := by
    simp only [μ_def, Δ_def, Category.assoc]
    simp only [← F.map_comp_assoc, mul_comul]
    simp only [map_comp, Category.assoc]
    simp only [Monoidal.map_tensor F, ← Category.assoc]
    rw [Monoidal.μ_δ F A A, Category.id_comp, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    congr 1
    simp only [Monoidal.μ_δ, Category.comp_id, δ_natural]
    rw [← tensorHom_comp_tensorHom]
    rw [Monoidal.map_tensor_assoc]
    rw [Monoidal.μ_δ, Category.comp_id]
    simp only [← Category.assoc]
    congr 1
    rw [← IsIso.eq_comp_inv]
    simp [tensorμ_comp_μ_tensorHom_μ_comp_μ]
  one_comul := by
    simp only [η_def, Δ_def, Category.assoc]
    simp only [← F.map_comp_assoc, one_comul]
    simp only [tensorObj.one_def, map_comp, Category.assoc, η_def]
    rw [Monoidal.map_tensor, Category.assoc, Category.assoc, Monoidal.μ_δ, Category.comp_id]
    rw [← tensorHom_comp_tensorHom]
    simp only [← Category.assoc]
    rw [@leftUnitor_inv_comp_tensorHom]
    simp only [Category.assoc, δ_natural, left_unitality F, Monoidal.whiskerRight_η_ε,
      Category.comp_id]
  mul_counit := by
    simp only [μ_def, ε_def, Category.assoc, Comon.tensorObj_counit]
    simp only [← F.map_comp_assoc, mul_counit]
    simp only [Comon.tensorObj_counit, map_comp, Category.assoc]
    rw [← tensorHom_comp_tensorHom, Monoidal.map_tensor]
    simp only [← Category.assoc, Monoidal.μ_δ, Category.id_comp]
    simp only [Category.assoc]
    rw [@Monoidal.map_leftUnitor_assoc]
    simp only [← Category.assoc, Monoidal.μ_δ, Category.id_comp]
    simp [tensorHom_def]
  one_counit := by
    simp only [η_def, ε_def, Category.assoc]
    simp only [← F.map_comp_assoc, one_counit]
    simp only [map_id, Category.id_comp, Monoidal.ε_η]

attribute [local instance] obj.instBimonObj

instance map.instIsBimon_Hom (F : C ⥤ D) [F.Braided] {X Y : C} [BimonObj X] [BimonObj Y]
    (f : X ⟶ Y) [IsBimonHom f] : IsBimonHom (F.map f) where

/-- A monoidal functor takes bimonoid objects to bimonoid objects.

That is, a monoidal functor `F : C ⥤ D` induces a functor `Bimon' C ⥤ Bimon' D`.
-/
@[implicit_reducible, simps]
def mapBimon (F : C ⥤ D) [F.Braided] : Bimon C ⥤ Bimon D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `BraidedFunctor C D`
-- and so can't state `mapBimonFunctor : BraidedFunctor C D ⥤ Bimon C ⥤ Bimon D`.

example (F : C ⥤ D) [F.Braided] (X : Bimon C) : μ[(F.mapBimon.obj X).X] =
  LaxMonoidal.μ F _ _ ≫ F.map μ[X.X] := by simp

section FullyFaithful

variable {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

/-- Pullback a bimonoid object along a fully faithful braided functor. -/
@[simps]
abbrev FullyFaithful.bimonObj (X : C)
    [BimonObj (F.obj X)] : BimonObj X where
  __ := hF.monObj X
  __ := hF.comonObj X
  mul_comul := by
    apply hF.map_injective
    simp only [map_comp, monObj_mul, comonObj_comul, map_preimage,
      Category.assoc, BimonObj.mul_comul_assoc]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    rw [CategoryTheory.Functor.Monoidal.map_tensor]
    simp only [map_preimage, Category.assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [← CategoryTheory.MonoidalCategory.tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc F X X X X]
    simp only [Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  one_comul := by
    apply hF.map_injective
    simp only [map_preimage, map_comp, monObj_one, comonObj_comul,
      Category.assoc, BimonObj.one_comul_assoc, Mon.one_def]
    rw [Monoidal.map_tensor, Monoidal.map_leftUnitor_inv]
    simp only [map_preimage, Category.assoc, Monoidal.μ_δ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map_assoc]
  mul_counit := by
    apply hF.map_injective
    simp only [map_preimage, map_comp, monObj_mul, comonObj_counit,
      Category.assoc, BimonObj.mul_counit_assoc, Comon.tensorObj_counit]
    rw [Monoidal.map_tensor]
    simp only [map_preimage, Category.assoc]
    rw [Monoidal.map_leftUnitor]
    simp only [LaxMonoidal.left_unitality, Monoidal.whiskerRight_η_ε_assoc, Monoidal.δ_μ_assoc]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
    congr 2
    rw [Monoidal.map_leftUnitor]
    rw [Monoidal.μ_δ_assoc]
    rw [MonoidalCategory.tensorHom_comp_whiskerRight_assoc]
    rw [Monoidal.ε_η]
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.id_whiskerLeft,
      LaxMonoidal.left_unitality, Category.assoc, LaxMonoidal.left_unitality_inv_assoc,
      Iso.inv_hom_id_map, Category.comp_id]
  one_counit := by
    apply hF.map_injective
    simp

lemma FullyFaithful.isBimonHom (X Y : C) [BimonObj (F.obj X)]
    [BimonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsBimonHom f] :
    letI := hF.bimonObj X; letI := hF.bimonObj Y;
    IsBimonHom (hF.preimage f) := by
  let := hF.bimonObj X; let := hF.bimonObj Y;
  have := hF.isMonHom; have := hF.isComonHom;
  exact IsBimonHom.mk

/-- Pullback a bimonoid object along a fully faithful braided functor as a bundled object. -/
@[implicit_reducible]
def FullyFaithful.bimon (hF : F.FullyFaithful) (X : C) [BimonObj (F.obj X)] :
    Bimon C where
  X := X
  bimon := hF.bimonObj X

/-- Pullback a morphism between bimonoid objects along a fully faithful braided functor. -/
@[simps!]
def FullyFaithful.bimonMap (hF : F.FullyFaithful) (X Y : C) [BimonObj (F.obj X)]
    [BimonObj (F.obj Y)] (f : F.obj X ⟶ F.obj Y) [IsBimonHom f] : hF.bimon X ⟶ hF.bimon Y :=
  letI := hF.isBimonHom X Y f; .mk (hF.preimage f)

end FullyFaithful

end Functor


/-! ### Lemmas on `Comon (Mon C)` and equivalence with `Mon (Comon C)` -/

namespace ComonMon

@[ext] lemma ext {X Y : Comon (Mon C)} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon.Hom.ext (Mon.Hom.ext w)

@[simp] theorem id_hom' (M : Comon (Mon C)) : Comon.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N K : Comon (Mon C)} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/-- The forgetful functor from bimonoid objects to monoid objects. -/
abbrev toMon : Comon (Mon C) ⥤ Mon C := Comon.forget (Mon C)

/-- The forgetful functor from bimonoid objects to the underlying category. -/
def forget : Comon (Mon C) ⥤ C := toMon C ⋙ Mon.forget C

@[simp]
theorem toMon_forget : toMon C ⋙ Mon.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
def toComon : Comon (Mon C) ⥤ Comon C := (Mon.forget C).mapComon

@[simp]
theorem toComon_forget : toComon C ⋙ Comon.forget C = forget C := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The object level part of the forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def toMonComonObj (M : Comon (Mon C)) : Mon (Comon C) where
  X := (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def toMonComon : Comon (Mon C) ⥤ Mon (Comon C) where
  obj := toMonComonObj
  map f := .mk' ((toComon C).map f)

variable {C}

/-- Auxiliary definition for `ofMonComonObj`. -/
@[simps! X]
def ofMonComonObjX (M : Mon (Comon C)) : Mon C := (Comon.forget C).mapMon.obj M

@[simp]
theorem ofMonComonObjX_one (M : Mon (Comon C)) :
    η[(ofMonComonObjX M).X] = 𝟙 (𝟙_ C) ≫ η[M.X].hom :=
  rfl

@[simp]
theorem ofMonComonObjX_mul (M : Mon (Comon C)) :
    μ[(ofMonComonObjX M).X] = 𝟙 (M.X.X ⊗ M.X.X) ≫ μ[M.X].hom :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ComonObj.instTensorUnit in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def tensorμ in
/-- The object level part of the backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def ofMonComonObj (M : Mon (Comon C)) : Comon (Mon C) where
  X := ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
def ofMonComon : Mon (Comon C) ⥤ Comon (Mon C) where
  obj := ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

@[simp]
theorem toMonComon_ofMonComon_obj_one (M : Comon (Mon C)) :
    η[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

@[simp]
theorem toMonComon_ofMonComon_obj_mul (M : Comon (Mon C)) :
    μ[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
def equivMonComonUnitIsoAppXAux (M : Comon (Mon C)) :
    M.X.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X.X :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
instance (M : Comon (Mon C)) : IsMonHom (equivMonComonUnitIsoAppXAux M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
def equivMonComonUnitIsoAppX (M : Comon (Mon C)) :
    M.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X :=
  Mon.mkIso (equivMonComonUnitIsoAppXAux M)

set_option backward.isDefEq.respectTransparency false in
instance (M : Comon (Mon C)) : IsComonHom (equivMonComonUnitIsoAppX M).hom where

/-- The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
def equivMonComonUnitIsoApp (M : Comon (Mon C)) :
    M ≅ (toMonComon C ⋙ ofMonComon C).obj M :=
  Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[simp]
theorem ofMonComon_toMonComon_obj_counit (M : Mon (Comon C)) :
    ε[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[simp]
theorem ofMonComon_toMonComon_obj_comul (M : Mon (Comon C)) :
    Δ[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
def equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (M : Mon (Comon C)) : IsComonHom (equivMonComonCounitIsoAppXAux M).hom where

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
def equivMonComonCounitIsoAppX (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X ≅ M.X :=
  Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (M : Mon (Comon C)) : IsMonHom (equivMonComonCounitIsoAppX M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
def equivMonComonCounitIsoApp (M : Mon (Comon C)) :
    (ofMonComon C ⋙ toMonComon C).obj M ≅ M :=
  Mon.mkIso (equivMonComonCounitIsoAppX M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Comon (Mon C) ≌ Mon (Comon C)` -/
def equivMonComon : Comon (Mon C) ≌ Mon (Comon C) where
  functor := toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

/-! ### The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
def trivial : Comon (Mon C) := Comon.trivial (Mon C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
def trivialTo (A : Comon (Mon C)) : trivial C ⟶ A :=
  .mk' (default : Mon.trivial C ⟶ A.X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
def toTrivial (A : Comon (Mon C)) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

/-! ### Additional lemmas -/

set_option backward.isDefEq.respectTransparency.types false in
theorem BimonObjAux_counit (M : Comon (Mon C)) :
    ε[((toComon C).obj M).X] = ε[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
theorem BimonObjAux_comul (M : Comon (Mon C)) :
    Δ[((toComon C).obj M).X] = Δ[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
instance (M : Comon (Mon C)) : BimonObj M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.counit_comul]
  comul_counit := by
    rw [← BimonObjAux_counit, ← BimonObjAux_comul, ComonObj.comul_counit]
  comul_assoc := by
    simp_rw [← BimonObjAux_comul, ComonObj.comul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Construct an object of `Comon (Mon C)` from an object `X : C` and `BimonObj X` instance. -/
@[simps X]
def mk' (X : C) [BimonObj X] : Comon (Mon C) where
  X := .mk X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X ⊗ X) }

instance (X Y : Comon (Mon C)) (f : X ⟶ Y) : IsMonHom f.hom.hom := f.hom.isMonHom_hom
instance (X Y : Comon (Mon C)) (f : X ⟶ Y) : IsComonHom f.hom.hom where
  hom_counit := congr(($f.isComonHom_hom.hom_counit).hom)
  hom_comul := congr(($f.isComonHom_hom.hom_comul).hom)
instance (X Y : Comon (Mon C)) (f : X ⟶ Y) : IsBimonHom f.hom.hom where

end ComonMon

/-! ### Equivalence between `Bimon C` and `Comon (Mon C)` -/

@[simps]
def ComonMon.toBimon : Comon (Mon C) ⥤ Bimon C where
  obj M := ⟨M.X.X⟩
  map f := .mk' f.hom.hom
  map_id M := rfl
  map_comp f g := rfl

@[simps]
def Bimon.toComonMon : Bimon C ⥤ Comon (Mon C) where
  obj M := ComonMon.mk' M.X
  map f := {
    hom := {
      hom := f.hom
      isMonHom_hom := f.isBimonHom_hom.toIsMonHom
    }
    isComonHom_hom := {
      hom_counit := Mon.Hom.ext' (IsComonHom.hom_counit f.hom)
      hom_comul := Mon.Hom.ext' (IsComonHom.hom_comul f.hom)
    }
  }
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def equiv : Comon (Mon C) ≌ Bimon C where
  functor := ComonMon.toBimon
  inverse := Bimon.toComonMon
  unitIso := NatIso.ofComponents Iso.refl (by intros; ext; simp)
  counitIso := NatIso.ofComponents Iso.refl (by intros; ext; simp)
  functor_unitIso_comp := by intros; ext; simp

end CategoryTheory
