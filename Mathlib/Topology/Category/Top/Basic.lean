/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro

! This file was ported from Lean 3 source module topology.category.Top.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.ContinuousFunction.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`discrete` and `trivial` from the category of types to `TopCat` which equip a type with the
corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see `topology.category.TopCat.adjunctions`.
-/


open CategoryTheory

open TopologicalSpace

universe u

/-- The category of topological spaces and continuous maps. -/
def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace
set_option linter.uppercaseLean3 false in
#align Top TopCat

namespace TopCat

-- porting note: had to add in the last two proofs
instance bundledHom : BundledHom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_injective,
    fun _ => rfl, fun _ _ _ _ _ => rfl⟩
set_option linter.uppercaseLean3 false in
#align Top.bundled_hom TopCat.bundledHom

deriving instance LargeCategory for TopCat

instance concreteCategory : ConcreteCategory TopCat := by
  dsimp only [TopCat]
  infer_instance

instance : CoeSort TopCat (Type _) :=
  Bundled.coeSort

instance topologicalSpaceUnbundled (x : TopCat) : TopologicalSpace x :=
  x.str
set_option linter.uppercaseLean3 false in
#align Top.topological_space_unbundled TopCat.topologicalSpaceUnbundled

-- porting note: this instance was not necessary in mathlib
instance {X Y : TopCat} : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ConcreteCategory.hasCoeToFun

@[simp]
theorem id_app (X : TopCat.{u}) (x : X) : (𝟙 X : X → X) x = x :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.id_app TopCat.id_app

@[simp]
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.comp_app TopCat.comp_app

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [hX : TopologicalSpace X] : TopCat :=
  ⟨X, hX⟩ -- porting note: had to specify hX
set_option linter.uppercaseLean3 false in
#align Top.of TopCat.of

instance (X : TopCat) : TopologicalSpace X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top.coe_of TopCat.coe_of

instance : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊥⟩
  map X Y f :=
    { toFun := f
      continuous_toFun := continuous_bot }
set_option linter.uppercaseLean3 false in
#align Top.discrete TopCat.discrete

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊤⟩
  map X Y f :=
    { toFun := f
      continuous_toFun := continuous_top }
set_option linter.uppercaseLean3 false in
#align Top.trivial TopCat.trivial

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.2⟩
  inv := ⟨f.symm, f.3⟩
set_option linter.uppercaseLean3 false in
#align Top.iso_of_homeo TopCat.isoOfHomeo

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y
    where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous
set_option linter.uppercaseLean3 false in
#align Top.homeo_of_iso TopCat.homeoOfIso

@[simp]
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align Top.of_iso_of_homeo TopCat.of_isoOfHomeo

@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align Top.of_homeo_of_iso TopCat.of_homeoOfIso

@[simp]
theorem openEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).openEmbedding.of_comp_iff f
set_option linter.uppercaseLean3 false in
#align Top.open_embedding_iff_comp_is_iso TopCat.openEmbedding_iff_comp_isIso

@[simp]
theorem openEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (asIso f).symm).openEmbedding
    exact congr_arg _ (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).openEmbedding
set_option linter.uppercaseLean3 false in
#align Top.open_embedding_iff_is_iso_comp TopCat.openEmbedding_iff_isIso_comp

end TopCat
