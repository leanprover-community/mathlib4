/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.category.Top.basic from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`TopCat.discrete` and `TopCat.trivial` from the category of types to `TopCat` which equip a type
with the corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see `Mathlib.Topology.Category.TopCat.Adjunctions`.
-/


open CategoryTheory

open TopologicalSpace

universe u

/-- The category of topological spaces and continuous maps. -/
@[to_additive existing TopCat]
def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace
set_option linter.uppercaseLean3 false in
#align Top TopCat

namespace TopCat

instance bundledHom : BundledHom @ContinuousMap where
  toFun := @ContinuousMap.toFun
  id := @ContinuousMap.id
  comp := @ContinuousMap.comp
set_option linter.uppercaseLean3 false in
#align Top.bundled_hom TopCat.bundledHom

deriving instance LargeCategory for TopCat

-- Porting note: currently no derive handler for ConcreteCategory
-- see https://github.com/leanprover-community/mathlib4/issues/5020
instance concreteCategory : ConcreteCategory TopCat :=
  inferInstanceAs <| ConcreteCategory (Bundled TopologicalSpace)

instance : CoeSort TopCat Type* where
  coe X := X.α

instance topologicalSpaceUnbundled (X : TopCat) : TopologicalSpace X :=
  X.str
set_option linter.uppercaseLean3 false in
#align Top.topological_space_unbundled TopCat.topologicalSpaceUnbundled

-- We leave this temporarily as a reminder of the downstream instances #13170
-- -- Porting note: cannot find a coercion to function otherwise
-- -- attribute [instance] ConcreteCategory.instFunLike in
-- instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
--   coe (f : C(X, Y)) := f

instance instFunLike (X Y : TopCat) : FunLike (X ⟶ Y) X Y :=
  inferInstanceAs <| FunLike C(X, Y) X Y

instance instMonoidHomClass (X Y : TopCat) : ContinuousMapClass (X ⟶ Y) X Y :=
  inferInstanceAs <| ContinuousMapClass C(X, Y) X Y

-- Porting note (#10618): simp can prove this; removed simp
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl
set_option linter.uppercaseLean3 false in
#align Top.id_app TopCat.id_app

-- Porting note (#10618): simp can prove this; removed simp
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl
set_option linter.uppercaseLean3 false in
#align Top.comp_app TopCat.comp_app

@[simp] theorem coe_id (X : TopCat.{u}) : (𝟙 X : X → X) = id := rfl

@[simp] theorem coe_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[simp]
lemma hom_inv_id_apply {X Y : TopCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
  DFunLike.congr_fun f.hom_inv_id x

@[simp]
lemma inv_hom_id_apply {X Y : TopCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
  DFunLike.congr_fun f.inv_hom_id y

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [TopologicalSpace X] : TopCat :=
  -- Porting note: needed to call inferInstance
  ⟨X, inferInstance⟩
set_option linter.uppercaseLean3 false in
#align Top.of TopCat.of

instance topologicalSpace_coe (X : TopCat) : TopologicalSpace X :=
  X.str

-- Porting note: cannot see through forget; made reducible to get closer to Lean 3 behavior
@[instance] abbrev topologicalSpace_forget
    (X : TopCat) : TopologicalSpace <| (forget TopCat).obj X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X := rfl
set_option linter.uppercaseLean3 false in
#align Top.coe_of TopCat.coe_of

/--
Replace a function coercion for a morphism `TopCat.of X ⟶ TopCat.of Y` with the definitionally
equal function coercion for a continuous map `C(X, Y)`.
-/
@[simp] theorem coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x} :
    @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
      (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
      f x =
    @DFunLike.coe C(X, Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl

instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

-- Porting note: added to ease the port of `AlgebraicTopology.TopologicalSimplex`
lemma hom_apply {X Y : TopCat} (f : X ⟶ Y) (x : X) : f x = ContinuousMap.toFun f x := rfl

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := ⟨X , ⊥⟩
  map f := @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot
set_option linter.uppercaseLean3 false in
#align Top.discrete TopCat.discrete

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊤⟩
  map f := @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top
set_option linter.uppercaseLean3 false in
#align Top.trivial TopCat.trivial

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  -- Porting note: previously ⟨f⟩ for hom (inv) and tidy closed proofs
  hom := f.toContinuousMap
  inv := f.symm.toContinuousMap
  hom_inv_id := by ext; exact f.symm_apply_apply _
  inv_hom_id := by ext; exact f.apply_symm_apply _
set_option linter.uppercaseLean3 false in
#align Top.iso_of_homeo TopCat.isoOfHomeo

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
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
  -- Porting note: unfold some defs now
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align Top.of_iso_of_homeo TopCat.of_isoOfHomeo

@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  -- Porting note: unfold some defs now
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl
set_option linter.uppercaseLean3 false in
#align Top.of_homeo_of_iso TopCat.of_homeoOfIso

-- Porting note: simpNF requested partially simped version below
theorem openEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).openEmbedding.of_comp_iff f
set_option linter.uppercaseLean3 false in
#align Top.open_embedding_iff_comp_is_iso TopCat.openEmbedding_iff_comp_isIso

@[simp]
theorem openEmbedding_iff_comp_isIso' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ OpenEmbedding f := by
  simp only [← Functor.map_comp]
  exact openEmbedding_iff_comp_isIso f g

-- Porting note: simpNF requested partially simped version below
theorem openEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (asIso f).symm).openEmbedding
    exact congrArg _ (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).openEmbedding
set_option linter.uppercaseLean3 false in
#align Top.open_embedding_iff_is_iso_comp TopCat.openEmbedding_iff_isIso_comp

@[simp]
theorem openEmbedding_iff_isIso_comp' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ OpenEmbedding g := by
  simp only [← Functor.map_comp]
  exact openEmbedding_iff_isIso_comp f g

end TopCat
