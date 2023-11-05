/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.category.Top.basic from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

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
@[to_additive existing TopCat]
def TopCat : Type (u + 1) :=
  Bundled TopologicalSpace

namespace TopCat

-- porting note: had to add in the last two proofs
instance bundledHom : BundledHom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_injective,
    fun _ => rfl, fun _ _ _ _ _ => rfl⟩

deriving instance LargeCategory for TopCat

-- Porting note: currently no derive handler for ConcreteCategory
-- see https://github.com/leanprover-community/mathlib4/issues/5020
instance concreteCategory : ConcreteCategory TopCat := by
  dsimp [TopCat]
  infer_instance

@[to_additive existing TopCat.instCoeSortTopCatType]
instance instCoeSortTopCatType : CoeSort TopCat (Type*) :=
  Bundled.coeSort

instance topologicalSpaceUnbundled (x : TopCat) : TopologicalSpace x :=
  x.str

-- Porting note: cannot find a coercion to function otherwise
attribute [instance] ConcreteCategory.funLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f

-- Porting note: simp can prove this; removed simp
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

-- Porting note: simp can prove this; removed simp
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [TopologicalSpace X] : TopCat :=
  -- Porting note: needed to call inferInstance
  ⟨X, inferInstance⟩

instance topologicalSpace_coe (X : TopCat) : TopologicalSpace X :=
  X.str

-- Porting note: cannot see through forget; made reducible to get closer to Lean 3 behavior
@[reducible]
instance topologicalSpace_forget (X : TopCat) : TopologicalSpace <| (forget TopCat).obj X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X := rfl

instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

-- porting note: added to ease the port of `AlgebraicTopology.TopologicalSimplex`
lemma hom_apply {X Y : TopCat} (f : X ⟶ Y) (x : X) : f x = ContinuousMap.toFun f x := rfl

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := ⟨X , ⊥⟩
  map f := @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := ⟨X, ⊤⟩
  map f := @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  -- Porting note: previously ⟨f⟩ for hom (inv) and tidy closed proofs
  hom := f.toContinuousMap
  inv := f.symm.toContinuousMap
  hom_inv_id := by ext; exact f.symm_apply_apply _
  inv_hom_id := by ext; exact f.apply_symm_apply _

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

@[simp]
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  -- Porting note: unfold some defs now
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl

@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  -- Porting note: unfold some defs now
  dsimp [homeoOfIso, isoOfHomeo]
  ext
  rfl

-- Porting note: simpNF requested partially simped version below
theorem openEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).openEmbedding.of_comp_iff f

@[simp]
theorem openEmbedding_iff_comp_isIso' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    OpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ OpenEmbedding f := by
  simp only [←Functor.map_comp]
  exact openEmbedding_iff_comp_isIso f g

-- Porting note: simpNF requested partially simped version below
theorem openEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding (f ≫ g) ↔ OpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (asIso f).symm).openEmbedding
    exact congrArg _ (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).openEmbedding

@[simp]
theorem openEmbedding_iff_isIso_comp' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    OpenEmbedding ((forget TopCat).map f ≫ (forget TopCat).map g) ↔ OpenEmbedding g := by
  simp only [←Functor.map_comp]
  exact openEmbedding_iff_isIso_comp f g

end TopCat
