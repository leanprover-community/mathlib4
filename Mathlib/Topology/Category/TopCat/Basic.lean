/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `TopCat` of topological spaces together with the functors
`TopCat.discrete` and `TopCat.trivial` from the category of types to `TopCat` which equip a type
with the corresponding discrete, resp. trivial, topology. For a proof that these functors are left,
resp. right adjoint to the forgetful functor, see
`Mathlib/Topology/Category/TopCat/Adjunctions.lean`.
-/

assert_not_exists Module

open CategoryTheory TopologicalSpace Topology

universe u

/-- The category of topological spaces. -/
structure TopCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type u
  [str : TopologicalSpace carrier]

attribute [instance] TopCat.str

initialize_simps_projections TopCat (-str)

namespace TopCat

instance : CoeSort (TopCat) (Type u) :=
  ⟨TopCat.carrier⟩

attribute [coe] TopCat.carrier

/-- The object in `TopCat` associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `TopCat`. -/
abbrev of (X : Type u) [TopologicalSpace X] : TopCat :=
  ⟨X⟩

lemma coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl

lemma of_carrier (X : TopCat.{u}) : of X = X := rfl

variable {X} in
/-- The type of morphisms in `TopCat`. -/
@[ext]
structure Hom (X Y : TopCat.{u}) where
  private mk ::
  /-- The underlying `ContinuousMap`. -/
  hom' : C(X, Y)

instance : Category TopCat where
  Hom X Y := Hom X Y
  id X := ⟨ContinuousMap.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} TopCat (fun X Y => C(X, Y)) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `TopCat` back into a `ContinuousMap`. -/
abbrev Hom.hom {X Y : TopCat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := TopCat) f

/-- Typecheck a `ContinuousMap` as a morphism in `TopCat`. -/
abbrev ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := TopCat) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (X Y : TopCat) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {X : TopCat.{u}} : (𝟙 X : X ⟶ X).hom = ContinuousMap.id X := rfl

@[simp]
theorem id_app (X : TopCat.{u}) (x : ↑X) : (𝟙 X : X ⟶ X) x = x := rfl

@[simp] theorem coe_id (X : TopCat.{u}) : (𝟙 X : X → X) = id := rfl

@[simp]
lemma hom_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
theorem comp_app {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X → Z) x = g (f x) := rfl

@[simp] theorem coe_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f := rfl

@[ext]
lemma hom_ext {X Y : TopCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
lemma ext {X Y : TopCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[simp]
lemma hom_ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
  (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {X Y : TopCat} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type u} [TopologicalSpace X] : ofHom (ContinuousMap.id X) = 𝟙 (of X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    (ofHom f) x = f x := rfl

lemma hom_inv_id_apply {X Y : TopCat} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x := by
  simp

lemma inv_hom_id_apply {X Y : TopCat} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y := by
  simp

/--
Replace a function coercion for a morphism `TopCat.of X ⟶ TopCat.of Y` with the definitionally
equal function coercion for a continuous map `C(X, Y)`.
-/
@[simp] theorem coe_of_of {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x} :
    @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
      (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) HasForget.instFunLike
      (ofHom f) x =
    @DFunLike.coe C(X, Y) X
      (fun _ ↦ Y) _
      f x :=
  rfl

instance inhabited : Inhabited TopCat :=
  ⟨TopCat.of Empty⟩

@[deprecated
  "Simply remove this from the `simp`/`rw` set: the LHS and RHS are now identical."
  (since := "2025-01-30")]
lemma hom_apply {X Y : TopCat} (f : X ⟶ Y) (x : X) : f x = ContinuousMap.toFun f.hom x := rfl

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊥
  map f := @ofHom _ _ ⊥ ⊥ <| @ContinuousMap.mk _ _ ⊥ ⊥ f continuous_bot

instance {X : Type u} : DiscreteTopology (discrete.obj X) :=
  ⟨rfl⟩

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ TopCat.{u} where
  obj X := @of X ⊤
  map f := @ofHom _ _ ⊤ ⊤ <| @ContinuousMap.mk _ _ ⊤ ⊤ f continuous_top

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ofHom f
  inv := ofHom f.symm

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

@[simp]
theorem of_isoOfHomeo {X Y : TopCat.{u}} (f : X ≃ₜ Y) : homeoOfIso (isoOfHomeo f) = f := by
  ext
  rfl

@[simp]
theorem of_homeoOfIso {X Y : TopCat.{u}} (f : X ≅ Y) : isoOfHomeo (homeoOfIso f) = f := by
  ext
  rfl

lemma isIso_of_bijective_of_isOpenMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsOpenMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen f.hom.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom

lemma isIso_of_bijective_of_isClosedMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hfbij : Function.Bijective f) (hfcl : IsClosedMap f) : IsIso f :=
  let e : X ≃ₜ Y :=
    (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousClosed f.hom.continuous hfcl
  inferInstanceAs <| IsIso (TopCat.isoOfHomeo e).hom

lemma isIso_iff_isHomeomorph {X Y : TopCat.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsHomeomorph f :=
  ⟨fun _ ↦ (homeoOfIso (asIso f)).isHomeomorph,
    fun H ↦ isIso_of_bijective_of_isOpenMap _ H.bijective H.isOpenMap⟩

theorem isOpenEmbedding_iff_comp_isIso {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding f :=
  (TopCat.homeoOfIso (asIso g)).isOpenEmbedding.of_comp_iff f

@[simp]
theorem isOpenEmbedding_iff_comp_isIso' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding f := by
  simp only [← Functor.map_comp]
  exact isOpenEmbedding_iff_comp_isIso f g

theorem isOpenEmbedding_iff_isIso_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (f ≫ g) ↔ IsOpenEmbedding g := by
  constructor
  · intro h
    convert h.comp (TopCat.homeoOfIso (asIso f).symm).isOpenEmbedding
    exact congr_arg (DFunLike.coe ∘ ConcreteCategory.hom) (IsIso.inv_hom_id_assoc f g).symm
  · exact fun h => h.comp (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

@[simp]
theorem isOpenEmbedding_iff_isIso_comp' {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    IsOpenEmbedding (g ∘ f) ↔ IsOpenEmbedding g := by
  simp only [← Functor.map_comp]
  exact isOpenEmbedding_iff_isIso_comp f g

end TopCat
