/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.Topology.StoneCech
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Data.Set.Subsingleton
import Mathlib.CategoryTheory.Elementwise

#align_import topology.category.CompHaus.basic from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `TopCat`.
The fully faithful functor `CompHaus ⥤ TopCat` is denoted `compHausToTop`.

**Note:** The file `Topology/Category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`CompactumToCompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `CompactumToCompHaus.isEquivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/


universe v u

-- This was a global instance prior to #13170. We may experiment with removing it.
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus where
  /-- The underlying topological space of an object of `CompHaus`. -/
  toTop : TopCat
  -- Porting note: Renamed field.
  /-- The underlying topological space is compact. -/
  [is_compact : CompactSpace toTop]
  /-- The underlying topological space is T2. -/
  [is_hausdorff : T2Space toTop]
set_option linter.uppercaseLean3 false in
#align CompHaus CompHaus

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := { α := PEmpty } }⟩

instance : CoeSort CompHaus Type* :=
  ⟨fun X => X.toTop⟩

instance {X : CompHaus} : CompactSpace X :=
  X.is_compact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

instance category : Category CompHaus :=
  InducedCategory.category toTop
set_option linter.uppercaseLean3 false in
#align CompHaus.category CompHaus.category

instance concreteCategory : ConcreteCategory CompHaus :=
  InducedCategory.concreteCategory _
set_option linter.uppercaseLean3 false in
#align CompHaus.concrete_category CompHaus.concreteCategory

/-
-- Porting note: This is now a syntactic tautology.
@[simp]
theorem coe_toTop {X : CompHaus} : (X.toTop : Type*) = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align CompHaus.coe_to_Top CompHaus.coe_toTop
-/

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus where
  toTop := TopCat.of X
  is_compact := ‹_›
  is_hausdorff := ‹_›
set_option linter.uppercaseLean3 false in
#align CompHaus.of CompHaus.of

@[simp]
theorem coe_of : (CompHaus.of X : Type _) = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align CompHaus.coe_of CompHaus.coe_of

-- Porting note (#10754): Adding instance
instance (X : CompHaus.{u}) : TopologicalSpace ((forget CompHaus).obj X) :=
  show TopologicalSpace X.toTop from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHaus.{u}) : CompactSpace ((forget CompHaus).obj X) :=
  show CompactSpace X.toTop from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHaus.{u}) : T2Space ((forget CompHaus).obj X) :=
  show T2Space X.toTop from inferInstance

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem isClosedMap {X Y : CompHaus.{u}} (f : X ⟶ Y) : IsClosedMap f := fun _ hC =>
  (hC.isCompact.image f.continuous).isClosed
set_option linter.uppercaseLean3 false in
#align CompHaus.is_closed_map CompHaus.isClosedMap

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem isIso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact isClosedMap f S hS
  refine ⟨⟨⟨E.symm, hE⟩, ?_, ?_⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply
set_option linter.uppercaseLean3 false in
#align CompHaus.is_iso_of_bijective CompHaus.isIso_of_bijective

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def isoOfBijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) :
    X ≅ Y :=
  letI := isIso_of_bijective _ bij
  asIso f
set_option linter.uppercaseLean3 false in
#align CompHaus.iso_of_bijective CompHaus.isoOfBijective

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompHaus.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompHaus.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/-- The equivalence between isomorphisms in `CompHaus` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompHaus.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `TopCat`. -/
-- Porting note: `semireducible` -> `.default`.
@[simps (config := { rhsMd := .default })]
def compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  inducedFunctor _ -- deriving Full, Faithful -- Porting note: deriving fails, adding manually.
set_option linter.uppercaseLean3 false in
#align CompHaus_to_Top compHausToTop

instance : compHausToTop.Full  :=
  show (inducedFunctor _).Full from inferInstance

instance : compHausToTop.Faithful :=
  show (inducedFunctor _).Faithful from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHaus) : CompactSpace (compHausToTop.obj X) :=
  show CompactSpace X.toTop from inferInstance

-- Porting note (#10754): Adding instance
instance (X : CompHaus) : T2Space (compHausToTop.obj X) :=
  show T2Space X.toTop from inferInstance

instance CompHaus.forget_reflectsIsomorphisms : (forget CompHaus.{u}).ReflectsIsomorphisms :=
  ⟨by intro A B f hf; exact CompHaus.isIso_of_bijective _ ((isIso_iff_bijective f).mp hf)⟩
set_option linter.uppercaseLean3 false in
#align CompHaus.forget_reflects_isomorphisms CompHaus.forget_reflectsIsomorphisms

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps!]
def stoneCechObj (X : TopCat) : CompHaus :=
  CompHaus.of (StoneCech X)
set_option linter.uppercaseLean3 false in
#align StoneCech_obj stoneCechObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where
  toFun f :=
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.2.comp (@continuous_stoneCechUnit X _) }
  invFun f :=
    { toFun := stoneCechExtend f.2
      continuous_toFun := continuous_stoneCechExtend f.2 }
  left_inv := by
    rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
    -- Porting note: `ext` fails.
    apply ContinuousMap.ext
    intro (x : StoneCech X)
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
    -- Porting note: `ext` fails.
    apply ContinuousMap.ext
    intro
    exact congr_fun (stoneCechExtend_extends hf) _
#align stone_cech_equivalence stoneCechEquivalence

/-- The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : TopCat.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl
set_option linter.uppercaseLean3 false in
#align Top_to_CompHaus topToCompHaus

theorem topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Top_to_CompHaus_obj topToCompHaus_obj

/-- The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective : Reflective compHausToTop where
  L := topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _
set_option linter.uppercaseLean3 false in
#align CompHaus_to_Top.reflective compHausToTop.reflective

noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _
set_option linter.uppercaseLean3 false in
#align CompHaus_to_Top.creates_limits compHausToTop.createsLimits

instance CompHaus.hasLimits : Limits.HasLimits CompHaus :=
  hasLimits_of_hasLimits_createsLimits compHausToTop
set_option linter.uppercaseLean3 false in
#align CompHaus.has_limits CompHaus.hasLimits

instance CompHaus.hasColimits : Limits.HasColimits CompHaus :=
  hasColimits_of_reflective compHausToTop
set_option linter.uppercaseLean3 false in
#align CompHaus.has_colimits CompHaus.hasColimits

namespace CompHaus

/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.Cone F :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { pt := {
      toTop := (TopCat.limitCone FF).pt
      is_compact := by
        show CompactSpace { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } := by
          ext1
          simp only [Set.mem_iInter, Set.mem_setOf_eq]
        rw [this]
        apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro f
        apply isClosed_eq
        · exact (ContinuousMap.continuous (F.map f)).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance }
    π := {
      app := fun j => (TopCat.limitCone FF).π.app j
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [comp_apply, Functor.const_obj_map, id_apply]
        exact (hx f).symm } }
set_option linter.uppercaseLean3 false in
#align CompHaus.limit_cone CompHaus.limitCone

/-- The limit cone `CompHaus.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) :
    Limits.IsLimit.{v} (limitCone.{v,u} F) :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => (TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S)
    fac := fun S => (TopCat.limitConeIsLimit FF).fac (compHausToTop.mapCone S)
    uniq := fun S => (TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) }
set_option linter.uppercaseLean3 false in
#align CompHaus.limit_cone_is_limit CompHaus.limitConeIsLimit

theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    haveI : CompactSpace (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.compactSpace
    haveI : T2Space (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z :=
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uLift_up.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x
      -- Porting note: `ext` doesn't apply these two lemmas.
      apply ULift.ext
      apply Subtype.ext
      dsimp
      -- Porting note: This `change` is not ideal.
      -- I think lean is having issues understanding when a `ContinuousMap` should be considered
      -- as a morphism.
      -- TODO(?): Make morphisms in `CompHaus` (and other topological categories)
      -- into a one-field-structure.
      change 0 = φ (f x)
      simp only [hφ0 (Set.mem_range_self x), Pi.zero_apply]
    apply_fun fun e => (e y).down.1 at H
    dsimp [Z] at H
    change 0 = φ y at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map
set_option linter.uppercaseLean3 false in
#align CompHaus.epi_iff_surjective CompHaus.epi_iff_surjective

theorem mono_iff_injective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : of PUnit ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : of PUnit ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ext
      exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit at this
    exact this
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget CompHaus).mono_of_mono_map
set_option linter.uppercaseLean3 false in
#align CompHaus.mono_iff_injective CompHaus.mono_iff_injective

end CompHaus
