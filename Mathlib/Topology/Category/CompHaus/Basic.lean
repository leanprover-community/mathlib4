/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.Topology.StoneCech
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `TopCat`.
The fully faithful functor `CompHaus ⥤ TopCat` is denoted `compHausToTop`.

**Note:** The file `Mathlib/Topology/Category/Compactum.lean` provides the equivalence between
`Compactum`, which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`CompactumToCompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `CompactumToCompHaus.isEquivalence`.
See `Mathlib/Topology/Category/Compactum.lean` for a more detailed discussion where these
definitions are introduced.

## Implementation

The category `CompHaus` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/


universe v u

open CategoryTheory CompHausLike

/-- The category of compact Hausdorff spaces. -/
abbrev CompHaus := CompHausLike (fun _ ↦ True)

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := TopCat.of PEmpty, prop := trivial}⟩

instance : CoeSort CompHaus Type* :=
  ⟨fun X => X.toTop⟩

instance {X : CompHaus} : CompactSpace X :=
  X.is_compact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

instance : HasProp (fun _ ↦ True) X := ⟨trivial⟩

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
abbrev of : CompHaus := CompHausLike.of _ X

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `TopCat`. -/
abbrev compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  CompHausLike.compHausLikeToTop _

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps!]
def stoneCechObj (X : TopCat) : CompHaus :=
  CompHaus.of (StoneCech X)

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where
  toFun f := TopCat.ofHom
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.hom.2.comp (@continuous_stoneCechUnit X _) }
  invFun f := CompHausLike.ofHom _
    { toFun := stoneCechExtend f.hom.2
      continuous_toFun := continuous_stoneCechExtend f.hom.2 }
  left_inv := by
    rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
    ext x
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _

/-- The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : TopCat.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

theorem topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl

/-- The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective : Reflective compHausToTop where
  L := topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _

noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _

instance CompHaus.hasLimits : Limits.HasLimits CompHaus :=
  hasLimits_of_hasLimits_createsLimits compHausToTop

instance CompHaus.hasColimits : Limits.HasColimits CompHaus :=
  hasColimits_of_reflective compHausToTop

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
        · exact ((F.map f).hom.continuous).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance
      prop := trivial }
    π := {
      app := fun j => (TopCat.limitCone FF).π.app j
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [CategoryTheory.comp_apply, Functor.const_obj_map, CategoryTheory.id_apply]
        exact (hx f).symm } }

/-- The limit cone `CompHaus.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) :
    Limits.IsLimit.{v} (limitCone.{v,u} F) :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => (TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S)
    fac := fun S => (TopCat.limitConeIsLimit FF).fac (compHausToTop.mapCone S)
    uniq := fun S => (TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) }

theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.continuous).isClosed
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
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map

end CompHaus

/-- Every `CompHausLike` admits a functor to `CompHaus`. -/
abbrev compHausLikeToCompHaus (P : TopCat → Prop) : CompHausLike P ⥤ CompHaus :=
  CompHausLike.toCompHausLike (by simp only [implies_true])
