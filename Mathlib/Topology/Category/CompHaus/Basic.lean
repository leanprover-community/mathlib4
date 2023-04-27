/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta

! This file was ported from Lean 3 source module topology.category.CompHaus.basic
! leanprover-community/mathlib commit 178a32653e369dce2da68dc6b2694e385d484ef1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.Topology.StoneCech
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.Topology.UrysohnsLemma
import Mathbin.Topology.Category.Top.Limits.Basic

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/


universe v u

open CategoryTheory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus where
  toTop : TopCat
  [IsCompact : CompactSpace to_Top]
  [is_hausdorff : T2Space to_Top]
#align CompHaus CompHaus

namespace CompHaus

instance : Inhabited CompHaus :=
  ⟨{ toTop := { α := PEmpty } }⟩

instance : CoeSort CompHaus (Type _) :=
  ⟨fun X => X.toTop⟩

instance {X : CompHaus} : CompactSpace X :=
  X.IsCompact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

instance category : Category CompHaus :=
  InducedCategory.category toTop
#align CompHaus.category CompHaus.category

instance concreteCategory : ConcreteCategory CompHaus :=
  InducedCategory.concreteCategory _
#align CompHaus.concrete_category CompHaus.concreteCategory

@[simp]
theorem coe_toTop {X : CompHaus} : (X.toTop : Type _) = X :=
  rfl
#align CompHaus.coe_to_Top CompHaus.coe_toTop

variable (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A constructor for objects of the category `CompHaus`,
taking a type, and bundling the compact Hausdorff topology
found by typeclass inference. -/
def of : CompHaus where
  toTop := TopCat.of X
  IsCompact := ‹_›
  is_hausdorff := ‹_›
#align CompHaus.of CompHaus.of

@[simp]
theorem coe_of : (CompHaus.of X : Type _) = X :=
  rfl
#align CompHaus.coe_of CompHaus.coe_of

/-- Any continuous function on compact Hausdorff spaces is a closed map. -/
theorem isClosedMap {X Y : CompHaus.{u}} (f : X ⟶ Y) : IsClosedMap f := fun C hC =>
  (hC.IsCompact.image f.Continuous).IsClosed
#align CompHaus.is_closed_map CompHaus.isClosedMap

/-- Any continuous bijection of compact Hausdorff spaces is an isomorphism. -/
theorem isIso_of_bijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) :
    IsIso f := by
  let E := Equiv.ofBijective _ bij
  have hE : Continuous E.symm := by
    rw [continuous_iff_isClosed]
    intro S hS
    rw [← E.image_eq_preimage]
    exact IsClosedMap f S hS
  refine' ⟨⟨⟨E.symm, hE⟩, _, _⟩⟩
  · ext x
    apply E.symm_apply_apply
  · ext x
    apply E.apply_symm_apply
#align CompHaus.is_iso_of_bijective CompHaus.isIso_of_bijective

/-- Any continuous bijection of compact Hausdorff spaces induces an isomorphism. -/
noncomputable def isoOfBijective {X Y : CompHaus.{u}} (f : X ⟶ Y) (bij : Function.Bijective f) :
    X ≅ Y :=
  letI := is_iso_of_bijective _ bij
  as_iso f
#align CompHaus.iso_of_bijective CompHaus.isoOfBijective

end CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps (config := { rhsMd := semireducible })]
def compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  inducedFunctor _ deriving Full, Faithful
#align CompHaus_to_Top compHausToTop

instance CompHaus.forget_reflectsIsomorphisms : ReflectsIsomorphisms (forget CompHaus.{u}) :=
  ⟨by intro A B f hf <;> exact CompHaus.isIso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩
#align CompHaus.forget_reflects_isomorphisms CompHaus.forget_reflectsIsomorphisms

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps]
def stoneCechObj (X : TopCat) : CompHaus :=
  CompHaus.of (StoneCech X)
#align StoneCech_obj stoneCechObj

/-- (Implementation) The bijection of homsets to establish the reflective adjunction of compact
Hausdorff spaces in topological spaces.
-/
noncomputable def stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y)
    where
  toFun f :=
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.2.comp (@continuous_stoneCechUnit X _) }
  invFun f :=
    { toFun := stoneCechExtend f.2
      continuous_toFun := continuous_stoneCechExtend f.2 }
  left_inv := by
    rintro ⟨f : StoneCech X ⟶ Y, hf : Continuous f⟩
    ext (x : StoneCech X)
    refine' congr_fun _ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    rintro _ ⟨y, rfl⟩
    apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
  right_inv := by
    rintro ⟨f : (X : Type _) ⟶ Y, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _
#align stone_cech_equivalence stoneCechEquivalence

/-- The Stone-Cech compactification functor from topological spaces to compact Hausdorff spaces,
left adjoint to the inclusion functor.
-/
noncomputable def topToCompHaus : TopCat.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl
#align Top_to_CompHaus topToCompHaus

theorem topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl
#align Top_to_CompHaus_obj topToCompHaus_obj

/-- The category of compact Hausdorff spaces is reflective in the category of topological spaces.
-/
noncomputable instance compHausToTop.reflective : Reflective compHausToTop
    where toIsRightAdjoint := ⟨topToCompHaus, Adjunction.adjunctionOfEquivLeft _ _⟩
#align CompHaus_to_Top.reflective compHausToTop.reflective

noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _
#align CompHaus_to_Top.creates_limits compHausToTop.createsLimits

instance CompHaus.hasLimits : Limits.HasLimits CompHaus :=
  has_limits_of_has_limits_creates_limits compHausToTop
#align CompHaus.has_limits CompHaus.hasLimits

instance CompHaus.hasColimits : Limits.HasColimits CompHaus :=
  has_colimits_of_reflective compHausToTop
#align CompHaus.has_colimits CompHaus.hasColimits

namespace CompHaus

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- An explicit limit cone for a functor `F : J ⥤ CompHaus`, defined in terms of
`Top.limit_cone`. -/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.Cone F
    where
  pt :=
    { toTop := (TopCat.limitCone (F ⋙ compHausToTop)).pt
      IsCompact :=
        by
        show CompactSpace ↥{ u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } :=
          by
          ext1
          simp only [Set.mem_interᵢ, Set.mem_setOf_eq]
        rw [this]
        apply isClosed_interᵢ
        intro i
        apply isClosed_interᵢ
        intro j
        apply isClosed_interᵢ
        intro f
        apply isClosed_eq
        · exact (ContinuousMap.continuous (F.map f)).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space ↥{ u : ∀ j, F.obj j | ∀ {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance }
  π :=
    { app := fun j => (TopCat.limitCone (F ⋙ compHausToTop)).π.app j
      naturality' := by
        intro _ _ _
        ext ⟨x, hx⟩
        simp only [comp_apply, functor.const_obj_map, id_apply]
        exact (hx f).symm }
#align CompHaus.limit_cone CompHaus.limitCone

/-- The limit cone `CompHaus.limit_cone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) :
    Limits.IsLimit (limitCone F)
    where
  lift S := (TopCat.limitConeIsLimit (F ⋙ compHausToTop)).lift (compHausToTop.mapCone S)
  uniq S m h := (TopCat.limitConeIsLimit _).uniq (compHausToTop.mapCone S) _ h
#align CompHaus.limit_cone_is_limit CompHaus.limitConeIsLimit

theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f :=
  by
  constructor
  · contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).IsClosed
    let D := {y}
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    haveI : NormalSpace ↥Y.to_Top := normalOfCompactT2
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_closed hC hD hCD
    haveI : CompactSpace (ULift.{u} <| Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.compact_space
    haveI : T2Space (ULift.{u} <| Set.Icc (0 : ℝ) 1) := homeomorph.ulift.symm.t2_space
    let Z := of (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z :=
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_ulift_up.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ⟨fun _ => ⟨⟨0, set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x
      dsimp
      simp only [comp_apply, ContinuousMap.coe_mk, Subtype.coe_mk, hφ0 (Set.mem_range_self x),
        Pi.zero_apply]
    apply_fun fun e => (e y).down  at H
    dsimp at H
    simp only [Subtype.mk_eq_mk, hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map
#align CompHaus.epi_iff_surjective CompHaus.epi_iff_surjective

theorem mono_iff_injective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  by
  constructor
  · intro hf x₁ x₂ h
    let g₁ : of PUnit ⟶ X := ⟨fun _ => x₁, continuous_const⟩
    let g₂ : of PUnit ⟶ X := ⟨fun _ => x₂, continuous_const⟩
    have : g₁ ≫ f = g₂ ≫ f := by
      ext
      exact h
    rw [cancel_mono] at this
    apply_fun fun e => e PUnit.unit  at this
    exact this
  · rw [← CategoryTheory.mono_iff_injective]
    apply (forget CompHaus).mono_of_mono_map
#align CompHaus.mono_iff_injective CompHaus.mono_iff_injective

end CompHaus

