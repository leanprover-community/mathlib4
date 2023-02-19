/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn

! This file was ported from Lean 3 source module category_theory.limits.has_limits
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Category.Ulift

/-!
# Existence of limits and colimits

In `category_theory.limits.is_limit` we defined `is_limit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

`has_limit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `has_limit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `has_limit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.X ⟶ limit F`, the universal morphism from any other `c : cone F`, etc.

Key to using the `has_limit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `has_limits_of_shape J C` and `has_limits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `is_limit`,
and then a result in terms of `has_limit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `has_limit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category_theory universes].
universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u} [Category.{v} C]

variable {F : J ⥤ C}

section Limit

/-- `limit_cone F` contains a cone over `F` together with the information that it is a limit. -/
-- @[nolint has_nonempty_instance] -- Porting note: removed
structure LimitCone (F : J ⥤ C) where
  cone : Cone F
  isLimit : IsLimit cone
#align category_theory.limits.limit_cone CategoryTheory.Limits.LimitCone

/-- `has_limit F` represents the mere existence of a limit for `F`. -/
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  exists_limit : Nonempty (LimitCone F)
#align category_theory.limits.has_limit CategoryTheory.Limits.HasLimit

theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩
#align category_theory.limits.has_limit.mk CategoryTheory.Limits.HasLimit.mk

/-- Use the axiom of choice to extract explicit `limit_cone F` from `has_limit F`. -/
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit
#align category_theory.limits.get_limit_cone CategoryTheory.Limits.getLimitCone

variable (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class HasLimitsOfShape : Prop where
  hasLimit : ∀ F : J ⥤ C, HasLimit F := by infer_instance
#align category_theory.limits.has_limits_of_shape CategoryTheory.Limits.HasLimitsOfShape

/-- `C` has all limits of size `v₁ u₁` (`has_limits_of_size.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[category.{v₁} J]`.
-/
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  hasLimitsOfShape : ∀ (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance
#align category_theory.limits.has_limits_of_size CategoryTheory.Limits.HasLimitsOfSize

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C
#align category_theory.limits.has_limits CategoryTheory.Limits.HasLimits

theorem HasLimits.hasLimitsOfShape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.hasLimitsOfShape J
#align category_theory.limits.has_limits.has_limits_of_shape CategoryTheory.Limits.HasLimits.hasLimitsOfShape

variable {J C}

-- see Note [lower instance priority]
instance (priority := 100) hasLimitOfHasLimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.hasLimit F
#align category_theory.limits.has_limit_of_has_limits_of_shape CategoryTheory.Limits.hasLimitOfHasLimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) hasLimitsOfShapeOfHasLimits {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.hasLimitsOfShape J
#align category_theory.limits.has_limits_of_shape_of_has_limits CategoryTheory.Limits.hasLimitsOfShapeOfHasLimits

-- Interface to the `has_limit` class.
/-- An arbitrary choice of limit cone for a functor. -/
def Limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone
#align category_theory.limits.limit.cone CategoryTheory.Limits.Limit.cone

/-- An arbitrary choice of limit object of a functor. -/
def limit (F : J ⥤ C) [HasLimit F] :=
  (Limit.cone F).X
#align category_theory.limits.limit CategoryTheory.Limits.limit

/-- The projection from the limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (Limit.cone F).π.app j
#align category_theory.limits.limit.π CategoryTheory.Limits.limit.π

@[simp]
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (Limit.cone F).X = limit F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.limit.cone_X CategoryTheory.Limits.limit.cone_x

@[simp]
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (Limit.cone F).π.app = limit.π _ :=
  rfl
#align category_theory.limits.limit.cone_π CategoryTheory.Limits.limit.cone_π

@[reassoc (attr := simp)]
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (Limit.cone F).w f
#align category_theory.limits.limit.w CategoryTheory.Limits.limit.w

/-- Evidence that the arbitrary choice of cone provied by `limit.cone F` is a limit cone. -/
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (Limit.cone F) :=
  (getLimitCone F).isLimit
#align category_theory.limits.limit.is_limit CategoryTheory.Limits.limit.isLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.X ⟶ limit F :=
  (limit.isLimit F).lift c
#align category_theory.limits.limit.lift CategoryTheory.Limits.limit.lift

@[simp]
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl
#align category_theory.limits.limit.is_limit_lift CategoryTheory.Limits.limit.isLimit_lift

@[reassoc (attr := simp)]
theorem limit.lift_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  IsLimit.fac _ c j
#align category_theory.limits.limit.lift_π CategoryTheory.Limits.limit.lift_π

/-- Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α
#align category_theory.limits.lim_map CategoryTheory.Limits.limMap

@[reassoc (attr := simp)]
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j
#align category_theory.limits.lim_map_π CategoryTheory.Limits.limMap_π

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ Limit.cone F :=
  (limit.isLimit F).liftConeMorphism c
#align category_theory.limits.limit.cone_morphism CategoryTheory.Limits.limit.coneMorphism

@[simp]
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).Hom = limit.lift F c :=
  rfl
#align category_theory.limits.limit.cone_morphism_hom CategoryTheory.Limits.limit.coneMorphism_hom

theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).Hom ≫ limit.π F j = c.π.app j := by simp
#align category_theory.limits.limit.cone_morphism_π CategoryTheory.Limits.limit.coneMorphism_π

@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _
#align category_theory.limits.limit.cone_point_unique_up_to_iso_hom_comp CategoryTheory.Limits.limit.conePointUniqueUpToIso_hom_comp

@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _
#align category_theory.limits.limit.cone_point_unique_up_to_iso_inv_comp CategoryTheory.Limits.limit.conePointUniqueUpToIso_inv_comp

theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    ∃! l : t.X ⟶ limit F, ∀ j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _
#align category_theory.limits.limit.exists_unique CategoryTheory.Limits.limit.existsUnique

/-- Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.X :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit
#align category_theory.limits.limit.iso_limit_cone CategoryTheory.Limits.limit.isoLimitCone

@[reassoc (attr := simp)]
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat
#align category_theory.limits.limit.iso_limit_cone_hom_π CategoryTheory.Limits.limit.isoLimitCone_hom_π

@[reassoc (attr := simp)]
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat
#align category_theory.limits.limit.iso_limit_cone_inv_π CategoryTheory.Limits.limit.isoLimitCone_inv_π

@[ext]
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w
#align category_theory.limits.limit.hom_ext CategoryTheory.Limits.limit.hom_ext

@[simp]
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cones.postcompose α).obj c) := by
  ext
  rw [assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
  rfl
#align category_theory.limits.limit.lift_map CategoryTheory.Limits.limit.lift_map

@[simp]
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (Limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self
#align category_theory.limits.limit.lift_cone CategoryTheory.Limits.limit.lift_cone

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W
#align category_theory.limits.limit.hom_iso CategoryTheory.Limits.limit.homIso

@[simp]
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} (f : ULift (W ⟶ limit F)) :
    (limit.homIso F W).hom f = (const J).map f.down ≫ (Limit.cone F).π :=
  (limit.isLimit F).homIso_hom f
#align category_theory.limits.limit.hom_iso_hom CategoryTheory.Limits.limit.homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W
#align category_theory.limits.limit.hom_iso' CategoryTheory.Limits.limit.homIso'

theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.X) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by aesop_cat
#align category_theory.limits.limit.lift_extend CategoryTheory.Limits.limit.lift_extend

/-- If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
theorem hasLimitOfIso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cones.postcompose α.hom).obj (Limit.cone F)
      isLimit :=
        { lift := fun s => limit.lift F ((Cones.postcompose α.inv).obj s)
          fac := fun s j =>
            by
            rw [Cones.postcompose_obj_π, NatTrans.comp_app, limit.cone_π, ← Category.assoc,
              limit.lift_π]
            simp
          uniq := fun s m w => by
            apply limit.hom_ext; intro j
            rw [limit.lift_π, Cones.postcompose_obj_π, NatTrans.comp_app, ← NatIso.app_inv,
              Iso.eq_comp_inv]
            simpa using w j } }
#align category_theory.limits.has_limit_of_iso CategoryTheory.Limits.hasLimitOfIso

-- See the construction of limits from products and equalizers
-- for an example usage.
/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
theorem HasLimit.ofConesIso {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
    (G : K ⥤ C) (h : F.cones ≅ G.cones) [HasLimit F] : HasLimit G :=
  HasLimit.mk ⟨_, IsLimit.ofNatIso (IsLimit.natIso (limit.isLimit F) ≪≫ h)⟩
#align category_theory.limits.has_limit.of_cones_iso CategoryTheory.Limits.HasLimit.ofConesIso

/-- The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w
#align category_theory.limits.has_limit.iso_of_nat_iso CategoryTheory.Limits.HasLimit.isoOfNatIso

@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _
#align category_theory.limits.has_limit.iso_of_nat_iso_hom_π CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π

@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _
#align category_theory.limits.has_limit.iso_of_nat_iso_inv_π CategoryTheory.Limits.HasLimit.isoOfNatIso_inv_π

@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cones.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _
#align category_theory.limits.has_limit.lift_iso_of_nat_iso_hom CategoryTheory.Limits.HasLimit.lift_isoOfNatIso_hom

@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cones.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _
#align category_theory.limits.has_limit.lift_iso_of_nat_iso_inv CategoryTheory.Limits.HasLimit.lift_isoOfNatIso_inv

/-- The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w
#align category_theory.limits.has_limit.iso_of_equivalence CategoryTheory.Limits.HasLimit.isoOfEquivalence

@[simp]
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp
#align category_theory.limits.has_limit.iso_of_equivalence_hom_π CategoryTheory.Limits.HasLimit.isoOfEquivalence_hom_π

@[simp]
theorem HasLimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    (HasLimit.isoOfEquivalence e w).inv ≫ limit.π F j = limit.π G (e.functor.obj j) ≫ w.hom.app j :=
  by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp
#align category_theory.limits.has_limit.iso_of_equivalence_inv_π CategoryTheory.Limits.HasLimit.isoOfEquivalence_inv_π

section Pre

variable (F) [HasLimit F] (E : K ⥤ J) [HasLimit (E ⋙ F)]

/-- The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((Limit.cone F).whisker E)
#align category_theory.limits.limit.pre CategoryTheory.Limits.limit.pre

@[reassoc (attr := simp)]
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  erw [IsLimit.fac]
  rfl
#align category_theory.limits.limit.pre_π CategoryTheory.Limits.limit.pre_π

@[simp]
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp
#align category_theory.limits.limit.lift_pre CategoryTheory.Limits.limit.lift_pre

variable {L : Type u₃} [Category.{v₃} L]

variable (D : L ⥤ K) [HasLimit (D ⋙ E ⋙ F)]

-- Porting note: added because instance not automatically synthesized
instance [h : HasLimit (D ⋙ E ⋙ F)] : HasLimit ((D ⋙ E) ⋙ F) where 
  exists_limit := by 
    rw [Functor.assoc]
    exact h.exists_limit
instance [h : HasLimit ((D ⋙ E) ⋙ F)] : HasLimit (D ⋙ E ⋙ F) where 
  exists_limit := by 
    rw [← Functor.assoc]
    exact h.exists_limit

@[simp]
theorem limit.pre_pre : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl
#align category_theory.limits.limit.pre_pre CategoryTheory.Limits.limit.pre_pre

variable {E F}

/-- -
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E =
      (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫ (limit.isoLimitCone s).inv :=
  by aesop_cat
#align category_theory.limits.limit.pre_eq CategoryTheory.Limits.limit.pre_eq

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]

variable (F) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (mapCone G (Limit.cone F))
#align category_theory.limits.limit.post CategoryTheory.Limits.limit.post

@[reassoc (attr := simp)]
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  erw [IsLimit.fac]
  rfl
#align category_theory.limits.limit.post_π CategoryTheory.Limits.limit.post_π

@[simp]
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (mapCone G c) := by
  ext
  rw [assoc, limit.post_π, ← G.map_comp, limit.lift_π, limit.lift_π]
  rfl
#align category_theory.limits.limit.lift_post CategoryTheory.Limits.limit.lift_post

@[simp]
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [HasLimit ((F ⋙ G) ⋙ H)] :
    -- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals 
    -- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H))
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
  by ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl
#align category_theory.limits.limit.post_post CategoryTheory.Limits.limit.post_post

end Post

theorem limit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasLimit F] [HasLimit (E ⋙ F)] [HasLimit (F ⋙ G)]
    [HasLimit ((E ⋙ F) ⋙ G)] :-- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs 
            -- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or
            G.map
          (limit.pre F E) ≫
        limit.post (E ⋙ F) G =
      limit.post F G ≫ limit.pre (F ⋙ G) E := by
  ext ; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]
#align category_theory.limits.limit.pre_post CategoryTheory.Limits.limit.pre_post

open CategoryTheory.Equivalence

instance hasLimitEquivalenceComp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (Limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }
#align category_theory.limits.has_limit_equivalence_comp CategoryTheory.Limits.hasLimitEquivalenceComp

-- Porting note: testing whether this still needed 
-- attribute [local elab_without_expected_type] inv_fun_id_assoc

-- not entirely sure why this is needed
/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
theorem hasLimitOfEquivalenceComp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  haveI : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimitEquivalenceComp e.symm
  apply hasLimitOfIso (e.invFunIdAssoc F)
#align category_theory.limits.has_limit_of_equivalence_comp CategoryTheory.Limits.hasLimitOfEquivalenceComp

-- `has_limit_comp_equivalence` and `has_limit_of_comp_equivalence`
-- are proved in `category_theory/adjunction/limits.lean`.
section LimFunctor

variable [HasLimitsOfShape J C]

section

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps obj]
def lim : (J ⥤ C) ⥤ C where
  obj F := limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    erw [limMap_π, Category.id_comp, Category.comp_id]
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    erw [assoc, IsLimit.fac, IsLimit.fac, ← assoc, IsLimit.fac, assoc]; rfl
#align category_theory.limits.lim CategoryTheory.Limits.lim

end

variable {G : J ⥤ C} (α : F ⟶ G)

-- We generate this manually since `simps` gives it a weird name.
@[simp]
theorem limMap_eq_limMap : lim.map α = limMap α :=
  rfl
#align category_theory.limits.lim_map_eq_lim_map CategoryTheory.Limits.limMap_eq_limMap

theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp
#align category_theory.limits.limit.map_pre CategoryTheory.Limits.limit.map_pre

theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp [← category.assoc]
#align category_theory.limits.limit.map_pre' CategoryTheory.Limits.limit.map_pre'

theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv := by 
  aesop_cat
#align category_theory.limits.limit.id_pre CategoryTheory.Limits.limit.id_pre

theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    /- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
     H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]
#align category_theory.limits.limit.map_post CategoryTheory.Limits.limit.map_post

/-- The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def limYoneda :
    lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅ CategoryTheory.cones J C := by
  refine 
    NatIso.ofComponents (fun F => NatIso.ofComponents (fun W => limit.homIso F (unop W))  ?_) ?_ 
  · intro X Y f 
    dsimp [yoneda,uliftFunctor,cones]
    funext g 
    dsimp [const,cones]
    apply NatTrans.ext
    aesop_cat
  · intro X Y f
    dsimp [yoneda,uliftFunctor]
    ext Z
    dsimp 
    funext g 
    dsimp [const,cones]
    apply NatTrans.ext
    aesop_cat
#align category_theory.limits.lim_yoneda CategoryTheory.Limits.limYoneda

/-- The constant functor and limit functor are adjoint to each other-/
def constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim where
  homEquiv c g :=
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun j => f ≫ limit.π _ _
          naturality := by aesop_cat }
      left_inv := fun _ => NatTrans.ext _ _ <| funext fun j => limit.lift_π _ _
      right_inv := fun α => limit.hom_ext fun j => limit.lift_π _ _ }
  unit :=
    { app := fun c => limit.lift _ ⟨_, 𝟙 _⟩
      naturality := fun _ _ _ => by aesop_cat }
  counit :=
    { app := fun g =>
        { app := limit.π _
          naturality := by aesop_cat }
      naturality := fun _ _ _ => by aesop_cat }
  homEquiv_unit := fun {c} {f} {g} => limit.hom_ext <| fun j => by simp
  homEquiv_counit {c} {g} {f} := NatTrans.ext _ _ <| funext fun j => rfl
#align category_theory.limits.const_lim_adj CategoryTheory.Limits.constLimAdj

instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, constLimAdj⟩

end LimFunctor

instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α
#align category_theory.limits.lim_map_mono' CategoryTheory.Limits.limMap_mono'

instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [∀ j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
    limit.hom_ext fun j => (cancel_mono (α.app j)).1 <| by simpa using h =≫ limit.π _ j⟩
#align category_theory.limits.lim_map_mono CategoryTheory.Limits.limMap_mono

/-- We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasLimitsOfShapeOfEquivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimitOfEquivalenceComp e
#align category_theory.limits.has_limits_of_shape_of_equivalence CategoryTheory.Limits.hasLimitsOfShapeOfEquivalence

variable (C)

/-- `has_limits_of_size_shrink.{v u} C` tries to obtain `has_limits_of_size.{v u} C`
from some other `has_limits_of_size C`.
-/
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C :=
  ⟨fun J _ => hasLimitsOfShapeOfEquivalence (UliftHomUliftCategory.equiv.{v₂, u₂} J).symm⟩
#align category_theory.limits.has_limits_of_size_shrink CategoryTheory.Limits.hasLimitsOfSizeShrink

instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C
#align category_theory.limits.has_smallest_limits_of_has_limits CategoryTheory.Limits.hasSmallestLimitsOfHasLimits

end Limit

section Colimit

/-- `colimit_cocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
-- @[nolint has_nonempty_instance] -- Porting note: removed
structure ColimitCocone (F : J ⥤ C) where
  cocone : Cocone F
  isColimit : IsColimit cocone
#align category_theory.limits.colimit_cocone CategoryTheory.Limits.ColimitCocone

/-- `has_colimit F` represents the mere existence of a colimit for `F`. -/
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  exists_colimit : Nonempty (ColimitCocone F)
#align category_theory.limits.has_colimit CategoryTheory.Limits.HasColimit

theorem HasColimit.mk {F : J ⥤ C} (d : ColimitCocone F) : HasColimit F :=
  ⟨Nonempty.intro d⟩
#align category_theory.limits.has_colimit.mk CategoryTheory.Limits.HasColimit.mk

/-- Use the axiom of choice to extract explicit `colimit_cocone F` from `has_colimit F`. -/
def getColimitCocone (F : J ⥤ C) [HasColimit F] : ColimitCocone F :=
  Classical.choice <| HasColimit.exists_colimit
#align category_theory.limits.get_colimit_cocone CategoryTheory.Limits.getColimitCocone

variable (J C)

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class HasColimitsOfShape : Prop where
  HasColimit : ∀ F : J ⥤ C, HasColimit F := by infer_instance
#align category_theory.limits.has_colimits_of_shape CategoryTheory.Limits.HasColimitsOfShape

/-- `C` has all colimits of size `v₁ u₁` (`has_colimits_of_size.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[category.{v₁} J]`.
-/
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  hasColimitsOfShape : ∀ (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance
#align category_theory.limits.has_colimits_of_size CategoryTheory.Limits.HasColimitsOfSize

/-- `C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/
abbrev HasColimits (C : Type u) [Category.{v} C] : Prop :=
  HasColimitsOfSize.{v, v} C
#align category_theory.limits.has_colimits CategoryTheory.Limits.HasColimits

theorem HasColimits.hasColimitsOfShape {C : Type u} [Category.{v} C] [HasColimits C] (J : Type v)
    [Category.{v} J] : HasColimitsOfShape J C :=
  HasColimitsOfSize.hasColimitsOfShape J
#align category_theory.limits.has_colimits.has_colimits_of_shape CategoryTheory.Limits.HasColimits.hasColimitsOfShape

variable {J C}

-- see Note [lower instance priority]
instance (priority := 100) hasColimitOfHasColimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfShape J C] (F : J ⥤ C) : HasColimit F :=
  HasColimitsOfShape.HasColimit F
#align category_theory.limits.has_colimit_of_has_colimits_of_shape CategoryTheory.Limits.hasColimitOfHasColimitsOfShape

-- see Note [lower instance priority]
instance (priority := 100) hasColimitsOfShapeOfHasColimitsOfSize {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfShape J C :=
  HasColimitsOfSize.hasColimitsOfShape J
#align category_theory.limits.has_colimits_of_shape_of_has_colimits_of_size CategoryTheory.Limits.hasColimitsOfShapeOfHasColimitsOfSize

-- Interface to the `has_colimit` class.
/-- An arbitrary choice of colimit cocone of a functor. -/
def Colimit.cocone (F : J ⥤ C) [HasColimit F] : Cocone F :=
  (getColimitCocone F).cocone
#align category_theory.limits.colimit.cocone CategoryTheory.Limits.Colimit.cocone

/-- An arbitrary choice of colimit object of a functor. -/
def colimit (F : J ⥤ C) [HasColimit F] :=
  (Colimit.cocone F).X
#align category_theory.limits.colimit CategoryTheory.Limits.colimit

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι (F : J ⥤ C) [HasColimit F] (j : J) : F.obj j ⟶ colimit F :=
  (Colimit.cocone F).ι.app j
#align category_theory.limits.colimit.ι CategoryTheory.Limits.colimit.ι

@[simp]
theorem colimit.cocone_ι {F : J ⥤ C} [HasColimit F] (j : J) :
    (Colimit.cocone F).ι.app j = colimit.ι _ j :=
  rfl
#align category_theory.limits.colimit.cocone_ι CategoryTheory.Limits.colimit.cocone_ι

@[simp]
theorem colimit.cocone_x {F : J ⥤ C} [HasColimit F] : (Colimit.cocone F).X = colimit F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.colimit.cocone_X CategoryTheory.Limits.colimit.cocone_x

@[reassoc (attr := simp)]
theorem colimit.w (F : J ⥤ C) [HasColimit F] {j j' : J} (f : j ⟶ j') :
    F.map f ≫ colimit.ι F j' = colimit.ι F j :=
  (Colimit.cocone F).w f
#align category_theory.limits.colimit.w CategoryTheory.Limits.colimit.w

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.isColimit (F : J ⥤ C) [HasColimit F] : IsColimit (Colimit.cocone F) :=
  (getColimitCocone F).isColimit
#align category_theory.limits.colimit.is_colimit CategoryTheory.Limits.colimit.isColimit

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [HasColimit F] (c : Cocone F) : colimit F ⟶ c.X :=
  (colimit.isColimit F).desc c
#align category_theory.limits.colimit.desc CategoryTheory.Limits.colimit.desc

@[simp]
theorem colimit.isColimit_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.isColimit F).desc c = colimit.desc F c :=
  rfl
#align category_theory.limits.colimit.is_colimit_desc CategoryTheory.Limits.colimit.isColimit_desc

/-- We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[reassoc (attr := simp)]
theorem colimit.ι_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  IsColimit.fac _ c j
#align category_theory.limits.colimit.ι_desc CategoryTheory.Limits.colimit.ι_desc

/-- Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
  IsColimit.map (colimit.isColimit F) _ α
#align category_theory.limits.colim_map CategoryTheory.Limits.colimMap

@[reassoc (attr := simp)]
theorem ι_colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) (j : J) :
    colimit.ι F j ≫ colimMap α = α.app j ≫ colimit.ι G j :=
  colimit.ι_desc _ j
#align category_theory.limits.ι_colim_map CategoryTheory.Limits.ι_colimMap

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) : Colimit.cocone F ⟶ c :=
  (colimit.isColimit F).descCoconeMorphism c
#align category_theory.limits.colimit.cocone_morphism CategoryTheory.Limits.colimit.coconeMorphism

@[simp]
theorem colimit.coconeMorphism_hom {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.coconeMorphism c).Hom = colimit.desc F c :=
  rfl
#align category_theory.limits.colimit.cocone_morphism_hom CategoryTheory.Limits.colimit.coconeMorphism_hom

theorem colimit.ι_coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ (colimit.coconeMorphism c).Hom = c.ι.app j := by simp
#align category_theory.limits.colimit.ι_cocone_morphism CategoryTheory.Limits.colimit.ι_coconeMorphism

@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_hom {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc).hom = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _
#align category_theory.limits.colimit.comp_cocone_point_unique_up_to_iso_hom CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_inv {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)).inv = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _
#align category_theory.limits.colimit.comp_cocone_point_unique_up_to_iso_inv CategoryTheory.Limits.colimit.comp_coconePointUniqueUpToIso_inv

theorem colimit.existsUnique {F : J ⥤ C} [HasColimit F] (t : Cocone F) :
    ∃! d : colimit F ⟶ t.X, ∀ j, colimit.ι F j ≫ d = t.ι.app j :=
  (colimit.isColimit F).existsUnique _
#align category_theory.limits.colimit.exists_unique CategoryTheory.Limits.colimit.existsUnique

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.isoColimitCocone {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) :
    colimit F ≅ t.cocone.X :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) t.isColimit
#align category_theory.limits.colimit.iso_colimit_cocone CategoryTheory.Limits.colimit.isoColimitCocone

@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_hom {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    colimit.ι F j ≫ (colimit.isoColimitCocone t).hom = t.cocone.ι.app j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat
#align category_theory.limits.colimit.iso_colimit_cocone_ι_hom CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom

@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_inv {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    t.cocone.ι.app j ≫ (colimit.isoColimitCocone t).inv = colimit.ι F j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat
#align category_theory.limits.colimit.iso_colimit_cocone_ι_inv CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv

@[ext]
theorem colimit.hom_ext {F : J ⥤ C} [HasColimit F] {X : C} {f f' : colimit F ⟶ X}
    (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
  (colimit.isColimit F).hom_ext w
#align category_theory.limits.colimit.hom_ext CategoryTheory.Limits.colimit.hom_ext

@[simp]
theorem colimit.desc_cocone {F : J ⥤ C} [HasColimit F] :
    colimit.desc F (Colimit.cocone F) = 𝟙 (colimit F) :=
  (colimit.isColimit _).desc_self
#align category_theory.limits.colimit.desc_cocone CategoryTheory.Limits.colimit.desc_cocone

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W
#align category_theory.limits.colimit.hom_iso CategoryTheory.Limits.colimit.homIso

@[simp]
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} (f : ULift (colimit F ⟶ W)) :
    (colimit.homIso F W).hom f = (Colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom f
#align category_theory.limits.colimit.hom_iso_hom CategoryTheory.Limits.colimit.homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W
#align category_theory.limits.colimit.hom_iso' CategoryTheory.Limits.colimit.homIso'

theorem colimit.desc_extend (F : J ⥤ C) [HasColimit F] (c : Cocone F) {X : C} (f : c.X ⟶ X) :
    colimit.desc F (c.extend f) = colimit.desc F c ≫ f := by ext1; rw [← Category.assoc]; simp
#align category_theory.limits.colimit.desc_extend CategoryTheory.Limits.colimit.desc_extend

-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
/-- If `F` has a colimit, so does any naturally isomorphic functor.
-/
theorem hasColimitOfIso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocones.precompose α.hom).obj (Colimit.cocone F)
      isColimit :=
        { desc := fun s => colimit.desc F ((Cocones.precompose α.inv).obj s)
          fac := fun s j =>
            by
            rw [Cocones.precompose_obj_ι, NatTrans.comp_app, colimit.cocone_ι]
            rw [Category.assoc, colimit.ι_desc, ← NatIso.app_hom, ← Iso.eq_inv_comp]; rfl
          uniq := fun s m w => by
            apply colimit.hom_ext; intro j
            rw [colimit.ι_desc, Cocones.precompose_obj_ι, NatTrans.comp_app, ← NatIso.app_inv,
              Iso.eq_inv_comp]
            simpa using w j } }
#align category_theory.limits.has_colimit_of_iso CategoryTheory.Limits.hasColimitOfIso

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofNatIso (IsColimit.natIso (colimit.isColimit F) ≪≫ h)⟩
#align category_theory.limits.has_colimit.of_cocones_iso CategoryTheory.Limits.HasColimit.ofCoconesIso

/-- The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def HasColimit.isoOfNatIso {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G) :
    colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfNatIso (colimit.isColimit F) (colimit.isColimit G) w
#align category_theory.limits.has_colimit.iso_of_nat_iso CategoryTheory.Limits.HasColimit.isoOfNatIso

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_hom {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι F j ≫ (HasColimit.isoOfNatIso w).hom = w.hom.app j ≫ colimit.ι G j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _
#align category_theory.limits.has_colimit.iso_of_nat_iso_ι_hom CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_hom

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_inv {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι G j ≫ (HasColimit.isoOfNatIso w).inv = w.inv.app j ≫ colimit.ι F j :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _
#align category_theory.limits.has_colimit.iso_of_nat_iso_ι_inv CategoryTheory.Limits.HasColimit.isoOfNatIso_ι_inv

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_hom_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).hom ≫ colimit.desc G t =
      colimit.desc F ((Cocones.precompose w.hom).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _
#align category_theory.limits.has_colimit.iso_of_nat_iso_hom_desc CategoryTheory.Limits.HasColimit.isoOfNatIso_hom_desc

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_inv_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).inv ≫ colimit.desc F t =
      colimit.desc G ((Cocones.precompose w.inv).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _
#align category_theory.limits.has_colimit.iso_of_nat_iso_inv_desc CategoryTheory.Limits.HasColimit.isoOfNatIso_inv_desc

/-- The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def HasColimit.isoOfEquivalence {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w
#align category_theory.limits.has_colimit.iso_of_equivalence CategoryTheory.Limits.HasColimit.isoOfEquivalence

@[simp]
theorem HasColimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    colimit.ι F j ≫ (HasColimit.isoOfEquivalence e w).hom =
      F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]
#align category_theory.limits.has_colimit.iso_of_equivalence_hom_π CategoryTheory.Limits.HasColimit.isoOfEquivalence_hom_π

@[simp]
theorem HasColimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    colimit.ι G k ≫ (HasColimit.isoOfEquivalence e w).inv =
      G.map (e.counitInv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]
#align category_theory.limits.has_colimit.iso_of_equivalence_inv_π CategoryTheory.Limits.HasColimit.isoOfEquivalence_inv_π

section Pre

variable (F) [HasColimit F] (E : K ⥤ J) [HasColimit (E ⋙ F)]

/-- The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((Colimit.cocone F).whisker E)
#align category_theory.limits.colimit.pre CategoryTheory.Limits.colimit.pre

@[reassoc (attr := simp)]
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) := by
  erw [IsColimit.fac]
  rfl
#align category_theory.limits.colimit.ι_pre CategoryTheory.Limits.colimit.ι_pre

@[reassoc (attr := simp)]
theorem colimit.pre_desc (c : Cocone F) :
    colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) := by
  ext; rw [← assoc, colimit.ι_pre]; simp
#align category_theory.limits.colimit.pre_desc CategoryTheory.Limits.colimit.pre_desc

variable {L : Type u₃} [Category.{v₃} L]

variable (D : L ⥤ K) [HasColimit (D ⋙ E ⋙ F)]

-- Porting note : added these instances 
instance [h : HasColimit (D ⋙ E ⋙ F)] : HasColimit ((D ⋙ E) ⋙ F) where 
  exists_colimit := by 
    rw [Functor.assoc]
    exact h.exists_colimit
instance [h : HasColimit ((D ⋙ E) ⋙ F)] : HasColimit (D ⋙ E ⋙ F) where 
  exists_colimit := by 
    rw [← Functor.assoc]
    exact h.exists_colimit


@[simp]
theorem colimit.pre_pre : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc, colimit.ι_pre, colimit.ι_pre]
  letI : HasColimit ((D ⋙ E) ⋙ F) := show HasColimit (D ⋙ E ⋙ F) by infer_instance
  exact (colimit.ι_pre F (D ⋙ E) j).symm
#align category_theory.limits.colimit.pre_pre CategoryTheory.Limits.colimit.pre_pre

variable {E F}

/-- -
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
theorem colimit.pre_eq (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F) :
    colimit.pre F E =
      (colimit.isoColimitCocone s).hom ≫
        s.isColimit.desc (t.cocone.whisker E) ≫ (colimit.isoColimitCocone t).inv :=
  by aesop_cat
#align category_theory.limits.colimit.pre_eq CategoryTheory.Limits.colimit.pre_eq

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]

variable (F) [HasColimit F] (G : C ⥤ D) [HasColimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (mapCocone G (Colimit.cocone F))
#align category_theory.limits.colimit.post CategoryTheory.Limits.colimit.post

@[reassoc (attr := simp)]
theorem colimit.ι_post (j : J) : colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) :=
  by
  erw [IsColimit.fac]
  rfl
#align category_theory.limits.colimit.ι_post CategoryTheory.Limits.colimit.ι_post

@[simp]
theorem colimit.post_desc (c : Cocone F) :
    colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (mapCocone G c) := by
  ext
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_desc, colimit.ι_desc]
  rfl
#align category_theory.limits.colimit.post_desc CategoryTheory.Limits.colimit.post_desc

@[simp]
theorem colimit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [HasColimit ((F ⋙ G) ⋙ H)]
    -- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals 
    -- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H))
    : colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_post]
  exact (colimit.ι_post F (G ⋙ H) j).symm
#align category_theory.limits.colimit.post_post CategoryTheory.Limits.colimit.post_post

end Post

theorem colimit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasColimit F] [HasColimit (E ⋙ F)] [HasColimit (F ⋙ G)] [H : HasColimit ((E ⋙ F) ⋙ G)] :
    -- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs 
    -- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) = 
      (@colimit.pre _ _ _ (F ⋙ G) _ E H ≫ colimit.post F G : _) := by
  ext j
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_pre, ← assoc]
  letI : HasColimit (E ⋙ F ⋙ G) := show HasColimit ((E ⋙ F) ⋙ G) by infer_instance
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
#align category_theory.limits.colimit.pre_post CategoryTheory.Limits.colimit.pre_post

open CategoryTheory.Equivalence

instance hasColimitEquivalenceComp (e : K ≌ J) [HasColimit F] : HasColimit (e.functor ⋙ F) :=
  HasColimit.mk
    { cocone := Cocone.whisker e.functor (Colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }
#align category_theory.limits.has_colimit_equivalence_comp CategoryTheory.Limits.hasColimitEquivalenceComp

/-- If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
theorem hasColimitOfEquivalenceComp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F := by
  haveI : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimitEquivalenceComp e.symm
  apply hasColimitOfIso (e.invFunIdAssoc F).symm
#align category_theory.limits.has_colimit_of_equivalence_comp CategoryTheory.Limits.hasColimitOfEquivalenceComp

section ColimFunctor

variable [HasColimitsOfShape J C]

section

-- attribute [local simp] colimMap

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps obj]
def colim : (J ⥤ C) ⥤ C where
  obj F := colimit F
  map α := colimMap α
  map_id F := by aesop_cat
  map_comp α β := by aesop_cat
#align category_theory.limits.colim CategoryTheory.Limits.colim

end

variable {G : J ⥤ C} (α : F ⟶ G)

@[reassoc (attr := simp)]
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j := by
  apply IsColimit.fac
#align category_theory.limits.colimit.ι_map CategoryTheory.Limits.colimit.ι_map

@[simp]
theorem colimit.map_desc (c : Cocone G) :
    colim.map α ≫ colimit.desc G c = colimit.desc F ((Cocones.precompose α).obj c) := by
  apply Limits.colimit.hom_ext; intro 
  rw [← assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]; rfl
#align category_theory.limits.colimit.map_desc CategoryTheory.Limits.colimit.map_desc

theorem colimit.pre_map [HasColimitsOfShape K C] (E : K ⥤ J) :
    colimit.pre F E ≫ colim.map α = colim.map (whiskerLeft E α) ≫ colimit.pre G E := by
  ext
  rw [← assoc, colimit.ι_pre, colimit.ι_map, ← assoc, colimit.ι_map, assoc, colimit.ι_pre]
  rfl
#align category_theory.limits.colimit.pre_map CategoryTheory.Limits.colimit.pre_map

theorem colimit.pre_map' [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    colimit.pre F E₁ = colim.map (whiskerRight α F) ≫ colimit.pre F E₂ := by
  ext1; simp [← Category.assoc]
#align category_theory.limits.colimit.pre_map' CategoryTheory.Limits.colimit.pre_map'

theorem colimit.pre_id (F : J ⥤ C) : colimit.pre F (𝟭 _) = colim.map (Functor.leftUnitor F).hom :=
  by aesop_cat
#align category_theory.limits.colimit.pre_id CategoryTheory.Limits.colimit.pre_id

theorem colimit.map_post {D : Type u'} [Category.{v'} D] [HasColimitsOfShape J D]
    (H : C ⥤ D) :/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
             H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
          colimit.post
          F H ≫
        H.map (colim.map α) =
      colim.map (whiskerRight α H) ≫ colimit.post G H := by
  ext
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_map, H.map_comp]
  rw [← assoc, colimit.ι_map, assoc, colimit.ι_post]
  rfl
#align category_theory.limits.colimit.map_post CategoryTheory.Limits.colimit.map_post

/-- The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅
      CategoryTheory.cocones J C := by 
  refine 
    NatIso.ofComponents (fun F => NatIso.ofComponents (colimit.homIso (unop F)) ?_) ?_ 
  · intro X Y f 
    dsimp [coyoneda,uliftFunctor,cocones]
    funext g 
    dsimp [const,cocones]
    apply NatTrans.ext 
    aesop_cat
  · intro X Y f 
    dsimp [coyoneda,uliftFunctor]
    ext Z
    dsimp 
    funext g 
    dsimp [const,cocones]
    apply NatTrans.ext
    aesop_cat
#align category_theory.limits.colim_coyoneda CategoryTheory.Limits.colimCoyoneda

/-- The colimit functor and constant functor are adjoint to each other
-/
def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J where
  homEquiv f c :=
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g
          naturality := by aesop_cat }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := fun _ => colimit.hom_ext fun j => colimit.ι_desc _ _
      right_inv := fun _ => NatTrans.ext _ _ <| funext fun j => colimit.ι_desc _ _ }
  unit :=
    { app := fun g =>
        { app := colimit.ι _
          naturality := by aesop_cat }
      naturality := by aesop_cat }
  counit :=
    { app := fun c => colimit.desc _ ⟨_, 𝟙 _⟩
      naturality := by aesop_cat }
  homEquiv_unit := fun {c} {f} {g} => NatTrans.ext _ _ <| funext fun _ => rfl
  homEquiv_counit {c} {f} {g} := colimit.hom_ext <| fun _ => by simp
#align category_theory.limits.colim_const_adj CategoryTheory.Limits.colimConstAdj

instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, colimConstAdj⟩

end ColimFunctor

instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α
#align category_theory.limits.colim_map_epi' CategoryTheory.Limits.colimMap_epi'

instance colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [∀ j, Epi (α.app j)] :
    Epi (colimMap α) :=
  ⟨fun {Z} u v h =>
    colimit.hom_ext fun j => (cancel_epi (α.app j)).1 <| by simpa using colimit.ι _ j ≫= h⟩
#align category_theory.limits.colim_map_epi CategoryTheory.Limits.colimMap_epi

/-- We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasColimitsOfShapeOfEquivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasColimitsOfShape J C] : HasColimitsOfShape J' C := by
  constructor
  intro F
  apply hasColimitOfEquivalenceComp e
#align category_theory.limits.has_colimits_of_shape_of_equivalence CategoryTheory.Limits.hasColimitsOfShapeOfEquivalence

variable (C)

/-- `has_colimits_of_size_shrink.{v u} C` tries to obtain `has_colimits_of_size.{v u} C`
from some other `has_colimits_of_size C`.
-/
theorem hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasColimitsOfSize.{v₁, u₁} C :=
  ⟨fun J _ => hasColimitsOfShapeOfEquivalence (UliftHomUliftCategory.equiv.{v₂, u₂} J).symm⟩
#align category_theory.limits.has_colimits_of_size_shrink CategoryTheory.Limits.hasColimitsOfSizeShrink

instance (priority := 100) hasSmallestColimitsOfHasColimits [HasColimits C] :
    HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C
#align category_theory.limits.has_smallest_colimits_of_has_colimits CategoryTheory.Limits.hasSmallestColimitsOfHasColimits

end Colimit

section Opposite

/-- If `t : cone F` is a limit cone, then `t.op : cocone F.op` is a colimit cocone.
-/
def IsLimit.op {t : Cone F} (P : IsLimit t) : IsColimit t.op where
  desc s := (P.lift s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl 
    · dsimp
      intro j
      rw [← w]
      rfl
#align category_theory.limits.is_limit.op CategoryTheory.Limits.IsLimit.op

/-- If `t : cocone F` is a colimit cocone, then `t.op : cone F.op` is a limit cone.
-/
def IsColimit.op {t : Cocone F} (P : IsColimit t) : IsLimit t.op where
  lift s := (P.desc s.unop).op
  fac s j := congrArg Quiver.Hom.op (P.fac s.unop (unop j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.unop m.unop]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
#align category_theory.limits.is_colimit.op CategoryTheory.Limits.IsColimit.op

/-- If `t : cone F.op` is a limit cone, then `t.unop : cocone F` is a colimit cocone.
-/
def IsLimit.unop {t : Cone F.op} (P : IsLimit t) : IsColimit t.unop where
  desc s := (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  -- Porting note: things `op j` is `IsLimit.op j`
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
#align category_theory.limits.is_limit.unop CategoryTheory.Limits.IsLimit.unop

/-- If `t : cocone F.op` is a colimit cocone, then `t.unop : cone F.` is a limit cone.
-/
def IsColimit.unop {t : Cocone F.op} (P : IsColimit t) : IsLimit t.unop where
  lift s := (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  -- Porting note: things `op j` is `IsLimit.op j`
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl
#align category_theory.limits.is_colimit.unop CategoryTheory.Limits.IsColimit.unop

/-- `t : cone F` is a limit cone if and only is `t.op : cocone F.op` is a colimit cocone.
-/
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op fun P =>
    P.unop.ofIsoLimit (Cones.ext (Iso.refl _) (by aesop_cat))
#align category_theory.limits.is_limit_equiv_is_colimit_op CategoryTheory.Limits.isLimitEquivIsColimitOp

/-- `t : cocone F` is a colimit cocone if and only is `t.op : cone F.op` is a limit cone.
-/
def isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op :=
  equivOfSubsingletonOfSubsingleton IsColimit.op fun P =>
    P.unop.ofIsoColimit (Cocones.ext (Iso.refl _) (by aesop_cat))
#align category_theory.limits.is_colimit_equiv_is_limit_op CategoryTheory.Limits.isColimitEquivIsLimitOp

end Opposite

