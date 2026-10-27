/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Existence of limits and colimits

In `CategoryTheory.Limits.IsLimit` we defined `IsLimit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `LimitCone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `HasLimit F`, asserting the mere existence of some limit cone for `F`.

`HasLimit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `HasLimit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `HasLimit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.pt ⟶ limit F`, the universal morphism from any other `c : Cone F`, etc.

Key to using the `HasLimit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `HasLimitsOfShape J C` and `HasLimits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `IsLimit`,
and then a result in terms of `HasLimit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `HasLimit`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category theory universes].
universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]
variable {F : J ⥤ C}

to_dual_name_hint Lift Desc

section Limit

/-- `LimitCone F` contains a cone over `F` together with the information that it is a limit. -/
structure LimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

/-- `ColimitCocone F` contains a cocone over `F` together with the information that it is a
colimit. -/
@[to_dual]
structure ColimitCocone (F : J ⥤ C) where
  /-- The cocone itself -/
  cocone : Cocone F
  /-- The proof that it is the colimit cocone -/
  isColimit : IsColimit cocone

/-- `HasLimit F` represents the mere existence of a limit for `F`. -/
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (LimitCone F)

/-- `HasColimit F` represents the mere existence of a colimit for `F`. -/
@[to_dual]
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  /-- There exists a colimit for `F` -/
  exists_colimit : Nonempty (ColimitCocone F)

@[to_dual]
theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `LimitCone F` from `HasLimit F`. -/
@[no_expose, to_dual
/-- Use the axiom of choice to extract explicit `ColimitCocone F` from `HasColimit F`. -/]
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit

variable (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class HasLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_limit : ∀ F : J ⥤ C, HasLimit F := by infer_instance

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
@[to_dual]
class HasColimitsOfShape : Prop where
  /-- All `F : J ⥤ C` have colimits for a fixed `J` -/
  has_colimit : ∀ F : J ⥤ C, HasColimit F := by infer_instance

/-- `C` has all limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have limits -/
  has_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance

/-- `C` has all colimits of size `v₁ u₁` (`HasColimitsOfSize.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the shape universes `v₁, u₁` would default
-- to universe output parameters. See Note [universe output parameters and typeclass caching].
@[to_dual, univ_out_params, pp_with_univ]
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All `F : J ⥤ C` have colimits for all small `J` -/
  has_colimits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
@[to_dual
/-- `C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/]
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C

@[to_dual]
theorem HasLimits.has_limits_of_shape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

variable {J C}

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.has_limit F

-- see Note [lower instance priority]
@[to_dual]
instance (priority := 100) {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

-- Interface to the `HasLimit` class.
/-- An arbitrary choice of limit cone for a functor. -/
@[to_dual colimit.cocone /-- An arbitrary choice of colimit cocone of a functor. -/]
def limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone

/-- An arbitrary choice of limit object of a functor. -/
@[to_dual (attr := implicit_reducible) /-- An arbitrary choice of colimit object of a functor. -/]
def limit (F : J ⥤ C) [HasLimit F] :=
  (limit.cone F).pt

/-- The projection from the limit object to a value of the functor. -/
@[to_dual (attr := implicit_reducible) ι
/-- The coprojection from a value of the functor to the colimit object. -/]
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j

theorem limit.π_comp_eqToHom (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j') :
    limit.π F j ≫ eqToHom (by subst hj; rfl) = limit.π F j' := by
  subst hj
  simp

@[to_dual existing (attr := reassoc) π_comp_eqToHom]
theorem colimit.eqToHom_comp_ι (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j') :
    eqToHom (by subst hj; rfl) ≫ colimit.ι F j = colimit.ι F j' := by
  subst hj
  simp

@[to_dual (attr := simp)]
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (limit.cone F).pt = limit F :=
  rfl

@[to_dual (attr := simp) cocone_ι]
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π _ :=
  rfl

@[to_dual (attr := reassoc (attr := simp))]
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `limit.cone F` is a limit cone. -/
@[to_dual
/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/]
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  (getLimitCone F).isLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
@[to_dual
/-- The morphism from the colimit object to the cone point of any other cocone. -/]
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  (limit.isLimit F).lift c

@[to_dual (attr := simp)]
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl

@[to_dual (attr := reassoc (attr := simp)) ι_desc]
theorem limit.lift_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  IsLimit.fac _ c j

/-- Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
@[to_dual
/-- Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/]
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α

@[to_dual (attr := reassoc (attr := simp)) ι_colimMap]
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
@[to_dual /-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/]
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ limit.cone F :=
  (limit.isLimit F).liftConeMorphism c

@[to_dual (attr := simp)]
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).hom = limit.lift F c :=
  rfl

@[to_dual ι_coconeMorphism]
theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).hom ≫ limit.π F j = c.π.app j := by simp

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[to_dual]
theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    ∃! l : t.pt ⟶ limit F, ∀ j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _

/-- Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point. -/
@[to_dual
/-- Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone
point. -/]
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_inv]
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := reassoc (attr := simp)) isoColimitCocone_ι_hom]
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  simp

@[to_dual (attr := ext)]
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w

@[to_dual]
instance isIso_limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [IsIso α] :
    IsIso (limMap α) :=
  ⟨limMap (inv α), by cat_disch , by cat_disch⟩

@[to_dual (attr := reassoc (attr := simp)) map_desc]
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cone.postcompose α).obj c) := by
  ext
  rw [assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
  rfl

@[to_dual (attr := simp)]
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W

@[simp]
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} :
    (limit.homIso F W).hom = ↾fun f ↦ (const J).map f.down ≫ (limit.cone F).π :=
  (limit.isLimit F).homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W

@[to_dual]
theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by cat_disch

/-- If a functor `F` has a limit, so does any naturally isomorphic functor. -/
@[to_dual none]
theorem hasLimit_of_iso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cone.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

@[to_dual]
theorem hasLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasLimit F ↔ HasLimit G :=
  ⟨fun _ ↦ hasLimit_of_iso α, fun _ ↦ hasLimit_of_iso α.symm⟩

-- See the construction of limits from products and equalizers
-- for an example usage.
/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
theorem HasLimit.ofConesIso {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
    (G : K ⥤ C) (h : F.cones ≅ G.cones) [HasLimit F] : HasLimit G :=
  HasLimit.mk ⟨_, IsLimit.ofRepresentableBy ((limit.isLimit F).representableBy.ofIso h)⟩

/-- The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
@[to_dual
/-- The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/]
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[to_dual (attr := reassoc (attr := simp)) ι_isoOfNatIso_inv]
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[to_dual (attr := reassoc (attr := simp)) ι_isoOfNatIso_hom]
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[to_dual (attr := reassoc (attr := simp)) isoOfNatIso_inv_desc]
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cone.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[to_dual (attr := reassoc (attr := simp)) isoOfNatIso_hom_desc]
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cone.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

/-- The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
@[to_dual
/-- The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/]
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc (attr := simp)) ι_isoOfEquivalence_inv]
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  simp

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc (attr := simp)) ι_isoOfEquivalence_hom]
theorem HasLimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    (HasLimit.isoOfEquivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j := by
  simp only [HasLimit.isoOfEquivalence]
  simp

section Pre

variable (F)
variable [HasLimit F] (E : K ⥤ J) [HasLimit (E ⋙ F)]

/-- The canonical morphism from the limit of `F` to the limit of `E ⋙ F`. -/
@[to_dual /-- The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`. -/]
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[to_dual (attr := reassoc (attr := simp)) ι_pre]
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  simp [limit.pre]

@[to_dual (attr := reassoc (attr := simp)) ι_inv_pre]
theorem limit.inv_pre_π [IsIso (pre F E)] (k : K) :
    inv (limit.pre F E) ≫ limit.π F (E.obj k) = limit.π (E ⋙ F) k := by
  simp

@[to_dual (attr := simp) pre_desc]
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[to_dual (attr := simp)]
theorem limit.pre_pre [h : HasLimit (D ⋙ E ⋙ F)] : haveI : HasLimit ((D ⋙ E) ⋙ F) := h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  have : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl

variable {E F}

/-- If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`. -/
@[to_dual
/-- If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`. -/]
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E = (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫
      (limit.isoLimitCone s).inv := by cat_disch

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F : J ⥤ C) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`. -/
@[to_dual
/-- The canonical morphism from the colimit of `F ⋙ G` to `G` applied to the colimit of `F`. -/]
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[to_dual (attr := reassoc (attr := simp)) ι_post]
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  simp [limit.post]

@[to_dual (attr := simp) post_desc]
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.mapCone c) := by
  ext
  rw [assoc, limit.post_π, ← G.map_comp, limit.lift_π, limit.lift_π]
  rfl

@[to_dual (attr := simp)]
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)] :
    -- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals
    -- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H))
    haveI : HasLimit (F ⋙ G ⋙ H) := h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  have : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl

end Post

@[to_dual]
theorem limit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasLimit F] [HasLimit (E ⋙ F)] [HasLimit (F ⋙ G)]
    [h : HasLimit ((E ⋙ F) ⋙ G)] :
    -- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs
    -- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or
    haveI : HasLimit (E ⋙ F ⋙ G) := h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  have : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]

@[to_dual]
instance hasLimit_equivalence_comp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

-- not entirely sure why this is needed
/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`. -/
@[to_dual
/-- If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`. -/]
theorem hasLimit_of_equivalence_comp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  have : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimit_equivalence_comp e.symm
  apply hasLimit_of_iso (e.invFunIdAssoc F)

@[to_dual]
lemma hasLimit_equivalence_comp_iff (e : K ≌ J) : HasLimit (e.functor ⋙ F) ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_equivalence_comp e, fun _ ↦ inferInstance⟩

@[to_dual]
lemma hasLimit_inverse_equivalence_comp_iff (e : J ≌ K) : HasLimit (e.inverse ⋙ F) ↔ HasLimit F :=
  hasLimit_equivalence_comp_iff e.symm

-- `hasLimitCompEquivalence` and `hasLimitOfCompEquivalence`
-- are proved in `Mathlib/CategoryTheory/Adjunction/Limits.lean`.
section LimFunctor

variable [HasLimitsOfShape J C]

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[to_dual (attr := implicit_reducible, simps)
/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/]
def lim : (J ⥤ C) ⥤ C where
  obj F := limit F
  map α := limMap α

/-- The natural transformation induced by `limit.π`. -/
@[to_dual (attr := simps) ι /-- The natural transformation induced by `colimit.ι`. -/]
def lim.π (j : J) : lim ⟶ (evaluation J C).obj j where
  app F := limit.π F j

variable {G : J ⥤ C} (α : F ⟶ G)

@[to_dual]
theorem limMap_eq : limMap α = lim.map α := rfl

@[to_dual (attr := reassoc) ι_map]
theorem limit.map_π (j : J) : lim.map α ≫ limit.π G j = limit.π F j ≫ α.app j := by simp

@[to_dual pre_map]
theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp

@[to_dual pre_map']
theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp

@[to_dual]
theorem limit.pre_id (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv := by
  cat_disch

@[deprecated (since := "2026-08-17")] alias limit.id_pre := limit.pre_id

@[to_dual]
theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    /- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
     H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def limYoneda :
    lim ⋙ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} ≅ CategoryTheory.cones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => limit.homIso F (unop W)

/-- The constant functor and limit functor are adjoint to each other -/
def constLimAdj : (const J : C ⥤ J ⥤ C) ⊣ lim := Adjunction.mk' {
  homEquiv := fun c g ↦
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun _ => f ≫ limit.π _ _ }
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } } }

instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨constLimAdj⟩⟩

end LimFunctor

instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α

@[to_dual colimMap_epi]
instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [∀ j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
    limit.hom_ext fun j => (cancel_mono (α.app j)).1 <| by simpa using h =≫ limit.π _ j⟩

section Adjunction

variable {L : (J ⥤ C) ⥤ C} (adj : Functor.const _ ⊣ L)

/- The fact that the existence of limits of shape `J` is equivalent to the existence
of a right adjoint to the constant functor `C ⥤ (J ⥤ C)` is obtained in
the file `Mathlib/CategoryTheory/Limits/ConeCategory.lean`: see the lemma
`hasLimitsOfShape_iff_isLeftAdjoint_const`. In the definitions below, given an
adjunction `adj : Functor.const _ ⊣ (L : (J ⥤ C) ⥤ C)`, we directly construct
a limit cone for any `F : J ⥤ C`. -/

/-- The limit cone obtained from a right adjoint of the constant functor. -/
@[simps]
noncomputable def coneOfAdj (F : J ⥤ C) : Cone F where
  pt := L.obj F
  π := adj.counit.app F

set_option backward.defeqAttrib.useBackward true in
/-- The cones defined by `coneOfAdj` are limit cones. -/
@[simps]
def isLimitConeOfAdj (F : J ⥤ C) :
    IsLimit (coneOfAdj adj F) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (adj.left_triangle_components s.pt) j
    dsimp at eq eq' ⊢
    rw [adj.homEquiv_unit, assoc, eq, reassoc_of% eq']
  uniq s m hm := (adj.homEquiv _ _).symm.injective (by ext j; simpa using! hm j)

end Adjunction

/-- We can transport limits of shape `J` along an equivalence `J ≌ J'`. -/
@[to_dual
/-- We can transport colimits of shape `J` along an equivalence `J ≌ J'`. -/]
theorem hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimit_of_equivalence_comp e

variable (C)

@[to_dual]
lemma HasLimitsOfShape.of_small
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [Small.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfSize.has_limits_of_shape (C := C) (ShrinkHoms (Shrink.{u₁} J))
  exact hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence _).symm.trans (Shrink.equivalence _).symm)

@[to_dual]
lemma HasLimitsOfShape.of_essentiallySmall
    [HasLimitsOfSize.{v₁, u₁} C] (J : Type u₂) [Category.{v₂} J]
    [EssentiallySmall.{u₁} J] [LocallySmall.{v₁} J] :
    HasLimitsOfShape J C := by
  have := HasLimitsOfShape.of_small.{v₁, u₁} C (SmallModel.{u₁} J)
  exact hasLimitsOfShape_of_equivalence (equivSmallModel.{u₁} J).symm

/-- A category that has larger limits also has smaller limits. -/
@[to_dual /-- A category that has larger colimits also has smaller colimits. -/]
theorem hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape J {_} := hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence.{v₁} J).trans <| Shrink.equivalence _).symm

/-- `hasLimitsOfSizeShrink.{v u} C` tries to obtain `HasLimitsOfSize.{v u} C`
from some other `HasLimitsOfSize C`.
-/
@[to_dual
/-- `hasColimitsOfSizeShrink.{v u} C` tries to obtain `HasColimitsOfSize.{v u} C`
from some other `HasColimitsOfSize C`.
-/]
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C := hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

@[to_dual]
instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C

end Limit

section Colimit

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W

@[simp]
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} :
    (colimit.homIso F W).hom =
      ↾fun f ↦ (colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W

-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
/-- If `F` has a colimit, so does any naturally isomorphic functor. -/
@[to_dual none]
theorem hasColimit_of_iso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocone.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofCorepresentableBy ((colimit.isColimit F).corepresentableBy.ofIso h)⟩

@[deprecated (since := "2026-08-17")]
alias HasColimit.isoOfNatIso_ι_hom := HasColimit.ι_isoOfNatIso_hom
@[deprecated (since := "2026-08-17")]
alias HasColimit.isoOfNatIso_ι_hom_assoc := HasColimit.ι_isoOfNatIso_hom_assoc
@[deprecated (since := "2026-08-17")]
alias HasColimit.isoOfNatIso_ι_inv := HasColimit.ι_isoOfNatIso_inv
@[deprecated (since := "2026-08-17")]
alias HasColimit.isoOfNatIso_ι_inv_assoc := HasColimit.ι_isoOfNatIso_inv_assoc

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_hom_π := HasColimit.ι_isoOfEquivalence_hom

@[deprecated (since := "2026-05-25")]
alias HasColimit.isoOfEquivalence_inv_π := HasColimit.ι_isoOfEquivalence_inv

section ColimFunctor

variable [HasColimitsOfShape J C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colimCoyoneda : colim.op ⋙ coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁}
    ≅ CategoryTheory.cocones J C :=
  NatIso.ofComponents fun F => NatIso.ofComponents fun W => colimit.homIso (unop F) W

/-- The colimit functor and constant functor are adjoint to each other
-/
def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ const J := Adjunction.mk' {
  homEquiv := fun f c ↦
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun _ => colimit.desc _ ⟨_, 𝟙 _⟩ } }

instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨colimConstAdj⟩⟩

end ColimFunctor

instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α

end Colimit

section Opposite

set_option backward.defeqAttrib.useBackward true in
/-- If `t : Cone F` is a limit cone, then `t.op : Cocone F.op` is a colimit cocone. -/
@[to_dual
/-- If `t : Cocone F` is a colimit cocone, then `t.op : Cone F.op` is a limit cone. -/]
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

set_option backward.defeqAttrib.useBackward true in
/-- If `t : Cone F.op` is a limit cone, then `t.unop : Cocone F` is a colimit cocone. -/
@[to_dual
/-- If `t : Cocone F.op` is a colimit cocone, then `t.unop : Cone F` is a limit cone. -/]
def IsLimit.unop {t : Cone F.op} (P : IsLimit t) : IsColimit t.unop where
  desc s := (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (.op j))
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

/-- If `t.op : Cocone F.op` is a colimit cocone, then `t : Cone F` is a limit cone. -/
@[to_dual /-- If `t.op : Cone F.op` is a limit cone, then `t : Cocone F` is a colimit cocone. -/]
def isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t :=
  P.unop

/-- If `t.unop : Cocone F` is a colimit cocone, then `t : Cone F.op` is a limit cone. -/
@[to_dual /-- If `t.unop : Cone F` is a limit cone, then `t : Cocone F.op` is a colimit cocone. -/]
def isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t :=
  P.op

/-- `t : Cone F` is a limit cone if and only if `t.op : Cocone F.op` is a colimit cocone. -/
@[to_dual
/-- `t : Cocone F` is a colimit cocone if and only if `t.op : Cone F.op` is a limit cone. -/]
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

end Opposite

end Limits

end CategoryTheory
