/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Logic.Equiv.Basic

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

-- morphism levels before object levels. See note [CategoryTheory universes].
universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u} [Category.{v} C]
variable {F : J ⥤ C}

section Limit

/-- `LimitCone F` contains a cone over `F` together with the information that it is a limit. -/
-- @[nolint has_nonempty_instance] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): removed; linter not ported yet
structure LimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isLimit : IsLimit cone

/-- `HasLimit F` represents the mere existence of a limit for `F`. -/
class HasLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some limit cone for `F` -/
  exists_limit : Nonempty (LimitCone F)

theorem HasLimit.mk {F : J ⥤ C} (d : LimitCone F) : HasLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `LimitCone F` from `HasLimit F`. -/
def getLimitCone (F : J ⥤ C) [HasLimit F] : LimitCone F :=
  Classical.choice <| HasLimit.exists_limit

variable (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class HasLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have limits -/
  has_limit : ∀ F : J ⥤ C, HasLimit F := by infer_instance

/-- `C` has all limits of size `v₁ u₁` (`HasLimitsOfSize.{v₁ u₁} C`)
if it has limits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasLimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All functors `F : J ⥤ C` from all small `J` have limits -/
  has_limits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasLimitsOfShape J C := by
    infer_instance

/-- `C` has all (small) limits if it has limits of every shape that is as big as its hom-sets. -/
abbrev HasLimits (C : Type u) [Category.{v} C] : Prop :=
  HasLimitsOfSize.{v, v} C

theorem HasLimits.has_limits_of_shape {C : Type u} [Category.{v} C] [HasLimits C] (J : Type v)
    [Category.{v} J] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

variable {J C}

-- see Note [lower instance priority]
instance (priority := 100) hasLimitOfHasLimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfShape J C] (F : J ⥤ C) : HasLimit F :=
  HasLimitsOfShape.has_limit F

-- see Note [lower instance priority]
instance (priority := 100) hasLimitsOfShapeOfHasLimits {J : Type u₁} [Category.{v₁} J]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfShape J C :=
  HasLimitsOfSize.has_limits_of_shape J

-- Interface to the `HasLimit` class.
/-- An arbitrary choice of limit cone for a functor. -/
def limit.cone (F : J ⥤ C) [HasLimit F] : Cone F :=
  (getLimitCone F).cone

/-- An arbitrary choice of limit object of a functor. -/
def limit (F : J ⥤ C) [HasLimit F] :=
  (limit.cone F).pt

/-- The projection from the limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j

@[reassoc]
theorem limit.π_comp_eqToHom (F : J ⥤ C) [HasLimit F] {j j' : J} (hj : j = j') :
    limit.π F j ≫ eqToHom (by subst hj; rfl) = limit.π F j' := by
  subst hj
  simp

@[simp]
theorem limit.cone_x {F : J ⥤ C} [HasLimit F] : (limit.cone F).pt = limit F :=
  rfl

@[simp]
theorem limit.cone_π {F : J ⥤ C} [HasLimit F] : (limit.cone F).π.app = limit.π _ :=
  rfl

@[reassoc (attr := simp)]
theorem limit.w (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `limit.cone F` is a limit cone. -/
def limit.isLimit (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  (getLimitCone F).isLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  (limit.isLimit F).lift c

@[simp]
theorem limit.isLimit_lift {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.isLimit F).lift c = limit.lift F c :=
  rfl

@[reassoc (attr := simp)]
theorem limit.lift_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  IsLimit.fac _ c j

/-- Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def limMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  IsLimit.map _ (limit.isLimit G) α

@[reassoc (attr := simp)]
theorem limMap_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.coneMorphism {F : J ⥤ C} [HasLimit F] (c : Cone F) : c ⟶ limit.cone F :=
  (limit.isLimit F).liftConeMorphism c

@[simp]
theorem limit.coneMorphism_hom {F : J ⥤ C} [HasLimit F] (c : Cone F) :
    (limit.coneMorphism c).hom = limit.lift F c :=
  rfl

theorem limit.coneMorphism_π {F : J ⥤ C} [HasLimit F] (c : Cone F) (j : J) :
    (limit.coneMorphism c).hom ≫ limit.π F j = c.π.app j := by simp

@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_hom_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso hc (limit.isLimit _)).hom ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
theorem limit.conePointUniqueUpToIso_inv_comp {F : J ⥤ C} [HasLimit F] {c : Cone F} (hc : IsLimit c)
    (j : J) : (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc).inv ≫ limit.π F j = c.π.app j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

theorem limit.existsUnique {F : J ⥤ C} [HasLimit F] (t : Cone F) :
    ∃! l : t.pt ⟶ limit F, ∀ j, l ≫ limit.π F j = t.π.app j :=
  (limit.isLimit F).existsUnique _

/-- Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.isoLimitCone {F : J ⥤ C} [HasLimit F] (t : LimitCone F) : limit F ≅ t.cone.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F) t.isLimit

@[reassoc (attr := simp)]
theorem limit.isoLimitCone_hom_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).hom ≫ t.cone.π.app j = limit.π F j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat

@[reassoc (attr := simp)]
theorem limit.isoLimitCone_inv_π {F : J ⥤ C} [HasLimit F] (t : LimitCone F) (j : J) :
    (limit.isoLimitCone t).inv ≫ limit.π F j = t.cone.π.app j := by
  dsimp [limit.isoLimitCone, IsLimit.conePointUniqueUpToIso]
  aesop_cat

@[ext]
theorem limit.hom_ext {F : J ⥤ C} [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.isLimit F).hom_ext w

@[simp]
theorem limit.lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cones.postcompose α).obj c) := by
  ext
  rw [assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
  rfl

@[simp]
theorem limit.lift_cone {F : J ⥤ C} [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.isLimit _).lift_self

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.homIso (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅ F.cones.obj (op W) :=
  (limit.isLimit F).homIso W

@[simp]
theorem limit.homIso_hom (F : J ⥤ C) [HasLimit F] {W : C} (f : ULift (W ⟶ limit F)) :
    (limit.homIso F W).hom f = (const J).map f.down ≫ (limit.cone F).π :=
  (limit.isLimit F).homIso_hom f

/-- The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.homIso' (F : J ⥤ C) [HasLimit F] (W : C) :
    ULift.{u₁} (W ⟶ limit F : Type v) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  (limit.isLimit F).homIso' W

theorem limit.lift_extend {F : J ⥤ C} [HasLimit F] (c : Cone F) {X : C} (f : X ⟶ c.pt) :
    limit.lift F (c.extend f) = f ≫ limit.lift F c := by aesop_cat

/-- If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
theorem hasLimitOfIso {F G : J ⥤ C} [HasLimit F] (α : F ≅ G) : HasLimit G :=
  HasLimit.mk
    { cone := (Cones.postcompose α.hom).obj (limit.cone F)
      isLimit := (IsLimit.postcomposeHomEquiv _ _).symm (limit.isLimit F) }

-- See the construction of limits from products and equalizers
-- for an example usage.
/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
theorem HasLimit.ofConesIso {J K : Type u₁} [Category.{v₁} J] [Category.{v₂} K] (F : J ⥤ C)
    (G : K ⥤ C) (h : F.cones ≅ G.cones) [HasLimit F] : HasLimit G :=
  HasLimit.mk ⟨_, IsLimit.ofNatIso (IsLimit.natIso (limit.isLimit F) ≪≫ h)⟩

/-- The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def HasLimit.isoOfNatIso {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfNatIso (limit.isLimit F) (limit.isLimit G) w

@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_hom_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ _

@[reassoc (attr := simp)]
theorem HasLimit.isoOfNatIso_inv_π {F G : J ⥤ C} [HasLimit F] [HasLimit G] (w : F ≅ G) (j : J) :
    (HasLimit.isoOfNatIso w).inv ≫ limit.π F j = limit.π G j ≫ w.inv.app j :=
  IsLimit.conePointsIsoOfNatIso_inv_comp _ _ _ _

@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_hom {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone F)
    (w : F ≅ G) :
    limit.lift F t ≫ (HasLimit.isoOfNatIso w).hom =
      limit.lift G ((Cones.postcompose w.hom).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_hom _ _ _

@[reassoc (attr := simp)]
theorem HasLimit.lift_isoOfNatIso_inv {F G : J ⥤ C} [HasLimit F] [HasLimit G] (t : Cone G)
    (w : F ≅ G) :
    limit.lift G t ≫ (HasLimit.isoOfNatIso w).inv =
      limit.lift F ((Cones.postcompose w.inv).obj _) :=
  IsLimit.lift_comp_conePointsIsoOfNatIso_inv _ _ _

/-- The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def HasLimit.isoOfEquivalence {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  IsLimit.conePointsIsoOfEquivalence (limit.isLimit F) (limit.isLimit G) e w

@[simp]
theorem HasLimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    (HasLimit.isoOfEquivalence e w).hom ≫ limit.π G k =
      limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp

@[simp]
theorem HasLimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasLimit F] {G : K ⥤ C} [HasLimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    (HasLimit.isoOfEquivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j := by
  simp only [HasLimit.isoOfEquivalence, IsLimit.conePointsIsoOfEquivalence_hom]
  dsimp
  simp

section Pre

variable (F)
variable [HasLimit F] (E : K ⥤ J) [HasLimit (E ⋙ F)]

/-- The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[reassoc (attr := simp)]
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) := by
  erw [IsLimit.fac]
  rfl

@[simp]
theorem limit.lift_pre (c : Cone F) :
    limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) := by ext; simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
theorem limit.pre_pre [h : HasLimit (D ⋙ E ⋙ F)] : haveI : HasLimit ((D ⋙ E) ⋙ F) := h
    limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := by
  haveI : HasLimit ((D ⋙ E) ⋙ F) := h
  ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; rfl

variable {E F}

/-- -
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
theorem limit.pre_eq (s : LimitCone (E ⋙ F)) (t : LimitCone F) :
    limit.pre F E = (limit.isoLimitCone t).hom ≫ s.isLimit.lift (t.cone.whisker E) ≫
      (limit.isoLimitCone s).inv := by aesop_cat

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F : J ⥤ C) [HasLimit F] (G : C ⥤ D) [HasLimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.mapCone (limit.cone F))

@[reassoc (attr := simp)]
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  erw [IsLimit.fac]
  rfl

@[simp]
theorem limit.lift_post (c : Cone F) :
    G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.mapCone c) := by
  ext
  rw [assoc, limit.post_π, ← G.map_comp, limit.lift_π, limit.lift_π]
  rfl

@[simp]
theorem limit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E) [h : HasLimit ((F ⋙ G) ⋙ H)] :
    -- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals
    -- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H))
    haveI : HasLimit (F ⋙ G ⋙ H) := h
    H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := by
  haveI : HasLimit (F ⋙ G ⋙ H) := h
  ext; erw [assoc, limit.post_π, ← H.map_comp, limit.post_π, limit.post_π]; rfl

end Post

theorem limit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasLimit F] [HasLimit (E ⋙ F)] [HasLimit (F ⋙ G)]
    [h : HasLimit ((E ⋙ F) ⋙ G)] :-- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs
            -- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or
    haveI : HasLimit (E ⋙ F ⋙ G) := h
    G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := by
  haveI : HasLimit (E ⋙ F ⋙ G) := h
  ext; erw [assoc, limit.post_π, ← G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]

open CategoryTheory.Equivalence

instance hasLimitEquivalenceComp (e : K ≌ J) [HasLimit F] : HasLimit (e.functor ⋙ F) :=
  HasLimit.mk
    { cone := Cone.whisker e.functor (limit.cone F)
      isLimit := IsLimit.whiskerEquivalence (limit.isLimit F) e }

-- Porting note: testing whether this still needed
-- attribute [local elab_without_expected_type] inv_fun_id_assoc

-- not entirely sure why this is needed
/-- If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
theorem hasLimitOfEquivalenceComp (e : K ≌ J) [HasLimit (e.functor ⋙ F)] : HasLimit F := by
  haveI : HasLimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasLimitEquivalenceComp e.symm
  apply hasLimitOfIso (e.invFunIdAssoc F)

-- `hasLimitCompEquivalence` and `hasLimitOfCompEquivalence`
-- are proved in `CategoryTheory/Adjunction/Limits.lean`.
section LimFunctor

variable [HasLimitsOfShape J C]

section

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps]
def lim : (J ⥤ C) ⥤ C where
  obj F := limit F
  map α := limMap α
  map_id F := by
    apply Limits.limit.hom_ext; intro j
    erw [limMap_π, Category.id_comp, Category.comp_id]
  map_comp α β := by
    apply Limits.limit.hom_ext; intro j
    erw [assoc, IsLimit.fac, IsLimit.fac, ← assoc, IsLimit.fac, assoc]; rfl

end

variable {G : J ⥤ C} (α : F ⟶ G)

theorem limit.map_pre [HasLimitsOfShape K C] (E : K ⥤ J) :
    lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whiskerLeft E α) := by
  ext
  simp

theorem limit.map_pre' [HasLimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whiskerRight α F) := by
  ext1; simp [← category.assoc]

-- theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (Functor.leftUnitor F).inv:=by
--   aesop_cat

theorem limit.map_post {D : Type u'} [Category.{v'} D] [HasLimitsOfShape J D] (H : C ⥤ D) :
    /- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
     H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
    H.map (limMap α) ≫ limit.post G H = limit.post F H ≫ limMap (whiskerRight α H) := by
  ext
  simp only [whiskerRight_app, limMap_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp]

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
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun _ => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } } }

instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨constLimAdj⟩⟩

end LimFunctor

instance limMap_mono' {F G : J ⥤ C} [HasLimitsOfShape J C] (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α

instance limMap_mono {F G : J ⥤ C} [HasLimit F] [HasLimit G] (α : F ⟶ G) [∀ j, Mono (α.app j)] :
    Mono (limMap α) :=
  ⟨fun {Z} u v h =>
    limit.hom_ext fun j => (cancel_mono (α.app j)).1 <| by simpa using h =≫ limit.π _ j⟩

section Adjunction

variable {L : (J ⥤ C) ⥤ C} (adj : Functor.const _ ⊣ L)

/- The fact that the existence of limits of shape `J` is equivalent to the existence
of a right adjoint to the constant functor `C ⥤ (J ⥤ C)` is obtained in
the file `Mathlib.CategoryTheory.Limits.ConeCategory`: see the lemma
`hasLimitsOfShape_iff_isLeftAdjoint_const`. In the definitions below, given an
adjunction `adj : Functor.const _ ⊣ (L : (J ⥤ C) ⥤ C)`, we directly construct
a limit cone for any `F : J ⥤ C`. -/

/-- The limit cone obtained from a right adjoint of the constant functor. -/
@[simps]
noncomputable def coneOfAdj (F : J ⥤ C) : Cone F where
  pt := L.obj F
  π := adj.counit.app F

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
  uniq s m hm := (adj.homEquiv _ _).symm.injective (by ext j; simpa using hm j)

end Adjunction

/-- We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasLimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasLimitsOfShape J C] : HasLimitsOfShape J' C := by
  constructor
  intro F
  apply hasLimitOfEquivalenceComp e

variable (C)

/-- A category that has larger limits also has smaller limits. -/
theorem hasLimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfSize.{v₂, u₂} C where
  has_limits_of_shape J {_} := hasLimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm

/-- `hasLimitsOfSizeShrink.{v u} C` tries to obtain `HasLimitsOfSize.{v u} C`
from some other `HasLimitsOfSize C`.
-/
theorem hasLimitsOfSizeShrink [HasLimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasLimitsOfSize.{v₁, u₁} C := hasLimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

instance (priority := 100) hasSmallestLimitsOfHasLimits [HasLimits C] : HasLimitsOfSize.{0, 0} C :=
  hasLimitsOfSizeShrink.{0, 0} C

end Limit

section Colimit

/-- `ColimitCocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
-- @[nolint has_nonempty_instance] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/5171): removed; linter not ported yet
structure ColimitCocone (F : J ⥤ C) where
  /-- The cocone itself -/
  cocone : Cocone F
  /-- The proof that it is the colimit cocone -/
  isColimit : IsColimit cocone

/-- `HasColimit F` represents the mere existence of a colimit for `F`. -/
class HasColimit (F : J ⥤ C) : Prop where mk' ::
  /-- There exists a colimit for `F` -/
  exists_colimit : Nonempty (ColimitCocone F)

theorem HasColimit.mk {F : J ⥤ C} (d : ColimitCocone F) : HasColimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `ColimitCocone F` from `HasColimit F`. -/
def getColimitCocone (F : J ⥤ C) [HasColimit F] : ColimitCocone F :=
  Classical.choice <| HasColimit.exists_colimit

variable (J C)

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class HasColimitsOfShape : Prop where
  /-- All `F : J ⥤ C` have colimits for a fixed `J` -/
  has_colimit : ∀ F : J ⥤ C, HasColimit F := by infer_instance

/-- `C` has all colimits of size `v₁ u₁` (`HasColimitsOfSize.{v₁ u₁} C`)
if it has colimits of every shape `J : Type u₁` with `[Category.{v₁} J]`.
-/
@[pp_with_univ]
class HasColimitsOfSize (C : Type u) [Category.{v} C] : Prop where
  /-- All `F : J ⥤ C` have colimits for all small `J` -/
  has_colimits_of_shape : ∀ (J : Type u₁) [Category.{v₁} J], HasColimitsOfShape J C := by
    infer_instance

/-- `C` has all (small) colimits if it has colimits of every shape that is as big as its hom-sets.
-/
abbrev HasColimits (C : Type u) [Category.{v} C] : Prop :=
  HasColimitsOfSize.{v, v} C

theorem HasColimits.hasColimitsOfShape {C : Type u} [Category.{v} C] [HasColimits C] (J : Type v)
    [Category.{v} J] : HasColimitsOfShape J C :=
  HasColimitsOfSize.has_colimits_of_shape J

variable {J C}

-- see Note [lower instance priority]
instance (priority := 100) hasColimitOfHasColimitsOfShape {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfShape J C] (F : J ⥤ C) : HasColimit F :=
  HasColimitsOfShape.has_colimit F

-- see Note [lower instance priority]
instance (priority := 100) hasColimitsOfShapeOfHasColimitsOfSize {J : Type u₁} [Category.{v₁} J]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfShape J C :=
  HasColimitsOfSize.has_colimits_of_shape J

-- Interface to the `HasColimit` class.
/-- An arbitrary choice of colimit cocone of a functor. -/
def colimit.cocone (F : J ⥤ C) [HasColimit F] : Cocone F :=
  (getColimitCocone F).cocone

/-- An arbitrary choice of colimit object of a functor. -/
def colimit (F : J ⥤ C) [HasColimit F] :=
  (colimit.cocone F).pt

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι (F : J ⥤ C) [HasColimit F] (j : J) : F.obj j ⟶ colimit F :=
  (colimit.cocone F).ι.app j

@[reassoc]
theorem colimit.eqToHom_comp_ι (F : J ⥤ C) [HasColimit F] {j j' : J} (hj : j = j') :
    eqToHom (by subst hj; rfl) ≫ colimit.ι F j = colimit.ι F j'  := by
  subst hj
  simp

@[simp]
theorem colimit.cocone_ι {F : J ⥤ C} [HasColimit F] (j : J) :
    (colimit.cocone F).ι.app j = colimit.ι _ j :=
  rfl

@[simp]
theorem colimit.cocone_x {F : J ⥤ C} [HasColimit F] : (colimit.cocone F).pt = colimit F :=
  rfl

@[reassoc (attr := simp)]
theorem colimit.w (F : J ⥤ C) [HasColimit F] {j j' : J} (f : j ⟶ j') :
    F.map f ≫ colimit.ι F j' = colimit.ι F j :=
  (colimit.cocone F).w f

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.isColimit (F : J ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F) :=
  (getColimitCocone F).isColimit

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [HasColimit F] (c : Cocone F) : colimit F ⟶ c.pt :=
  (colimit.isColimit F).desc c

@[simp]
theorem colimit.isColimit_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.isColimit F).desc c = colimit.desc F c :=
  rfl

/-- We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `Category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `Tactic/reassoc_axiom.lean`)
 -/
@[reassoc (attr := simp)]
theorem colimit.ι_desc {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  IsColimit.fac _ c j

/-- Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
  IsColimit.map (colimit.isColimit F) _ α

@[reassoc (attr := simp)]
theorem ι_colimMap {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) (j : J) :
    colimit.ι F j ≫ colimMap α = α.app j ≫ colimit.ι G j :=
  colimit.ι_desc _ j

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) : colimit.cocone F ⟶ c :=
  (colimit.isColimit F).descCoconeMorphism c

@[simp]
theorem colimit.coconeMorphism_hom {F : J ⥤ C} [HasColimit F] (c : Cocone F) :
    (colimit.coconeMorphism c).hom = colimit.desc F c :=
  rfl

theorem colimit.ι_coconeMorphism {F : J ⥤ C} [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ (colimit.coconeMorphism c).hom = c.ι.app j := by simp

@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_hom {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc).hom = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ _

@[reassoc (attr := simp)]
theorem colimit.comp_coconePointUniqueUpToIso_inv {F : J ⥤ C} [HasColimit F] {c : Cocone F}
    (hc : IsColimit c) (j : J) :
    colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)).inv = c.ι.app j :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

theorem colimit.existsUnique {F : J ⥤ C} [HasColimit F] (t : Cocone F) :
    ∃! d : colimit F ⟶ t.pt, ∀ j, colimit.ι F j ≫ d = t.ι.app j :=
  (colimit.isColimit F).existsUnique _

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.isoColimitCocone {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) :
    colimit F ≅ t.cocone.pt :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) t.isColimit

@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_hom {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    colimit.ι F j ≫ (colimit.isoColimitCocone t).hom = t.cocone.ι.app j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat

@[reassoc (attr := simp)]
theorem colimit.isoColimitCocone_ι_inv {F : J ⥤ C} [HasColimit F] (t : ColimitCocone F) (j : J) :
    t.cocone.ι.app j ≫ (colimit.isoColimitCocone t).inv = colimit.ι F j := by
  dsimp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]
  aesop_cat

@[ext]
theorem colimit.hom_ext {F : J ⥤ C} [HasColimit F] {X : C} {f f' : colimit F ⟶ X}
    (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
  (colimit.isColimit F).hom_ext w

@[simp]
theorem colimit.desc_cocone {F : J ⥤ C} [HasColimit F] :
    colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
  (colimit.isColimit _).desc_self

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.homIso (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅ F.cocones.obj W :=
  (colimit.isColimit F).homIso W

@[simp]
theorem colimit.homIso_hom (F : J ⥤ C) [HasColimit F] {W : C} (f : ULift (colimit F ⟶ W)) :
    (colimit.homIso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f.down :=
  (colimit.isColimit F).homIso_hom f

/-- The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.homIso' (F : J ⥤ C) [HasColimit F] (W : C) :
    ULift.{u₁} (colimit F ⟶ W : Type v) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  (colimit.isColimit F).homIso' W

theorem colimit.desc_extend (F : J ⥤ C) [HasColimit F] (c : Cocone F) {X : C} (f : c.pt ⟶ X) :
    colimit.desc F (c.extend f) = colimit.desc F c ≫ f := by ext1; rw [← Category.assoc]; simp

-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
/-- If `F` has a colimit, so does any naturally isomorphic functor.
-/
theorem hasColimitOfIso {F G : J ⥤ C} [HasColimit F] (α : G ≅ F) : HasColimit G :=
  HasColimit.mk
    { cocone := (Cocones.precompose α.hom).obj (colimit.cocone F)
      isColimit := (IsColimit.precomposeHomEquiv _ _).symm (colimit.isColimit F) }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
theorem HasColimit.ofCoconesIso {K : Type u₁} [Category.{v₂} K] (F : J ⥤ C) (G : K ⥤ C)
    (h : F.cocones ≅ G.cocones) [HasColimit F] : HasColimit G :=
  HasColimit.mk ⟨_, IsColimit.ofNatIso (IsColimit.natIso (colimit.isColimit F) ≪≫ h)⟩

/-- The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def HasColimit.isoOfNatIso {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G) :
    colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfNatIso (colimit.isColimit F) (colimit.isColimit G) w

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_hom {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι F j ≫ (HasColimit.isoOfNatIso w).hom = w.hom.app j ≫ colimit.ι G j :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_ι_inv {F G : J ⥤ C} [HasColimit F] [HasColimit G] (w : F ≅ G)
    (j : J) : colimit.ι G j ≫ (HasColimit.isoOfNatIso w).inv = w.inv.app j ≫ colimit.ι F j :=
  IsColimit.comp_coconePointsIsoOfNatIso_inv _ _ _ _

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_hom_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone G)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).hom ≫ colimit.desc G t =
      colimit.desc F ((Cocones.precompose w.hom).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_hom_desc _ _ _

@[reassoc (attr := simp)]
theorem HasColimit.isoOfNatIso_inv_desc {F G : J ⥤ C} [HasColimit F] [HasColimit G] (t : Cocone F)
    (w : F ≅ G) :
    (HasColimit.isoOfNatIso w).inv ≫ colimit.desc F t =
      colimit.desc G ((Cocones.precompose w.inv).obj _) :=
  IsColimit.coconePointsIsoOfNatIso_inv_desc _ _ _

/-- The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def HasColimit.isoOfEquivalence {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G] (e : J ≌ K)
    (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  IsColimit.coconePointsIsoOfEquivalence (colimit.isColimit F) (colimit.isColimit G) e w

@[simp]
theorem HasColimit.isoOfEquivalence_hom_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
    colimit.ι F j ≫ (HasColimit.isoOfEquivalence e w).hom =
      F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]

@[simp]
theorem HasColimit.isoOfEquivalence_inv_π {F : J ⥤ C} [HasColimit F] {G : K ⥤ C} [HasColimit G]
    (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
    colimit.ι G k ≫ (HasColimit.isoOfEquivalence e w).inv =
      G.map (e.counitInv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) := by
  simp [HasColimit.isoOfEquivalence, IsColimit.coconePointsIsoOfEquivalence_inv]

section Pre

variable (F)
variable [HasColimit F] (E : K ⥤ J) [HasColimit (E ⋙ F)]

/-- The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[reassoc (attr := simp)]
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) := by
  erw [IsColimit.fac]
  rfl

@[reassoc (attr := simp)]
theorem colimit.ι_inv_pre [IsIso (pre F E)] (k : K) :
    colimit.ι F (E.obj k) ≫ inv (colimit.pre F E) = colimit.ι (E ⋙ F) k := by
  simp [IsIso.comp_inv_eq]

@[reassoc (attr := simp)]
theorem colimit.pre_desc (c : Cocone F) :
    colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) := by
  ext; rw [← assoc, colimit.ι_pre]; simp

variable {L : Type u₃} [Category.{v₃} L]
variable (D : L ⥤ K)

@[simp]
theorem colimit.pre_pre [h : HasColimit (D ⋙ E ⋙ F)] :
    haveI : HasColimit ((D ⋙ E) ⋙ F) := h
    colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := by
  ext j
  rw [← assoc, colimit.ι_pre, colimit.ι_pre]
  haveI : HasColimit ((D ⋙ E) ⋙ F) := h
  exact (colimit.ι_pre F (D ⋙ E) j).symm

variable {E F}

/-- -
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
theorem colimit.pre_eq (s : ColimitCocone (E ⋙ F)) (t : ColimitCocone F) :
    colimit.pre F E =
      (colimit.isoColimitCocone s).hom ≫
        s.isColimit.desc (t.cocone.whisker E) ≫ (colimit.isoColimitCocone t).inv := by
  aesop_cat

end Pre

section Post

variable {D : Type u'} [Category.{v'} D]
variable (F)
variable [HasColimit F] (G : C ⥤ D) [HasColimit (F ⋙ G)]

/-- The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (G.mapCocone (colimit.cocone F))

@[reassoc (attr := simp)]
theorem colimit.ι_post (j : J) :
    colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) := by
  erw [IsColimit.fac]
  rfl

@[simp]
theorem colimit.post_desc (c : Cocone F) :
    colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.mapCocone c) := by
  ext
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_desc, colimit.ι_desc]
  rfl

@[simp]
theorem colimit.post_post {E : Type u''} [Category.{v''} E] (H : D ⥤ E)
    -- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals
    -- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H))
    [h : HasColimit ((F ⋙ G) ⋙ H)] : haveI : HasColimit (F ⋙ G ⋙ H) := h
    colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) := by
  ext j
  rw [← assoc, colimit.ι_post, ← H.map_comp, colimit.ι_post]
  haveI : HasColimit (F ⋙ G ⋙ H) := h
  exact (colimit.ι_post F (G ⋙ H) j).symm

end Post

theorem colimit.pre_post {D : Type u'} [Category.{v'} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
    [HasColimit F] [HasColimit (E ⋙ F)] [HasColimit (F ⋙ G)] [h : HasColimit ((E ⋙ F) ⋙ G)] :
    -- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs
    -- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or
    haveI : HasColimit (E ⋙ F ⋙ G) := h
    colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) =
      colimit.pre (F ⋙ G) E ≫ colimit.post F G := by
  ext j
  rw [← assoc, colimit.ι_post, ← G.map_comp, colimit.ι_pre, ← assoc]
  haveI : HasColimit (E ⋙ F ⋙ G) := h
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]

open CategoryTheory.Equivalence

instance hasColimit_equivalence_comp (e : K ≌ J) [HasColimit F] : HasColimit (e.functor ⋙ F) :=
  HasColimit.mk
    { cocone := Cocone.whisker e.functor (colimit.cocone F)
      isColimit := IsColimit.whiskerEquivalence (colimit.isColimit F) e }

/-- If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
theorem hasColimit_of_equivalence_comp (e : K ≌ J) [HasColimit (e.functor ⋙ F)] : HasColimit F := by
  haveI : HasColimit (e.inverse ⋙ e.functor ⋙ F) := Limits.hasColimit_equivalence_comp e.symm
  apply hasColimitOfIso (e.invFunIdAssoc F).symm

section ColimFunctor

variable [HasColimitsOfShape J C]

section

-- attribute [local simp] colimMap -- Porting note: errors out colim.map_id and map_comp now

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps] -- Porting note: simps on all fields now
def colim : (J ⥤ C) ⥤ C where
  obj F := colimit F
  map α := colimMap α

end

variable {G : J ⥤ C} (α : F ⟶ G)

-- @[reassoc (attr := simp)] Porting note: now simp can prove these
@[reassoc]
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j := by simp

@[simp] -- Porting note: proof adjusted to account for @[simps] on all fields of colim
theorem colimit.map_desc (c : Cocone G) :
    colimMap α ≫ colimit.desc G c = colimit.desc F ((Cocones.precompose α).obj c) := by
  ext j
  simp [← assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]

theorem colimit.pre_map [HasColimitsOfShape K C] (E : K ⥤ J) :
    colimit.pre F E ≫ colim.map α = colim.map (whiskerLeft E α) ≫ colimit.pre G E := by
  ext
  rw [← assoc, colimit.ι_pre, colimit.ι_map, ← assoc, colimit.ι_map, assoc, colimit.ι_pre]
  rfl

theorem colimit.pre_map' [HasColimitsOfShape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
    colimit.pre F E₁ = colim.map (whiskerRight α F) ≫ colimit.pre F E₂ := by
  ext1
  simp [← assoc, assoc]

-- theorem colimit.pre_id (F : J ⥤ C) :
--     colimit.pre F (𝟭 _) = colim.map (Functor.leftUnitor F).hom := by aesop_cat

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
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun _ => colimit.desc _ ⟨_, 𝟙 _⟩ } }

instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, ⟨colimConstAdj⟩⟩

end ColimFunctor

instance colimMap_epi' {F G : J ⥤ C} [HasColimitsOfShape J C] (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α

instance colimMap_epi {F G : J ⥤ C} [HasColimit F] [HasColimit G] (α : F ⟶ G) [∀ j, Epi (α.app j)] :
    Epi (colimMap α) :=
  ⟨fun {Z} u v h =>
    colimit.hom_ext fun j => (cancel_epi (α.app j)).1 <| by simpa using colimit.ι _ j ≫= h⟩

/-- We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem hasColimitsOfShape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J')
    [HasColimitsOfShape J C] : HasColimitsOfShape J' C := by
  constructor
  intro F
  apply hasColimit_of_equivalence_comp e

variable (C)

/-- A category that has larger colimits also has smaller colimits. -/
theorem hasColimitsOfSizeOfUnivLE [UnivLE.{v₂, v₁}] [UnivLE.{u₂, u₁}]
    [HasColimitsOfSize.{v₁, u₁} C] : HasColimitsOfSize.{v₂, u₂} C where
  has_colimits_of_shape J {_} := hasColimitsOfShape_of_equivalence
    ((ShrinkHoms.equivalence J).trans <| Shrink.equivalence _).symm

/-- `hasColimitsOfSizeShrink.{v u} C` tries to obtain `HasColimitsOfSize.{v u} C`
from some other `HasColimitsOfSize C`.
-/
theorem hasColimitsOfSizeShrink [HasColimitsOfSize.{max v₁ v₂, max u₁ u₂} C] :
    HasColimitsOfSize.{v₁, u₁} C := hasColimitsOfSizeOfUnivLE.{max v₁ v₂, max u₁ u₂} C

instance (priority := 100) hasSmallestColimitsOfHasColimits [HasColimits C] :
    HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink.{0, 0} C

end Colimit

section Opposite

/-- If `t : Cone F` is a limit cone, then `t.op : Cocone F.op` is a colimit cocone.
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

/-- If `t : Cocone F` is a colimit cocone, then `t.op : Cone F.op` is a limit cone.
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

/-- If `t : Cone F.op` is a limit cone, then `t.unop : Cocone F` is a colimit cocone.
-/
def IsLimit.unop {t : Cone F.op} (P : IsLimit t) : IsColimit t.unop where
  desc s := (P.lift s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  -- Porting note: thinks `op j` is `IsLimit.op j`
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

/-- If `t : Cocone F.op` is a colimit cocone, then `t.unop : Cone F` is a limit cone.
-/
def IsColimit.unop {t : Cocone F.op} (P : IsColimit t) : IsLimit t.unop where
  lift s := (P.desc s.op).unop
  fac s j := congrArg Quiver.Hom.unop (P.fac s.op (Opposite.op j))
  -- Porting note: thinks `op j` is `IsLimit.op j`
  uniq s m w := by
    dsimp
    rw [← P.uniq s.op m.op]
    · rfl
    · dsimp
      intro j
      rw [← w]
      rfl

/-- If `t.op : Cocone F.op` is a colimit cocone, then `t : Cone F` is a limit cone. -/
def isLimitOfOp {t : Cone F} (P : IsColimit t.op) : IsLimit t :=
  P.unop

/-- If `t.op : Cone F.op` is a limit cone, then `t : Cocone F` is a colimit cocone. -/
def isColimitOfOp {t : Cocone F} (P : IsLimit t.op) : IsColimit t :=
  P.unop

/-- If `t.unop : Cocone F` is a colimit cocone, then `t : Cone F.op` is a limit cone.-/
def isLimitOfUnop {t : Cone F.op} (P : IsColimit t.unop) : IsLimit t :=
  P.op

/-- If `t.unop : Cone F` is a limit cone, then `t : Cocone F.op` is a colimit cocone. -/
def isColimitOfUnop {t : Cocone F.op} (P : IsLimit t.unop) : IsColimit t :=
  P.op

/-- `t : Cone F` is a limit cone if and only if `t.op : Cocone F.op` is a colimit cocone.
-/
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

/-- `t : Cocone F` is a colimit cocone if and only if `t.op : Cone F.op` is a limit cone.
-/
def isColimitEquivIsLimitOp {t : Cocone F} : IsColimit t ≃ IsLimit t.op :=
  equivOfSubsingletonOfSubsingleton IsColimit.op isColimitOfOp

end Opposite

end Limits

end CategoryTheory
