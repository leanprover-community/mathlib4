/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weak limits

If `F : J ⥤ C` is a functor and `c : Cone F`, we say that `c` is a weak limit of `F` if
every cone over `F` admits a (not necessarily unique) morphism to `c`. In other words, a
weak limit satisfies the same "versal property" as a limit, without the uniqueness
condition. In particular, weak limits are not unique, and they are not functorial.

We set up some API for weak limits, mostly copied from that for limits, prove that any
limit cone is a weak limit cone, and that, if a limit exists, then it is a retract of any
weak limit (see `Retract.ofIsLimit`).

We then specialize to weak equalizers, weak kernels and weak pullbacks, and give some API
for those shapes, again inspired from the non-weak case. We prove that a category with weak
equalizers and pullbacks has weak pullbacks, and that a preadditive category has weak equalizers
if and only if it has weak kernels.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {J : Type*} [Category* J] {K : Type*} [Category* K] {C : Type*}
    [Category* C] {F : Functor J C} {D : Type*} [Category* D] {G : Functor K D}

namespace CategoryTheory.Limits

/-- A cone `t` over `F` is a weak limit cone if each cone over `F` admits a
cone morphism to `t`. -/
structure IsWeakLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch

attribute [reassoc (attr := simp)] IsWeakLimit.fac

/--
If `F` has a limit, then it is a retract of any weak limit of `F`.
-/
def _root_.Retract.ofIsLimit {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t') :
    Retract t.pt t'.pt where
      i := l'.lift t
      r := l.lift t'
      retract := l.hom_ext (fun _ ↦ by rw [assoc, id_comp, l.fac t', l'.fac t])

/--
If `c : Cone F` is a limit, then it is a weak limit.
-/
def IsWeakLimit.OfIsLimit {t : Cone F} (l : IsLimit t) : IsWeakLimit t where
  lift := l.lift
  fac := l.fac

/-- `WeakLimitCone F` contains a cone over `F` together with the information that it is
a weak limit. -/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isWeakLimit : IsWeakLimit cone

/--
Any limit cone defines a weak limit cone with the same underlying cone over `F` and the same
lifts.
-/
def WeakLimitCone.OfLimitCone {F : J ⥤ C} (c : LimitCone F) : WeakLimitCone F where
  cone := c.cone
  isWeakLimit := IsWeakLimit.OfIsLimit c.isLimit

/-- `HasWeakLimit F` represents the mere existence of a weak limit for `F`. -/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimit : Nonempty (WeakLimitCone F)

/--
If `F` has a limit, then it has a weak limit.
-/
lemma HasWeakLimit_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasWeakLimit F where
  exists_weakLimit := Nonempty.intro (WeakLimitCone.OfLimitCone (getLimitCone F))

theorem HasWeakLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
  Classical.choice <| HasWeakLimit.exists_weakLimit

variable (J C) in
/-- `C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`. -/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  has_weakLimit : ∀ F : J ⥤ C, HasWeakLimit F := by infer_instance

instance (priority := 100) hasWeakLimitOfHasWeakLimitsOfShape
    [HasWeakLimitsOfShape J C] (F : J ⥤ C) : HasWeakLimit F :=
  HasWeakLimitsOfShape.has_weakLimit F

instance (priority := 100) hasWeakLimitsOfShapeOfHasLimitsOfShape {J : Type*} [Category* J]
    [HasLimitsOfShape J C] : HasWeakLimitsOfShape J C where
      has_weakLimit F := HasWeakLimit_of_hasLimit F

-- Interface to the `HasWeakLimit` class.
/-- An arbitrary choice of weak limit cone for a functor. -/
def weakLimit.cone (F : J ⥤ C) [HasWeakLimit F] : Cone F :=
  (getWeakLimitCone F).cone

/-- An arbitrary choice of weak limit object of a functor. -/
def weakLimit (F : J ⥤ C) [HasWeakLimit F] :=
  (weakLimit.cone F).pt

/-- The projection from the weak limit object to a value of the functor. -/
def weakLimit.π (F : J ⥤ C) [HasWeakLimit F] (j : J) : weakLimit F ⟶ F.obj j :=
  (weakLimit.cone F).π.app j

@[reassoc]
theorem weakLimit.π_comp_eqToHom (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j') :
    weakLimit.π F j ≫ eqToHom (by subst hj; rfl) = weakLimit.π F j' := by
  subst hj
  simp

@[simp]
theorem weakLimit.cone_x {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).pt = weakLimit F := rfl

@[simp]
theorem weakLimit.cone_π {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).π.app = weakLimit.π _ := rfl

@[reassoc (attr := simp)]
theorem weakLimit.w (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j') :
    weakLimit.π F j ≫ F.map f = weakLimit.π F j' :=
  (weakLimit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `weakLimit.cone F`
is a weak limit cone. -/
def weakLimit.isWeakLimit (F : J ⥤ C) [HasWeakLimit F] :
    IsWeakLimit (weakLimit.cone F) :=
  (getWeakLimitCone F).isWeakLimit

/-- A morphism from the cone point of any other cone to the weak limit object. -/
def weakLimit.lift (F : J ⥤ C) [HasWeakLimit F] (c : Cone F) :
    c.pt ⟶ weakLimit F :=
  (weakLimit.isWeakLimit F).lift c

@[simp]
theorem weakLimit.isWeakLimit_lift {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) :
    (weakLimit.isWeakLimit F).lift c = weakLimit.lift F c :=
  rfl

@[reassoc (attr := simp)]
theorem weakLimit.lift_π {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J) :
    weakLimit.lift F c ≫ weakLimit.π F j = c.π.app j :=
  IsWeakLimit.fac _ c j

namespace IsWeakLimit

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom
  fac s j := by simp

theorem ofIsoWeakLimit_lift {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) (s) :
    (P.ofIsoWeakLimit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

/-- The versal morphism from any other cone to a weak limit cone. -/
def liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

/-- Given a right adjoint functor between categories of cones,
the image of a weak limit cone is a weak limit cone.
-/
def ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c) where
      lift s := (adj.homEquiv s c (t.liftConeMorphism _)).hom
      fac s j := by simp

end IsWeakLimit

/-- If a functor `F` has a weak limit, so does any naturally isomorphic functor.
-/
theorem hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G :=
  HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit := {
        lift s := (weakLimit.isWeakLimit F).lift ((Cone.postcompose α.inv).obj s)
        fac s j := by
          simp only [Cone.postcompose_obj_π, weakLimit.cone_x, NatTrans.comp_app, weakLimit.cone_π]
          refine (weakLimit.lift_π_assoc ((Cone.postcompose α.inv).obj s) j (α.hom.app j)).trans ?_
          simp only [Cone.postcompose_obj_π, NatTrans.comp_app]
          change (_ ≫ _) ≫ _ = _
          rw [assoc, Iso.inv_hom_id_app, comp_id]}
      }

theorem hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWeakLimit G :=
  ⟨fun _ ↦ hasWeakLimit_of_iso α, fun _ ↦ hasWeakLimit_of_iso α.symm⟩

end CategoryTheory.Limits
