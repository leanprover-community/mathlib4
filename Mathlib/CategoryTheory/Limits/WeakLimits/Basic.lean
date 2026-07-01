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
weak limit (see `IsWeakLimit.retractOfIsLimit`).

In the files `WeakEqualizers.lean`, `WeakKernels.lean` and `WeakPullbacks.lean`, we specialize
to weak equalizers, weak kernels and weak pullbacks, and give some API for those shapes,
again inspired from the non-weak case. We prove that a category with weak equalizers and
pullbacks has weak pullbacks, and that a preadditive category has weak equalizers if and only
if it has weak kernels.

## References

* [Peter J Freyd, *Representations in Abelian categories*, p. 99][freyd1966repabelian]

-/

@[expose] public section

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
def IsWeakLimit.retractOfIsLimit {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t') :
    Retract t.pt t'.pt where
  i := l'.lift t
  r := l.lift t'
  retract := l.hom_ext (fun _ ↦ by rw [assoc, id_comp, l.fac t', l'.fac t])

/--
If `c : Cone F` is a limit, then it is a weak limit.
-/
def IsLimit.isWeakLimit {t : Cone F} (l : IsLimit t) : IsWeakLimit t where
  lift := l.lift
  fac := l.fac

/-- `WeakLimitCone F` contains a cone over `F` together with the information that it is
a weak limit. -/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the weak limit cone -/
  isWeakLimit : IsWeakLimit cone

/--
Any limit cone defines a weak limit cone with the same underlying cone over `F` and the same
lifts.
-/
def WeakLimitCone.ofLimitCone {F : J ⥤ C} (c : LimitCone F) : WeakLimitCone F where
  cone := c.cone
  isWeakLimit := c.isLimit.isWeakLimit

/-- `HasWeakLimit F` represents the mere existence of a weak limit for `F`. -/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimitCone : Nonempty (WeakLimitCone F)

/--
If `F` has a limit, then it has a weak limit.
-/
instance (F : J ⥤ C) [HasLimit F] : HasWeakLimit F where
  exists_weakLimitCone := Nonempty.intro (WeakLimitCone.ofLimitCone (getLimitCone F))

theorem HasWeakLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
@[no_expose]
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
  Classical.choice <| HasWeakLimit.exists_weakLimitCone

variable (J C) in
/-- `C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`. -/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  hasWeakLimit : ∀ F : J ⥤ C, HasWeakLimit F := by infer_instance

attribute [instance] HasWeakLimitsOfShape.hasWeakLimit

instance (priority := 100) [HasLimitsOfShape J C] : HasWeakLimitsOfShape J C where

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
theorem weakLimit.cone_pt {F : J ⥤ C} [HasWeakLimit F] :
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

/-- Transport evidence that a cone is a weak limit cone across an isomorphism of cones. -/
@[simps]
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom

/-- Isomorphism of cones preserves whether or not they are weak limit cones. -/
def equivIsoWeakLimit {r t : Cone F} (i : r ≅ t) : IsWeakLimit r ≃ IsWeakLimit t where
  toFun h := h.ofIsoWeakLimit i
  invFun h := h.ofIsoWeakLimit i.symm
  left_inv _ := by simp [ofIsoWeakLimit]
  right_inv _ := by simp [ofIsoWeakLimit]

@[simp]
theorem equivIsoWeakLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit r) :
    equivIsoWeakLimit i P = P.ofIsoWeakLimit i :=
  rfl

@[simp]
theorem equivIsoWeakLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsWeakLimit t) :
    (equivIsoWeakLimit i).symm P = P.ofIsoWeakLimit i.symm :=
  rfl

/-- The versal morphism from any other cone to a weak limit cone. -/
@[simps]
def liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

/-- Alternative constructor for `isWeakLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
def mkOfConeMorphism {t : Cone F} (lift : ∀ s : Cone F, s ⟶ t) : IsWeakLimit t where
  lift s := (lift s).hom

/-- Given a right adjoint functor between categories of cones,
the image of a weak limit cone is a weak limit cone.
-/
def ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c) :=
  mkOfConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))

/-- Given two functors which have equivalent categories of cones, we can transport evidence of
a weak limit cone across the equivalence.
-/
lemma iff_of_cone_equiv {D : Type*} [Category* D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    Nonempty (IsWeakLimit (h.functor.obj c)) ↔ Nonempty (IsWeakLimit c) :=
  ⟨fun P ↦ Nonempty.intro (IsWeakLimit.ofIsoWeakLimit
    (IsWeakLimit.ofRightAdjoint h.toAdjunction P.some) (h.unitIso.symm.app c)),
   fun P ↦ Nonempty.intro (IsWeakLimit.ofRightAdjoint h.symm.toAdjunction P.some)⟩

/-- A cone postcomposed with a natural isomorphism is a weak limit cone
if and only if the original cone is.
-/
lemma postcompose_hom_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.hom).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  iff_of_cone_equiv (Cone.postcomposeEquivalence α)

/-- A cone postcomposed with the inverse of a natural isomorphism is a weak limit cone
if and only if the original cone is.
-/
lemma postcompose_inv_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    Nonempty (IsWeakLimit ((Cone.postcompose α.inv).obj c)) ↔ Nonempty (IsWeakLimit c) :=
  postcompose_hom_iff_of_iso α.symm c

/-- Constructing an equivalence between `Nonempty (IsWeakLimit c)` and `Nonempty (IsWeakLimit d)`
from a natural isomorphism between the underlying functors, and then an isomorphism between `c`
transported along this and `d`.
-/
lemma iff_of_natIso_of_iso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
    (w : (Cone.postcompose α.hom).obj c ≅ d) :
    Nonempty (IsWeakLimit c) ↔  Nonempty (IsWeakLimit d) :=
  (postcompose_hom_iff_of_iso α _).symm.trans (IsWeakLimit.equivIsoWeakLimit w).nonempty_congr

end IsWeakLimit

/-- If a functor `F` has a weak limit, so does any naturally isomorphic functor.
-/
theorem hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G :=
  HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit :=
        Nonempty.some ((IsWeakLimit.postcompose_hom_iff_of_iso α _ ).mpr
        (Nonempty.intro (weakLimit.isWeakLimit F))) }

theorem hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWeakLimit G :=
  ⟨fun _ ↦ hasWeakLimit_of_iso α, fun _ ↦ hasWeakLimit_of_iso α.symm⟩

end CategoryTheory.Limits
