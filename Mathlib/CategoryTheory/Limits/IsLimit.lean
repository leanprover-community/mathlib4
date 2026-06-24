/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Batteries.Tactic.Congr

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The main structures defined in this file is
* `IsLimit c`, for `c : Cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,

See also `CategoryTheory.Limits.HasLimits` which further builds:
* `LimitCone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `HasLimit F`, asserting the mere existence of some limit cone for `F`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C]
variable {F : J ⥤ C}

/-- A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`. -/
@[stacks 002E]
structure IsLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch
  /-- It is the unique such map to do this -/
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt) (_ : ∀ j : J, m ≫ t.π.app j = s.π.app j), m = lift s := by
    cat_disch

set_option backward.defeqAttrib.useBackward true in
/-- A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`. -/
@[stacks 002F, to_dual]
structure IsColimit (t : Cocone F) where
  /-- `t.pt` maps to all other cocone covertices -/
  desc : ∀ s : Cocone F, t.pt ⟶ s.pt
  /-- The map `desc` makes the diagram with the natural transformations commute -/
  fac : ∀ (s : Cocone F) (j : J), dsimp% t.ι.app j ≫ desc s = s.ι.app j := by cat_disch
  /-- `desc` is the unique such map -/
  uniq :
    ∀ (s : Cocone F) (m : t.pt ⟶ s.pt) (_ : ∀ j : J, t.ι.app j ≫ m = s.ι.app j), m = desc s := by
    cat_disch

attribute [reassoc (attr := simp)] IsLimit.fac IsColimit.fac

to_dual_name_hint Lift Desc, Left Right

namespace IsLimit

@[to_dual]
instance subsingleton {t : Cone F} : Subsingleton (IsLimit t) :=
  ⟨by intro P Q; cases P; cases Q; congr; cat_disch⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
@[to_dual (reorder := s P t)
/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/]
def map {F G : J ⥤ C} (s : Cone F) {t : Cone G} (P : IsLimit t) (α : F ⟶ G) : s.pt ⟶ t.pt :=
  P.lift ((Cone.postcompose α).obj s)

-- The `set_option` is needed to make reassoc generate the right theorem
set_option backward.isDefEq.respectTransparency false in
@[to_dual (attr := reassoc (attr := simp)) (reorder := c hd d) ι_map]
theorem map_π {F G : J ⥤ C} (c : Cone F) {d : Cone G} (hd : IsLimit d) (α : F ⟶ G) (j : J) :
    hd.map c α ≫ d.π.app j = c.π.app j ≫ α.app j :=
  fac _ _ _

@[to_dual (attr := simp)]
theorem lift_self {c : Cone F} (t : IsLimit c) : t.lift c = 𝟙 c.pt :=
  (t.uniq _ _ fun _ => id_comp _).symm

-- Repackaging the definition in terms of cone morphisms.
/-- The universal morphism from any other cone to a limit cone. -/
@[to_dual (attr := simps)
/-- The universal morphism from a colimit cocone to any other cocone. -/]
def liftConeMorphism {t : Cone F} (h : IsLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

@[to_dual]
theorem uniq_cone_morphism {s t : Cone F} (h : IsLimit t) {f f' : s ⟶ t} : f = f' :=
  have : ∀ {g : s ⟶ t}, g = h.liftConeMorphism s := by
    intro g; apply ConeMorphism.ext; exact h.uniq _ _ g.w
  this.trans this.symm

/-- Restating the definition of a limit cone in terms of the ∃! operator. -/
@[to_dual /-- Restating the definition of a colimit cocone in terms of the ∃! operator. -/]
theorem existsUnique {t : Cone F} (h : IsLimit t) (s : Cone F) :
    ∃! l : s.pt ⟶ t.pt, ∀ j, l ≫ t.π.app j = s.π.app j :=
  ⟨h.lift s, h.fac s, h.uniq s⟩

/-- Noncomputably make a limit cone from the existence of unique factorizations. -/
@[to_dual /-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/]
def ofExistsUnique {t : Cone F}
    (ht : ∀ s : Cone F, ∃! l : s.pt ⟶ t.pt, ∀ j, l ≫ t.π.app j = s.π.app j) : IsLimit t := by
  choose s hs hs' using ht
  exact ⟨s, hs, hs'⟩

/-- Alternative constructor for `isLimit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[to_dual (attr := simps)
/-- Alternative constructor for `IsColimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/]
def mkConeMorphism {t : Cone F} (lift : ∀ s : Cone F, s ⟶ t)
    (uniq : ∀ (s : Cone F) (m : s ⟶ t), m = lift s) : IsLimit t where
  lift s := (lift s).hom
  uniq s m w :=
    have : ConeMorphism.mk m w = lift s := by apply uniq
    congrArg ConeMorphism.hom this

/-- Limit cones on `F` are unique up to isomorphism. -/
@[to_dual (attr := simps) /-- Colimit cocones on `F` are unique up to isomorphism. -/]
def uniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s ≅ t where
  hom := Q.liftConeMorphism s
  inv := P.liftConeMorphism t
  hom_inv_id := P.uniq_cone_morphism
  inv_hom_id := Q.uniq_cone_morphism

/-- Any cone morphism between limit cones is an isomorphism. -/
@[to_dual (reorder := P Q) /-- Any cocone morphism between colimit cocones is an isomorphism. -/]
theorem hom_isIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (f : s ⟶ t) : IsIso f :=
  ⟨⟨P.liftConeMorphism t, ⟨P.uniq_cone_morphism, Q.uniq_cone_morphism⟩⟩⟩

/-- Limits of `F` are unique up to isomorphism. -/
@[to_dual /-- Colimits of `F` are unique up to isomorphism. -/]
def conePointUniqueUpToIso {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) : s.pt ≅ t.pt :=
  (Cone.forget F).mapIso (uniqueUpToIso P Q)

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_inv]
theorem conePointUniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.app j :=
  (uniqueUpToIso P Q).hom.w _

@[to_dual (attr := reassoc (attr := simp)) comp_coconePointUniqueUpToIso_hom]
theorem conePointUniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) :
    (conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.app j :=
  (uniqueUpToIso P Q).inv.w _

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_inv_desc]
theorem lift_comp_conePointUniqueUpToIso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    P.lift r ≫ (conePointUniqueUpToIso P Q).hom = Q.lift r :=
  Q.uniq _ _ (by simp)

@[to_dual (attr := reassoc (attr := simp)) coconePointUniqueUpToIso_hom_desc]
theorem lift_comp_conePointUniqueUpToIso_inv {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t) :
    Q.lift r ≫ (conePointUniqueUpToIso P Q).inv = P.lift r :=
  P.uniq _ _ (by simp)

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
@[to_dual
/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/]
def ofIsoLimit {r t : Cone F} (P : IsLimit r) (i : r ≅ t) : IsLimit t :=
  IsLimit.mkConeMorphism (fun s => P.liftConeMorphism s ≫ i.hom) fun s m => by
    rw [← i.comp_inv_eq]; apply P.uniq_cone_morphism

@[to_dual (attr := simp)]
theorem ofIsoLimit_lift {r t : Cone F} (P : IsLimit r) (i : r ≅ t) (s) :
    (P.ofIsoLimit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
@[to_dual /-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/]
def equivIsoLimit {r t : Cone F} (i : r ≅ t) : IsLimit r ≃ IsLimit t where
  toFun h := h.ofIsoLimit i
  invFun h := h.ofIsoLimit i.symm
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]
theorem equivIsoLimit_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit r) :
    equivIsoLimit i P = P.ofIsoLimit i :=
  rfl

@[to_dual (attr := simp)]
theorem equivIsoLimit_symm_apply {r t : Cone F} (i : r ≅ t) (P : IsLimit t) :
    (equivIsoLimit i).symm P = P.ofIsoLimit i.symm :=
  rfl

/-- If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
@[to_dual
/-- If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/]
def ofPointIso {r t : Cone F} (P : IsLimit r) [i : IsIso (P.lift t)] : IsLimit t :=
  ofIsoLimit P (by
    haveI : IsIso (P.liftConeMorphism t).hom := i
    haveI : IsIso (P.liftConeMorphism t) := Cone.cone_iso_of_hom_iso _
    symm
    apply asIso (P.liftConeMorphism t))

variable {t : Cone F}

set_option backward.defeqAttrib.useBackward true in
@[to_dual]
theorem hom_lift (h : IsLimit t) {W : C} (m : W ⟶ t.pt) :
    m = h.lift { pt := W, π := { app := fun b => m ≫ t.π.app b } } :=
  h.uniq { pt := W, π := { app := fun b => m ≫ t.π.app b } } m fun _ => rfl

/-- Two morphisms into a limit are equal if their compositions with
each cone morphism are equal. -/
@[to_dual /-- Two morphisms out of a colimit are equal if their compositions with
each cocone morphism are equal. -/]
theorem hom_ext (h : IsLimit t) {W : C} {f f' : W ⟶ t.pt}
    (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) :
    f = f' := by
  rw [h.hom_lift f, h.hom_lift f']; congr; exact funext w

@[to_dual]
lemma nonempty_isLimit_iff_isIso_lift {s t : Cone F} (hs : IsLimit s) :
    Nonempty (IsLimit t) ↔ IsIso (hs.lift t) :=
  ⟨fun ⟨ht⟩ ↦ ⟨ht.lift s, ht.hom_ext (by simp), hs.hom_ext (by simp)⟩, fun h ↦ ⟨hs.ofPointIso⟩⟩

/-- Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
@[to_dual
/-- Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/]
def ofRightAdjoint {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} {left : Cone F ⥤ Cone G}
    {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsLimit c) : IsLimit (right.obj c) :=
  mkConeMorphism (fun s => adj.homEquiv s c (t.liftConeMorphism _))
    fun _ _ => (Adjunction.eq_homEquiv_apply _ _ _).2 t.uniq_cone_morphism

/-- Given two functors which have equivalent categories of cones, we can transport a limiting cone
across the equivalence.
-/
def ofConeEquiv {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F) {c : Cone G} :
    IsLimit (h.functor.obj c) ≃ IsLimit c where
  toFun P := ofIsoLimit (ofRightAdjoint h.toAdjunction P) (h.unitIso.symm.app c)
  invFun := ofRightAdjoint h.symm.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
@[to_dual existing]
def _root_.CategoryTheory.Limits.IsColimit.ofCoconeEquiv {D : Type u₄} [Category.{v₄} D]
    {G : K ⥤ D} (h : Cocone G ≌ Cocone F) {c : Cocone G} :
    IsColimit (h.functor.obj c) ≃ IsColimit c where
  toFun P := IsColimit.ofIsoColimit (IsColimit.ofLeftAdjoint h.symm.toAdjunction P)
    (h.unitIso.symm.app c)
  invFun := IsColimit.ofLeftAdjoint h.toAdjunction
  left_inv := by cat_disch
  right_inv := by cat_disch

@[to_dual (attr := simp)]
theorem ofConeEquiv_apply_lift {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D} (h : Cone G ≌ Cone F)
    {c : Cone G} (P : IsLimit (h.functor.obj c)) (s) :
    (ofConeEquiv h P).lift s =
      ((h.unitIso.hom.app s).hom ≫ (h.inverse.map (P.liftConeMorphism (h.functor.obj s))).hom) ≫
        (h.unitIso.inv.app c).hom :=
  rfl

@[to_dual (attr := simp)]
theorem ofConeEquiv_symm_apply_lift {D : Type u₄} [Category.{v₄} D] {G : K ⥤ D}
    (h : Cone G ≌ Cone F) {c : Cone G} (P : IsLimit c) (s) :
    ((ofConeEquiv h).symm P).lift s =
      (h.counitIso.inv.app s).hom ≫ (h.functor.map (P.liftConeMorphism (h.inverse.obj s))).hom :=
  rfl

@[deprecated (since := "2026-06-21")] alias ofConeEquiv_apply_desc := ofConeEquiv_apply_lift
@[deprecated (since := "2026-06-21")]
alias ofConeEquiv_symm_apply_desc := ofConeEquiv_symm_apply_lift

/-- A cone postcomposed with a natural isomorphism is a limit cone
if and only if the original cone is.
-/
@[to_dual precomposeInvEquiv
/-- A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/]
def postcomposeHomEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) :
    IsLimit ((Cone.postcompose α.hom).obj c) ≃ IsLimit c :=
  ofConeEquiv (Cone.postcomposeEquivalence α)

/-- A cone postcomposed with the inverse of a natural isomorphism is a limit cone
if and only if the original cone is.
-/
@[to_dual precomposeHomEquiv
/-- A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/]
def postcomposeInvEquiv {F G : J ⥤ C} (α : F ≅ G) (c : Cone G) :
    IsLimit ((Cone.postcompose α.inv).obj c) ≃ IsLimit c :=
  postcomposeHomEquiv α.symm c

/-- Constructing an equivalence `IsLimit c ≃ IsLimit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/
@[to_dual
/-- Constructing an equivalence `isColimit c ≃ isColimit d` from a natural isomorphism
between the underlying functors, and then an isomorphism between `c` transported along this and `d`.
-/]
def equivOfNatIsoOfIso {F G : J ⥤ C} (α : F ≅ G) (c : Cone F) (d : Cone G)
    (w : (Cone.postcompose α.hom).obj c ≅ d) : IsLimit c ≃ IsLimit d :=
  (postcomposeHomEquiv α _).symm.trans (equivIsoLimit w)

set_option backward.defeqAttrib.useBackward true in
/-- The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[to_dual (attr := simps)
/-- The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/]
def conePointsIsoOfNatIso {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s) (Q : IsLimit t)
    (w : F ≅ G) : s.pt ≅ t.pt where
  hom := Q.map s w.hom
  inv := P.map t w.inv
  hom_inv_id := P.hom_ext (by simp)
  inv_hom_id := Q.hom_ext (by simp)

set_option linter.translateOverwrite false in
attribute [to_dual existing IsColimit.coconePointsIsoOfNatIso_inv] conePointsIsoOfNatIso_hom
set_option linter.translateOverwrite false in
attribute [to_dual existing IsColimit.coconePointsIsoOfNatIso_hom] conePointsIsoOfNatIso_inv

@[to_dual (attr := reassoc) comp_coconePointsIsoOfNatIso_inv]
theorem conePointsIsoOfNatIso_hom_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (w : F ≅ G) (j : J) :
    (conePointsIsoOfNatIso P Q w).hom ≫ t.π.app j = s.π.app j ≫ w.hom.app j := by simp

@[to_dual (attr := reassoc) comp_coconePointsIsoOfNatIso_hom]
theorem conePointsIsoOfNatIso_inv_comp {F G : J ⥤ C} {s : Cone F} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (w : F ≅ G) (j : J) :
    (conePointsIsoOfNatIso P Q w).inv ≫ s.π.app j = t.π.app j ≫ w.inv.app j := by simp

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_inv_desc]
theorem lift_comp_conePointsIsoOfNatIso_hom {F G : J ⥤ C} {r s : Cone F} {t : Cone G}
    (P : IsLimit s) (Q : IsLimit t) (w : F ≅ G) :
    P.lift r ≫ (conePointsIsoOfNatIso P Q w).hom = Q.map r w.hom :=
  Q.hom_ext (by simp)

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc) coconePointsIsoOfNatIso_hom_desc]
theorem lift_comp_conePointsIsoOfNatIso_inv {F G : J ⥤ C} {r s : Cone G} {t : Cone F}
    (P : IsLimit t) (Q : IsLimit s) (w : F ≅ G) :
    Q.lift r ≫ (conePointsIsoOfNatIso P Q w).inv = P.map r w.inv :=
  P.hom_ext (by simp)

section Equivalence

open CategoryTheory.Equivalence

/-- If `s : Cone F` is a limit cone, so is `s` whiskered by an equivalence `e`. -/
def whiskerEquivalence {s : Cone F} (P : IsLimit s) (e : K ≌ J) : IsLimit (s.whisker e.functor) :=
  ofRightAdjoint (Cone.whiskeringEquivalence e).symm.toAdjunction P

/-- If `s : Cocone F` is a colimit cocone, so is `s` whiskered by an equivalence `e`. -/
@[to_dual existing]
def _root_.CategoryTheory.Limits.IsColimit.whiskerEquivalence {s : Cocone F}
    (P : IsColimit s) (e : K ≌ J) : IsColimit (s.whisker e.functor) :=
  IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).toAdjunction P

/-- If `s : Cone F` whiskered by an equivalence `e` is a limit cone, so is `s`. -/
def ofWhiskerEquivalence {s : Cone F} (e : K ≌ J) (P : IsLimit (s.whisker e.functor)) : IsLimit s :=
  equivIsoLimit ((Cone.whiskeringEquivalence e).unitIso.app s).symm
    (ofRightAdjoint (Cone.whiskeringEquivalence e).toAdjunction P)

/-- If `s : Cocone F` whiskered by an equivalence `e` is a colimit cocone, so is `s`. -/
@[to_dual existing]
def _root_.CategoryTheory.Limits.IsColimit.ofWhiskerEquivalence {s : Cocone F} (e : K ≌ J)
    (P : IsColimit (s.whisker e.functor)) : IsColimit s :=
  IsColimit.equivIsoColimit ((Cocone.whiskeringEquivalence e).unitIso.app s).symm
    (IsColimit.ofLeftAdjoint (Cocone.whiskeringEquivalence e).symm.toAdjunction P)

/-- Given an equivalence of diagrams `e`, `s` is a limit cone iff `s.whisker e.functor` is. -/
@[to_dual
/-- Given an equivalence of diagrams `e`, `s` is a colimit cocone iff `s.whisker e.functor` is. -/]
def whiskerEquivalenceEquiv {s : Cone F} (e : K ≌ J) : IsLimit s ≃ IsLimit (s.whisker e.functor) :=
  ⟨fun h => h.whiskerEquivalence e, ofWhiskerEquivalence e, by cat_disch, by cat_disch⟩

/-- A limit cone extended by an isomorphism is a limit cone. -/
@[to_dual /-- A colimit cocone extended by an isomorphism is a colimit cocone. -/]
def extendIso {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit s) :
    IsLimit (s.extend i) :=
  IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i))

/-- A cone is a limit cone if its extension by an isomorphism is. -/
@[to_dual /-- A cocone is a colimit cocone if its extension by an isomorphism is. -/]
def ofExtendIso {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] (hs : IsLimit (s.extend i)) :
    IsLimit s :=
  IsLimit.ofIsoLimit hs (Cone.extendIso s (asIso' i)).symm

/-- A cone is a limit cone iff its extension by an isomorphism is. -/
@[to_dual /-- A cocone is a colimit cocone iff its extension by an isomorphism is. -/]
def extendIsoEquiv {s : Cone F} {X : C} (i : X ⟶ s.pt) [IsIso i] :
    IsLimit s ≃ IsLimit (s.extend i) :=
  equivOfSubsingletonOfSubsingleton (extendIso i) (ofExtendIso i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- We can prove two cone points `(s : Cone F).pt` and `(t : Cone G).pt` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[to_dual (attr := simps)
/-- We can prove two cocone points `(s : Cocone F).pt` and `(t : Cocone G).pt` are isomorphic if
* both cocones are colimit cocones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/]
def conePointsIsoOfEquivalence {F : J ⥤ C} {s : Cone F} {G : K ⥤ C} {t : Cone G} (P : IsLimit s)
    (Q : IsLimit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.pt ≅ t.pt :=
  let w' : e.inverse ⋙ F ≅ G := (isoWhiskerLeft e.inverse w).symm ≪≫ invFunIdAssoc e G
  { hom := Q.lift ((Cone.equivalenceOfReindexing e.symm w').functor.obj s)
    inv := P.lift ((Cone.equivalenceOfReindexing e w).functor.obj t)
    hom_inv_id := by
      apply hom_ext P; intro j
      dsimp [w']
      simp only [Limits.Cone.whisker_π, Limits.Cone.postcompose_obj_π, fac, whiskerLeft_app,
        assoc, id_comp, invFunIdAssoc_hom_app, fac_assoc, NatTrans.comp_app]
      rw [counit_app_functor, ← Functor.comp_map, ← w.inv.naturality_assoc]
      simp
    inv_hom_id := by
      apply hom_ext Q
      cat_disch }

set_option linter.translateOverwrite false in
attribute [to_dual existing IsColimit.coconePointsIsoOfEquivalence_inv]
  conePointsIsoOfEquivalence_hom
set_option linter.translateOverwrite false in
attribute [to_dual existing IsColimit.coconePointsIsoOfEquivalence_hom]
  conePointsIsoOfEquivalence_inv

end Equivalence

set_option backward.defeqAttrib.useBackward true in
/-- The universal property of a limit cone: a map `W ⟶ t.pt` is the same as
a cone on `F` with cone point `W`. -/
@[to_dual (attr := simps apply)
/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
a cocone on `F` with cone point `W`. -/]
def homEquiv (h : IsLimit t) {W : C} : (W ⟶ t.pt) ≃ ((Functor.const J).obj W ⟶ F) where
  toFun f := (t.extend f).π
  invFun π := h.lift (Cone.mk _ π)
  left_inv f := h.hom_ext (by simp)
  right_inv π := by cat_disch

@[to_dual (attr := reassoc (attr := simp)) ι_app_homEquiv_symm]
lemma homEquiv_symm_π_app (h : IsLimit t) {W : C}
    (f : (const J).obj W ⟶ F) (j : J) :
    h.homEquiv.symm f ≫ t.π.app j = f.app j := by
  simp [homEquiv]

set_option backward.defeqAttrib.useBackward true in
@[to_dual]
lemma homEquiv_symm_naturality (h : IsLimit t) {W W' : C}
    (f : (const J).obj W ⟶ F) (g : W' ⟶ W) :
    h.homEquiv.symm ((Functor.const _).map g ≫ f) = g ≫ h.homEquiv.symm f :=
  h.homEquiv.injective (by aesop)

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
a cone on `F` with cone point `W`. -/
@[to_dual
/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
a cocone on `F` with cone point `W`. -/]
def homIso (h : IsLimit t) (W : C) : ULift.{u₁} (W ⟶ t.pt : Type v₃) ≅ (const J).obj W ⟶ F :=
  Equiv.toIso (Equiv.ulift.trans h.homEquiv)

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
@[simp]
theorem homIso_hom (h : IsLimit t) {W : C} :
    (IsLimit.homIso h W).hom = ↾fun f ↦ (t.extend f.down).π :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with cone point `W`. -/
def natIso (h : IsLimit t) : yoneda.obj t.pt ⋙ uliftFunctor.{u₁} ≅ F.cones := by
  refine NatIso.ofComponents (fun W => IsLimit.homIso h (unop W))

set_option backward.defeqAttrib.useBackward true in
/-- Another, more explicit, formulation of the universal property of a limit cone.
See also `homIso`. -/
def homIso' (h : IsLimit t) (W : C) :
    (ULift.{u₁} (W ⟶ t.pt : Type v₃)) ≅
      { p : ∀ j, W ⟶ F.obj j // ∀ {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
  h.homIso W ≪≫
    { hom := ↾fun π =>
        ⟨fun j => π.app j, fun f => by convert! ← (π.naturality f).symm; apply id_comp⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [id_comp]; exact (p.2 f).symm } }

/-- If `G : C → D` is a faithful functor which sends t to a limit cone,
then it suffices to check that the induced maps for the image of t
can be lifted to maps of `C`. -/
@[to_dual /-- If `G : C → D` is a faithful functor which sends t to a colimit cocone,
then it suffices to check that the induced maps for the image of t
can be lifted to maps of `C`. -/]
def ofFaithful {t : Cone F} {D : Type u₄} [Category.{v₄} D] (G : C ⥤ D) [G.Faithful]
    (ht : IsLimit (mapCone G t)) (lift : ∀ s : Cone F, s.pt ⟶ t.pt)
    (h : ∀ s, G.map (lift s) = ht.lift (mapCone G s)) : IsLimit t :=
  { lift
    fac := fun s j => by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac
    uniq := fun s m w => by
      apply G.map_injective; rw [h]
      refine ht.uniq (mapCone G s) _ fun j => ?_
      convert! ← congrArg (fun f => G.map f) (w j)
      apply G.map_comp }

/-- If `F` and `G` are naturally isomorphic, then `F.mapCone c` being a limit implies
`G.mapCone c` is also a limit.
-/
@[to_dual
/-- If `F` and `G` are naturally isomorphic, then `F.mapCocone c` being a colimit implies
`G.mapCocone c` is also a colimit.
-/]
def mapConeEquiv {D : Type u₄} [Category.{v₄} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : Cone K}
    (t : IsLimit (mapCone F c)) : IsLimit (mapCone G c) := by
  apply postcomposeInvEquiv (isoWhiskerLeft K h :) (mapCone G c) _
  apply t.ofIsoLimit (postcomposeWhiskerLeftMapCone h.symm c).symm

-- TODO: `to_dual` doesn't yet know that it shouldn't translate the category on `Type _`.
/-- A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def isoUniqueConeMorphism {t : Cone F} :
    IsLimit t ≅ ∀ s, Unique (s ⟶ t) where
  hom := ↾fun h s ↦
    { default := h.liftConeMorphism s
      uniq := fun _ => h.uniq_cone_morphism }
  inv := ↾fun h =>
    { lift := fun s => (h s).default.hom
      uniq := fun s f w => congrArg ConeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : F.cones.RepresentableBy X)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point
`Y`. -/
def coneOfHom {Y : C} (f : Y ⟶ X) : Cone F where
  pt := Y
  π := h.homEquiv f

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.pt ⟶ X`. -/
def homOfCone (s : Cone F) : s.pt ⟶ X :=
  h.homEquiv.symm s.π

@[simp]
theorem coneOfHom_homOfCone (s : Cone F) : coneOfHom h (homOfCone h s) = s := by
  dsimp [coneOfHom, homOfCone]
  match s with
  | .mk s_pt s_π =>
    congr
    exact h.homEquiv.apply_symm_apply s_π

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homOfCone_coneOfHom {Y : C} (f : Y ⟶ X) : homOfCone h (coneOfHom h f) = f := by
  simp [coneOfHom, homOfCone]

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limitCone : Cone F :=
  coneOfHom h (𝟙 X)

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
theorem coneOfHom_fac {Y : C} (f : Y ⟶ X) : coneOfHom h f = (limitCone h).extend f := by
  dsimp [coneOfHom, limitCone, Cone.extend]
  congr
  conv_lhs => rw [← Category.comp_id f]
  exact h.homEquiv_comp f (𝟙 X)

/-- If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
corresponding morphism. -/
theorem cone_fac (s : Cone F) : (limitCone h).extend (homOfCone h s) = s := by
  rw [← coneOfHom_homOfCone h s]
  conv_lhs => simp only [homOfCone_coneOfHom]
  apply (coneOfHom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/-- If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def ofRepresentableBy {X : C} (h : F.cones.RepresentableBy X) : IsLimit (limitCone h) where
  lift s := homOfCone h s
  fac s j := by
    have h := cone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCone_coneOfHom h m]
    congr
    rw [coneOfHom_fac]
    dsimp [Cone.extend]; cases s; congr with j; exact w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a limit cone, `F.cones` is representable by the point of the cone. -/
def representableBy (hc : IsLimit t) : F.cones.RepresentableBy t.pt where
  homEquiv := hc.homEquiv
  homEquiv_comp {X X'} f g := NatTrans.ext <| funext fun j ↦ by simp

end

end IsLimit


namespace IsColimit


variable {t : Cocone F}


@[simp]
theorem homIso_hom (h : IsColimit t) {W : C} :
    (IsColimit.homIso h W).hom = ↾fun f ↦ (t.extend f.down).ι :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with cone point `W`. -/
def natIso (h : IsColimit t) : coyoneda.obj (op t.pt) ⋙ uliftFunctor.{u₁} ≅ F.cocones :=
  NatIso.ofComponents (IsColimit.homIso h)

set_option backward.defeqAttrib.useBackward true in
/-- Another, more explicit, formulation of the universal property of a colimit cocone.
See also `homIso`. -/
def homIso' (h : IsColimit t) (W : C) :
    (ULift.{u₁} (t.pt ⟶ W : Type v₃)) ≅
      { p : ∀ j, F.obj j ⟶ W // ∀ {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
  h.homIso W ≪≫
    { hom := ↾fun ι =>
        ⟨fun j => ι.app j, fun {j} {j'} f => by convert! ← ι.naturality f; apply comp_id⟩
      inv := ↾fun p =>
        { app := fun j => p.1 j
          naturality := fun j j' f => by dsimp; rw [comp_id]; exact p.2 f } }


set_option backward.defeqAttrib.useBackward true in
/-- A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def isoUniqueCoconeMorphism {t : Cocone F} :
    IsColimit t ≅ ∀ s, Unique (t ⟶ s) where
  hom := ↾fun h s ↦
    { default := h.descCoconeMorphism s
      uniq := fun _ => h.uniq_cocone_morphism }
  inv := ↾fun h ↦
    { desc := fun s => (h s).default.hom
      uniq := fun s f w => congrArg CoconeMorphism.hom ((h s).uniq ⟨f, w⟩) }

namespace OfNatIso

variable {X : C} (h : F.cocones.CorepresentableBy X)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone
point `Y`. -/
def coconeOfHom {Y : C} (f : X ⟶ Y) : Cocone F where
  pt := Y
  ι := h.homEquiv f

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.pt`. -/
def homOfCocone (s : Cocone F) : X ⟶ s.pt :=
  h.homEquiv.symm s.ι

@[simp]
theorem coconeOfHom_homOfCocone (s : Cocone F) : coconeOfHom h (homOfCocone h s) = s := by
  dsimp [coconeOfHom, homOfCocone]
  match s with
  | .mk s_pt s_ι =>
    congr
    exact h.homEquiv.apply_symm_apply s_ι

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homOfCocone_coconeOfHom {Y : C} (f : X ⟶ Y) : homOfCocone h (coconeOfHom h f) = f := by
  simp [homOfCocone, coconeOfHom]

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimitCocone : Cocone F :=
  coconeOfHom h (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
theorem coconeOfHom_fac {Y : C} (f : X ⟶ Y) : coconeOfHom h f = (colimitCocone h).extend f := by
  dsimp [coconeOfHom, colimitCocone, Cocone.extend]
  congr
  conv_lhs => rw [← Category.id_comp f]
  exact h.homEquiv_comp f (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
corresponding morphism. -/
theorem cocone_fac (s : Cocone F) : (colimitCocone h).extend (homOfCocone h s) = s := by
  rw [← coconeOfHom_homOfCocone h s]
  conv_lhs => simp only [homOfCocone_coconeOfHom]
  apply (coconeOfHom_fac _ _).symm

end OfNatIso

section

open OfNatIso

/-- If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def ofCorepresentableBy {X : C} (h : F.cocones.CorepresentableBy X) :
    IsColimit (colimitCocone h) where
  desc s := homOfCocone h s
  fac s j := by
    have h := cocone_fac h s
    cases s
    injection h with h₁ h₂
    simp only at h₂
    conv_rhs => rw [← h₂]
    rfl
  uniq s m w := by
    rw [← homOfCocone_coconeOfHom h m]
    congr
    rw [coconeOfHom_fac]
    dsimp [Cocone.extend]; cases s; congr with j; exact w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a colimit cocone, `F.cocones` is corepresentable by the point of the cocone. -/
def corepresentableBy (hc : IsColimit t) : F.cocones.CorepresentableBy t.pt where
  homEquiv := hc.homEquiv
  homEquiv_comp {X X'} f g := NatTrans.ext <| funext fun j ↦ by simp

end

end IsColimit

end CategoryTheory.Limits
