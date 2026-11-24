/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Cospan & Span

We define a category `WalkingCospan` (resp. `WalkingSpan`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

## References

* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

-- Porting note: `aesop cases` does not work on type synonyms like `WidePullbackShape`
-- attribute [local aesop safe cases] WidePullbackShape WalkingPair

to_dual_name_hint One Zero, Fst Inl, Snd Inr

/-- The type of objects for the diagram indexing a pullback, defined as a special case of
`WidePullbackShape`. -/
@[to_dual
/-- The type of objects for the diagram indexing a pushout, defined as a special case of
`WidePushoutShape`.
-/]
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair

/-- The left point of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The left point of the walking span. -/]
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left

/-- The right point of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The right point of the walking span. -/]
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right

/-- The central point of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The central point of the walking span. -/]
abbrev WalkingCospan.one : WalkingCospan :=
  none

namespace WalkingCospan

/-- The type of arrows for the diagram indexing a pullback. -/
@[to_dual (reorder := 1 2) /-- The type of arrows for the diagram indexing a pushout. -/]
abbrev Hom (X Y : WalkingCospan) : Type :=
  WidePullbackShape.Hom X Y

/-- The left arrow of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The left arrow of the walking span. -/]
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The right arrow of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The right arrow of the walking span. -/]
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _

/-- The identity arrows of the walking cospan. -/
@[to_dual (attr := match_pattern) /-- The identity arrows of the walking span. -/]
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X

@[to_dual]
instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  constructor; intros; simp [eq_iff_true_of_subsingleton]

end WalkingCospan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
def WalkingCospan.ext {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
    (w₁ : s.π.app WalkingCospan.left = i.hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.hom ≫ t.π.app WalkingCospan.right) : s ≅ t := by
  apply Cone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    dsimp at h₁
    simp only [Category.id_comp] at h₁
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    dsimp at h₂
    simp only [Category.id_comp] at h₂
    simp_rw [h₂, ← Category.assoc, ← w₁, ← h₁]
  · exact w₁
  · exact w₂

/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply Cocone.ext i _
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₁
    simp only [Category.comp_id] at h₁
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    dsimp at h₂
    simp only [Category.comp_id] at h₂
    simp_rw [← h₁, Category.assoc, w₁, h₂]
  · exact w₁
  · exact w₂

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
@[to_dual (attr := implicit_reducible)
/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/]
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g

@[to_dual (attr := simp)]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl

@[to_dual (attr := simp)]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y := rfl

@[to_dual (attr := simp)]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl

@[to_dual (attr := simp)]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f := rfl

@[to_dual (attr := simp)]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g := rfl

@[to_dual]
theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ := rfl

/-- Every diagram indexing a pullback is naturally isomorphic (actually, equal) to a `cospan` -/
@[to_dual (attr := simps (rhsMd := default))
/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/]
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor applied to a cospan is a cospan. -/
@[to_dual /-- A functor applied to a span is a span. -/]
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> simp)

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[to_dual (attr := simp)]
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ := rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ := rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _ := rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl

@[to_dual (attr := simp)]
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ := rfl

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

/-- Constructor for natural transformations between cospans. -/
@[simps]
def cospanHomMk {F G : WalkingCospan ⥤ C}
    (z : F.obj .one ⟶ G.obj .one) (l : F.obj .left ⟶ G.obj .left)
    (r : F.obj .right ⟶ G.obj .right)
    (hl : F.map inl ≫ z = l ≫ G.map inl := by cat_disch)
    (hr : F.map inr ≫ z = r ≫ G.map inr := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

/-- Constructor for natural isomorphisms between cospans. -/
@[simps!]
def cospanIsoMk {F G : WalkingCospan ⥤ C}
    (z : F.obj .one ≅ G.obj .one) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map inl ≫ z.hom = l.hom ≫ G.map inl := by cat_disch)
    (hr : F.map inr ≫ z.hom = r.hom ≫ G.map inr := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- Construct an isomorphism of cospans from components. -/
def cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
    cospan f g ≅ cospan f' g' :=
  cospanIsoMk iZ iX iY

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := rfl

@[simp]
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := rfl

@[simp]
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := rfl

@[simp]
theorem cospanExt_hom_app_left :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom := rfl

@[simp]
theorem cospanExt_hom_app_right :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom := rfl

@[simp]
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := rfl

@[simp]
theorem cospanExt_inv_app_left :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := rfl

@[simp]
theorem cospanExt_inv_app_right :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv :=
  rfl

@[simp]
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  rfl

end

section

/-- Constructor for natural transformations between spans. -/
@[simps]
def spanHomMk {F G : WalkingSpan ⥤ C}
    (z : F.obj .zero ⟶ G.obj .zero) (l : F.obj .left ⟶ G.obj .left)
    (r : F.obj .right ⟶ G.obj .right)
    (hl : F.map fst ≫ l = z ≫ G.map fst := by cat_disch)
    (hr : F.map snd ≫ r = z ≫ G.map snd := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _ | _); exacts [z, l, r]
  naturality := by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch

/-- Constructor for natural isomorphisms between spans. -/
@[simps!]
def spanIsoMk {F G : WalkingSpan ⥤ C}
    (z : F.obj .zero ≅ G.obj .zero) (l : F.obj .left ≅ G.obj .left)
    (r : F.obj .right ≅ G.obj .right)
    (hl : F.map fst ≫ l.hom = z.hom ≫ G.map fst := by cat_disch)
    (hr : F.map snd ≫ r.hom = z.hom ≫ G.map snd := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _ | _); exacts [z, l, r])
    (by rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals cat_disch)

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  spanIsoMk iX iY iZ

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := rfl

@[simp]
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := rfl

@[simp]
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := rfl

@[simp]
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := rfl

@[simp]
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := rfl

@[simp]
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := rfl

@[simp]
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := rfl

@[simp]
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := rfl

@[simp]
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := rfl

end

end

end CategoryTheory.Limits
