/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Cospan & Span

We define a category `WalkingCospan` (resp. `WalkingSpan`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

-- attribute [local tidy] tactic.case_bash Porting note: no tidy, no local

/-- The type of objects for the diagram indexing a pullback, defined as a special case of
`WidePullbackShape`. -/
abbrev WalkingCospan : Type :=
  WidePullbackShape WalkingPair
#align category_theory.limits.walking_cospan CategoryTheory.Limits.WalkingCospan

/-- The left point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.left : WalkingCospan :=
  some WalkingPair.left
#align category_theory.limits.walking_cospan.left CategoryTheory.Limits.WalkingCospan.left

/-- The right point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.right : WalkingCospan :=
  some WalkingPair.right
#align category_theory.limits.walking_cospan.right CategoryTheory.Limits.WalkingCospan.right

/-- The central point of the walking cospan. -/
@[match_pattern]
abbrev WalkingCospan.one : WalkingCospan :=
  none
#align category_theory.limits.walking_cospan.one CategoryTheory.Limits.WalkingCospan.one

/-- The type of objects for the diagram indexing a pushout, defined as a special case of
`WidePushoutShape`.
-/
abbrev WalkingSpan : Type :=
  WidePushoutShape WalkingPair
#align category_theory.limits.walking_span CategoryTheory.Limits.WalkingSpan

/-- The left point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.left : WalkingSpan :=
  some WalkingPair.left
#align category_theory.limits.walking_span.left CategoryTheory.Limits.WalkingSpan.left

/-- The right point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.right : WalkingSpan :=
  some WalkingPair.right
#align category_theory.limits.walking_span.right CategoryTheory.Limits.WalkingSpan.right

/-- The central point of the walking span. -/
@[match_pattern]
abbrev WalkingSpan.zero : WalkingSpan :=
  none
#align category_theory.limits.walking_span.zero CategoryTheory.Limits.WalkingSpan.zero

namespace WalkingCospan

/-- The type of arrows for the diagram indexing a pullback. -/
abbrev Hom : WalkingCospan → WalkingCospan → Type :=
  WidePullbackShape.Hom
#align category_theory.limits.walking_cospan.hom CategoryTheory.Limits.WalkingCospan.Hom

/-- The left arrow of the walking cospan. -/
@[match_pattern]
abbrev Hom.inl : left ⟶ one :=
  WidePullbackShape.Hom.term _
#align category_theory.limits.walking_cospan.hom.inl CategoryTheory.Limits.WalkingCospan.Hom.inl

/-- The right arrow of the walking cospan. -/
@[match_pattern]
abbrev Hom.inr : right ⟶ one :=
  WidePullbackShape.Hom.term _
#align category_theory.limits.walking_cospan.hom.inr CategoryTheory.Limits.WalkingCospan.Hom.inr

/-- The identity arrows of the walking cospan. -/
@[match_pattern]
abbrev Hom.id (X : WalkingCospan) : X ⟶ X :=
  WidePullbackShape.Hom.id X
#align category_theory.limits.walking_cospan.hom.id CategoryTheory.Limits.WalkingCospan.Hom.id

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by
  constructor; intros; simp [eq_iff_true_of_subsingleton]

end WalkingCospan

namespace WalkingSpan

/-- The type of arrows for the diagram indexing a pushout. -/
abbrev Hom : WalkingSpan → WalkingSpan → Type :=
  WidePushoutShape.Hom
#align category_theory.limits.walking_span.hom CategoryTheory.Limits.WalkingSpan.Hom

/-- The left arrow of the walking span. -/
@[match_pattern]
abbrev Hom.fst : zero ⟶ left :=
  WidePushoutShape.Hom.init _
#align category_theory.limits.walking_span.hom.fst CategoryTheory.Limits.WalkingSpan.Hom.fst

/-- The right arrow of the walking span. -/
@[match_pattern]
abbrev Hom.snd : zero ⟶ right :=
  WidePushoutShape.Hom.init _
#align category_theory.limits.walking_span.hom.snd CategoryTheory.Limits.WalkingSpan.Hom.snd

/-- The identity arrows of the walking span. -/
@[match_pattern]
abbrev Hom.id (X : WalkingSpan) : X ⟶ X :=
  WidePushoutShape.Hom.id X
#align category_theory.limits.walking_span.hom.id CategoryTheory.Limits.WalkingSpan.Hom.id

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by
  constructor; intros a b; simp [eq_iff_true_of_subsingleton]

end WalkingSpan

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C]

/-- To construct an isomorphism of cones over the walking cospan,
it suffices to construct an isomorphism
of the cone points and check it commutes with the legs to `left` and `right`. -/
def WalkingCospan.ext {F : WalkingCospan ⥤ C} {s t : Cone F} (i : s.pt ≅ t.pt)
    (w₁ : s.π.app WalkingCospan.left = i.hom ≫ t.π.app WalkingCospan.left)
    (w₂ : s.π.app WalkingCospan.right = i.hom ≫ t.π.app WalkingCospan.right) : s ≅ t := by
  apply Cones.ext i _
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
#align category_theory.limits.walking_cospan.ext CategoryTheory.Limits.WalkingCospan.ext

/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply Cocones.ext i _
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
#align category_theory.limits.walking_span.ext CategoryTheory.Limits.WalkingSpan.ext

/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : WalkingCospan ⥤ C :=
  WidePullbackShape.wideCospan Z (fun j => WalkingPair.casesOn j X Y) fun j =>
    WalkingPair.casesOn j f g
#align category_theory.limits.cospan CategoryTheory.Limits.cospan

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : WalkingSpan ⥤ C :=
  WidePushoutShape.wideSpan X (fun j => WalkingPair.casesOn j Y Z) fun j =>
    WalkingPair.casesOn j f g
#align category_theory.limits.span CategoryTheory.Limits.span

@[simp]
theorem cospan_left {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.left = X :=
  rfl
#align category_theory.limits.cospan_left CategoryTheory.Limits.cospan_left

@[simp]
theorem span_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.left = Y :=
  rfl
#align category_theory.limits.span_left CategoryTheory.Limits.span_left

@[simp]
theorem cospan_right {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).obj WalkingCospan.right = Y := rfl
#align category_theory.limits.cospan_right CategoryTheory.Limits.cospan_right

@[simp]
theorem span_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.right = Z :=
  rfl
#align category_theory.limits.span_right CategoryTheory.Limits.span_right

@[simp]
theorem cospan_one {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (cospan f g).obj WalkingCospan.one = Z :=
  rfl
#align category_theory.limits.cospan_one CategoryTheory.Limits.cospan_one

@[simp]
theorem span_zero {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).obj WalkingSpan.zero = X :=
  rfl
#align category_theory.limits.span_zero CategoryTheory.Limits.span_zero

@[simp]
theorem cospan_map_inl {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inl = f := rfl
#align category_theory.limits.cospan_map_inl CategoryTheory.Limits.cospan_map_inl

@[simp]
theorem span_map_fst {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.fst = f :=
  rfl
#align category_theory.limits.span_map_fst CategoryTheory.Limits.span_map_fst

@[simp]
theorem cospan_map_inr {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (cospan f g).map WalkingCospan.Hom.inr = g := rfl
#align category_theory.limits.cospan_map_inr CategoryTheory.Limits.cospan_map_inr

@[simp]
theorem span_map_snd {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : (span f g).map WalkingSpan.Hom.snd = g :=
  rfl
#align category_theory.limits.span_map_snd CategoryTheory.Limits.span_map_snd

theorem cospan_map_id {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : WalkingCospan) :
    (cospan f g).map (WalkingCospan.Hom.id w) = 𝟙 _ := rfl
#align category_theory.limits.cospan_map_id CategoryTheory.Limits.cospan_map_id

theorem span_map_id {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : WalkingSpan) :
    (span f g).map (WalkingSpan.Hom.id w) = 𝟙 _ := rfl
#align category_theory.limits.span_map_id CategoryTheory.Limits.span_map_id

/-- Every diagram indexing a pullback is naturally isomorphic (actually, equal) to a `cospan` -/
-- @[simps (config := { rhsMd := semireducible })]  Porting note: no semireducible
@[simps!]
def diagramIsoCospan (F : WalkingCospan ⥤ C) : F ≅ cospan (F.map inl) (F.map inr) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
#align category_theory.limits.diagram_iso_cospan CategoryTheory.Limits.diagramIsoCospan

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
-- @[simps (config := { rhsMd := semireducible })]  Porting note: no semireducible
@[simps!]
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
#align category_theory.limits.diagram_iso_span CategoryTheory.Limits.diagramIsoSpan

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor applied to a cospan is a cospan. -/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
#align category_theory.limits.cospan_comp_iso CategoryTheory.Limits.cospanCompIso

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

@[simp]
theorem cospanCompIso_app_left : (cospanCompIso F f g).app WalkingCospan.left = Iso.refl _ := rfl
#align category_theory.limits.cospan_comp_iso_app_left CategoryTheory.Limits.cospanCompIso_app_left

@[simp]
theorem cospanCompIso_app_right : (cospanCompIso F f g).app WalkingCospan.right = Iso.refl _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_app_right CategoryTheory.Limits.cospanCompIso_app_right

@[simp]
theorem cospanCompIso_app_one : (cospanCompIso F f g).app WalkingCospan.one = Iso.refl _ := rfl
#align category_theory.limits.cospan_comp_iso_app_one CategoryTheory.Limits.cospanCompIso_app_one

@[simp]
theorem cospanCompIso_hom_app_left : (cospanCompIso F f g).hom.app WalkingCospan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_hom_app_left CategoryTheory.Limits.cospanCompIso_hom_app_left

@[simp]
theorem cospanCompIso_hom_app_right : (cospanCompIso F f g).hom.app WalkingCospan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_hom_app_right CategoryTheory.Limits.cospanCompIso_hom_app_right

@[simp]
theorem cospanCompIso_hom_app_one : (cospanCompIso F f g).hom.app WalkingCospan.one = 𝟙 _ := rfl
#align category_theory.limits.cospan_comp_iso_hom_app_one CategoryTheory.Limits.cospanCompIso_hom_app_one

@[simp]
theorem cospanCompIso_inv_app_left : (cospanCompIso F f g).inv.app WalkingCospan.left = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_inv_app_left CategoryTheory.Limits.cospanCompIso_inv_app_left

@[simp]
theorem cospanCompIso_inv_app_right : (cospanCompIso F f g).inv.app WalkingCospan.right = 𝟙 _ :=
  rfl
#align category_theory.limits.cospan_comp_iso_inv_app_right CategoryTheory.Limits.cospanCompIso_inv_app_right

@[simp]
theorem cospanCompIso_inv_app_one : (cospanCompIso F f g).inv.app WalkingCospan.one = 𝟙 _ := rfl
#align category_theory.limits.cospan_comp_iso_inv_app_one CategoryTheory.Limits.cospanCompIso_inv_app_one

end

/-- A functor applied to a span is a span. -/
def spanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    span f g ⋙ F ≅ span (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
#align category_theory.limits.span_comp_iso CategoryTheory.Limits.spanCompIso

section

variable (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

@[simp]
theorem spanCompIso_app_left : (spanCompIso F f g).app WalkingSpan.left = Iso.refl _ := rfl
#align category_theory.limits.span_comp_iso_app_left CategoryTheory.Limits.spanCompIso_app_left

@[simp]
theorem spanCompIso_app_right : (spanCompIso F f g).app WalkingSpan.right = Iso.refl _ := rfl
#align category_theory.limits.span_comp_iso_app_right CategoryTheory.Limits.spanCompIso_app_right

@[simp]
theorem spanCompIso_app_zero : (spanCompIso F f g).app WalkingSpan.zero = Iso.refl _ := rfl
#align category_theory.limits.span_comp_iso_app_zero CategoryTheory.Limits.spanCompIso_app_zero

@[simp]
theorem spanCompIso_hom_app_left : (spanCompIso F f g).hom.app WalkingSpan.left = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_hom_app_left CategoryTheory.Limits.spanCompIso_hom_app_left

@[simp]
theorem spanCompIso_hom_app_right : (spanCompIso F f g).hom.app WalkingSpan.right = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_hom_app_right CategoryTheory.Limits.spanCompIso_hom_app_right

@[simp]
theorem spanCompIso_hom_app_zero : (spanCompIso F f g).hom.app WalkingSpan.zero = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_hom_app_zero CategoryTheory.Limits.spanCompIso_hom_app_zero

@[simp]
theorem spanCompIso_inv_app_left : (spanCompIso F f g).inv.app WalkingSpan.left = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_inv_app_left CategoryTheory.Limits.spanCompIso_inv_app_left

@[simp]
theorem spanCompIso_inv_app_right : (spanCompIso F f g).inv.app WalkingSpan.right = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_inv_app_right CategoryTheory.Limits.spanCompIso_inv_app_right

@[simp]
theorem spanCompIso_inv_app_zero : (spanCompIso F f g).inv.app WalkingSpan.zero = 𝟙 _ := rfl
#align category_theory.limits.span_comp_iso_inv_app_zero CategoryTheory.Limits.spanCompIso_inv_app_zero

end

section

variable {X Y Z X' Y' Z' : C} (iX : X ≅ X') (iY : Y ≅ Y') (iZ : Z ≅ Z')

section

variable {f : X ⟶ Z} {g : Y ⟶ Z} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}

/-- Construct an isomorphism of cospans from components. -/
def cospanExt (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom) :
    cospan f g ≅ cospan f' g' :=
  NatIso.ofComponents
    (by rintro (⟨⟩ | ⟨⟨⟩⟩); exacts [iZ, iX, iY])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])
#align category_theory.limits.cospan_ext CategoryTheory.Limits.cospanExt

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := by
  dsimp [cospanExt]
#align category_theory.limits.cospan_ext_app_left CategoryTheory.Limits.cospanExt_app_left

@[simp]
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := by
  dsimp [cospanExt]
#align category_theory.limits.cospan_ext_app_right CategoryTheory.Limits.cospanExt_app_right

@[simp]
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := by
  dsimp [cospanExt]
#align category_theory.limits.cospan_ext_app_one CategoryTheory.Limits.cospanExt_app_one

@[simp]
theorem cospanExt_hom_app_left :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom := by dsimp [cospanExt]
#align category_theory.limits.cospan_ext_hom_app_left CategoryTheory.Limits.cospanExt_hom_app_left

@[simp]
theorem cospanExt_hom_app_right :
    (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom := by dsimp [cospanExt]
#align category_theory.limits.cospan_ext_hom_app_right CategoryTheory.Limits.cospanExt_hom_app_right

@[simp]
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := by
  dsimp [cospanExt]
#align category_theory.limits.cospan_ext_hom_app_one CategoryTheory.Limits.cospanExt_hom_app_one

@[simp]
theorem cospanExt_inv_app_left :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv := by dsimp [cospanExt]
#align category_theory.limits.cospan_ext_inv_app_left CategoryTheory.Limits.cospanExt_inv_app_left

@[simp]
theorem cospanExt_inv_app_right :
    (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv := by dsimp [cospanExt]
#align category_theory.limits.cospan_ext_inv_app_right CategoryTheory.Limits.cospanExt_inv_app_right

@[simp]
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  dsimp [cospanExt]
#align category_theory.limits.cospan_ext_inv_app_one CategoryTheory.Limits.cospanExt_inv_app_one

end

section

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩); exacts [iX, iY, iZ])
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])
#align category_theory.limits.span_ext CategoryTheory.Limits.spanExt

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_app_left CategoryTheory.Limits.spanExt_app_left

@[simp]
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_app_right CategoryTheory.Limits.spanExt_app_right

@[simp]
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_app_one CategoryTheory.Limits.spanExt_app_one

@[simp]
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_hom_app_left CategoryTheory.Limits.spanExt_hom_app_left

@[simp]
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_hom_app_right CategoryTheory.Limits.spanExt_hom_app_right

@[simp]
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_hom_app_zero CategoryTheory.Limits.spanExt_hom_app_zero

@[simp]
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_inv_app_left CategoryTheory.Limits.spanExt_inv_app_left

@[simp]
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_inv_app_right CategoryTheory.Limits.spanExt_inv_app_right

@[simp]
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := by
  dsimp [spanExt]
#align category_theory.limits.span_ext_inv_app_zero CategoryTheory.Limits.spanExt_inv_app_zero

end

end

end CategoryTheory.Limits
