/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Pullbacks

We define a category `WalkingCospan` (resp. `WalkingSpan`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/


noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe w v₁ v₂ v u u₂

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

instance (X Y : WalkingCospan) : Subsingleton (X ⟶ Y) := by constructor; intros; simp
                                                            -- ⊢ ∀ (a b : X ⟶ Y), a = b
                                                                         -- ⊢ a✝ = b✝
                                                                                 -- 🎉 no goals

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

instance (X Y : WalkingSpan) : Subsingleton (X ⟶ Y) := by constructor; intros a b; simp
                                                          -- ⊢ ∀ (a b : X ⟶ Y), a = b
                                                                       -- ⊢ a = b
                                                                                   -- 🎉 no goals

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
  -- ⊢ ∀ (j : WalkingCospan), NatTrans.app s.π j = i.hom ≫ NatTrans.app t.π j
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.π.naturality WalkingCospan.Hom.inl
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    dsimp at h₁
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    simp only [Category.id_comp] at h₁
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    have h₂ := t.π.naturality WalkingCospan.Hom.inl
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    dsimp at h₂
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    simp only [Category.id_comp] at h₂
    -- ⊢ NatTrans.app s.π none = i.hom ≫ NatTrans.app t.π none
    simp_rw [h₂, ← Category.assoc, ← w₁, ← h₁]
    -- 🎉 no goals
  · exact w₁
    -- 🎉 no goals
  · exact w₂
    -- 🎉 no goals
#align category_theory.limits.walking_cospan.ext CategoryTheory.Limits.WalkingCospan.ext

/-- To construct an isomorphism of cocones over the walking span,
it suffices to construct an isomorphism
of the cocone points and check it commutes with the legs from `left` and `right`. -/
def WalkingSpan.ext {F : WalkingSpan ⥤ C} {s t : Cocone F} (i : s.pt ≅ t.pt)
    (w₁ : s.ι.app WalkingCospan.left ≫ i.hom = t.ι.app WalkingCospan.left)
    (w₂ : s.ι.app WalkingCospan.right ≫ i.hom = t.ι.app WalkingCospan.right) : s ≅ t := by
  apply Cocones.ext i _
  -- ⊢ ∀ (j : WalkingSpan), NatTrans.app s.ι j ≫ i.hom = NatTrans.app t.ι j
  rintro (⟨⟩ | ⟨⟨⟩⟩)
  · have h₁ := s.ι.naturality WalkingSpan.Hom.fst
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    dsimp at h₁
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    simp only [Category.comp_id] at h₁
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    have h₂ := t.ι.naturality WalkingSpan.Hom.fst
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    dsimp at h₂
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    simp only [Category.comp_id] at h₂
    -- ⊢ NatTrans.app s.ι none ≫ i.hom = NatTrans.app t.ι none
    simp_rw [← h₁, Category.assoc, w₁, h₂]
    -- 🎉 no goals
  · exact w₁
    -- 🎉 no goals
  · exact w₂
    -- 🎉 no goals
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
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
                                           -- ⊢ F.map (WidePullbackShape.Hom.id none) ≫ ((fun j => eqToIso (_ : F.obj j = (c …
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- ⊢ F.map (term WalkingPair.left) ≫ ((fun j => eqToIso (_ : F.obj j = (cospan (F …
                                           -- ⊢ F.map (WidePullbackShape.Hom.id (some WalkingPair.left)) ≫ ((fun j => eqToIs …
                                           -- 🎉 no goals
                                           -- ⊢ F.map (term WalkingPair.right) ≫ ((fun j => eqToIso (_ : F.obj j = (cospan ( …
                                           -- 🎉 no goals
                                           -- ⊢ F.map (WidePullbackShape.Hom.id (some WalkingPair.right)) ≫ ((fun j => eqToI …
                                                       -- ⊢ F.map (𝟙 none) ≫ 𝟙 (F.obj none) = 𝟙 (F.obj none) ≫ (cospan (F.map inl) (F.ma …
                                                       -- ⊢ F.map (term WalkingPair.left) ≫ 𝟙 (F.obj none) = 𝟙 (F.obj (some WalkingPair. …
                                                       -- ⊢ F.map (𝟙 (some WalkingPair.left)) ≫ 𝟙 (F.obj (some WalkingPair.left)) = 𝟙 (F …
                                                       -- ⊢ F.map (term WalkingPair.right) ≫ 𝟙 (F.obj none) = 𝟙 (F.obj (some WalkingPair …
                                                       -- ⊢ F.map (𝟙 (some WalkingPair.right)) ≫ 𝟙 (F.obj (some WalkingPair.right)) = 𝟙  …
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align category_theory.limits.diagram_iso_cospan CategoryTheory.Limits.diagramIsoCospan

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
-- @[simps (config := { rhsMd := semireducible })]  Porting note: no semireducible
@[simps!]
def diagramIsoSpan (F : WalkingSpan ⥤ C) : F ≅ span (F.map fst) (F.map snd) :=
  NatIso.ofComponents
  (fun j => eqToIso (by rcases j with (⟨⟩ | ⟨⟨⟩⟩) <;> rfl))
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
                                           -- ⊢ F.map (WidePushoutShape.Hom.id none) ≫ ((fun j => eqToIso (_ : F.obj j = (sp …
                                           -- ⊢ F.map (init WalkingPair.left) ≫ ((fun j => eqToIso (_ : F.obj j = (span (F.m …
                                           -- ⊢ F.map (init WalkingPair.right) ≫ ((fun j => eqToIso (_ : F.obj j = (span (F. …
                                           -- 🎉 no goals
                                           -- ⊢ F.map (WidePushoutShape.Hom.id (some WalkingPair.left)) ≫ ((fun j => eqToIso …
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- 🎉 no goals
                                           -- ⊢ F.map (WidePushoutShape.Hom.id (some WalkingPair.right)) ≫ ((fun j => eqToIs …
                                                       -- ⊢ F.map (𝟙 none) ≫ 𝟙 (F.obj none) = 𝟙 (F.obj none) ≫ (span (F.map fst) (F.map  …
                                                       -- ⊢ F.map (init WalkingPair.left) ≫ 𝟙 (F.obj (some WalkingPair.left)) = 𝟙 (F.obj …
                                                       -- ⊢ F.map (init WalkingPair.right) ≫ 𝟙 (F.obj (some WalkingPair.right)) = 𝟙 (F.o …
                                                       -- ⊢ F.map (𝟙 (some WalkingPair.left)) ≫ 𝟙 (F.obj (some WalkingPair.left)) = 𝟙 (F …
                                                       -- ⊢ F.map (𝟙 (some WalkingPair.right)) ≫ 𝟙 (F.obj (some WalkingPair.right)) = 𝟙  …
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align category_theory.limits.diagram_iso_span CategoryTheory.Limits.diagramIsoSpan

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor applied to a cospan is a cospan. -/
def cospanCompIso (F : C ⥤ D) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    cospan f g ⋙ F ≅ cospan (F.map f) (F.map g) :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩) <;> exact Iso.refl _)
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
                                             -- ⊢ (cospan f g ⋙ F).map (WidePullbackShape.Hom.id none) ≫ (Option.casesOn none  …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g ⋙ F).map (term WalkingPair.left) ≫ (Option.casesOn none (Iso.ref …
                                             -- ⊢ (cospan f g ⋙ F).map (WidePullbackShape.Hom.id (some WalkingPair.left)) ≫ (O …
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g ⋙ F).map (term WalkingPair.right) ≫ (Option.casesOn none (Iso.re …
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g ⋙ F).map (WidePullbackShape.Hom.id (some WalkingPair.right)) ≫ ( …
                                                         -- ⊢ F.map ((cospan f g).map (𝟙 none)) ≫ 𝟙 (F.obj Z) = 𝟙 (F.obj Z) ≫ (cospan (F.m …
                                                         -- ⊢ F.map f ≫ 𝟙 (F.obj Z) = 𝟙 (F.obj X) ≫ F.map f
                                                         -- ⊢ F.map ((cospan f g).map (𝟙 (some WalkingPair.left))) ≫ 𝟙 (F.obj X) = 𝟙 (F.ob …
                                                         -- ⊢ F.map g ≫ 𝟙 (F.obj Z) = 𝟙 (F.obj Y) ≫ F.map g
                                                         -- ⊢ F.map ((cospan f g).map (𝟙 (some WalkingPair.right))) ≫ 𝟙 (F.obj Y) = 𝟙 (F.o …
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
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
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp)
                                             -- ⊢ (span f g ⋙ F).map (WidePushoutShape.Hom.id none) ≫ (Option.casesOn none (Is …
                                             -- ⊢ (span f g ⋙ F).map (init WalkingPair.left) ≫ (Option.casesOn (some WalkingPa …
                                             -- ⊢ (span f g ⋙ F).map (init WalkingPair.right) ≫ (Option.casesOn (some WalkingP …
                                             -- 🎉 no goals
                                             -- ⊢ (span f g ⋙ F).map (WidePushoutShape.Hom.id (some WalkingPair.left)) ≫ (Opti …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ (span f g ⋙ F).map (WidePushoutShape.Hom.id (some WalkingPair.right)) ≫ (Opt …
                                                         -- ⊢ F.map ((span f g).map (𝟙 none)) ≫ 𝟙 (F.obj X) = 𝟙 (F.obj X) ≫ (span (F.map f …
                                                         -- ⊢ F.map f ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map f
                                                         -- ⊢ F.map g ≫ 𝟙 (F.obj Z) = 𝟙 (F.obj X) ≫ F.map g
                                                         -- ⊢ F.map ((span f g).map (𝟙 (some WalkingPair.left))) ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj  …
                                                         -- ⊢ F.map ((span f g).map (𝟙 (some WalkingPair.right))) ≫ 𝟙 (F.obj Z) = 𝟙 (F.obj …
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
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
                            -- 🎉 no goals
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])
                                             -- ⊢ (cospan f g).map (WidePullbackShape.Hom.id none) ≫ (Option.casesOn none iZ f …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g).map (term WalkingPair.left) ≫ (Option.casesOn none iZ fun val = …
                                             -- ⊢ (cospan f g).map (WidePullbackShape.Hom.id (some WalkingPair.left)) ≫ (Optio …
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g).map (term WalkingPair.right) ≫ (Option.casesOn none iZ fun val  …
                                             -- 🎉 no goals
                                             -- ⊢ (cospan f g).map (WidePullbackShape.Hom.id (some WalkingPair.right)) ≫ (Opti …
                                                         -- ⊢ (cospan f g).map (𝟙 none) ≫ iZ.hom = iZ.hom ≫ (cospan f' g').map (𝟙 none)
                                                         -- ⊢ f ≫ iZ.hom = iX.hom ≫ f'
                                                         -- ⊢ (cospan f g).map (𝟙 (some WalkingPair.left)) ≫ iX.hom = iX.hom ≫ (cospan f'  …
                                                         -- ⊢ g ≫ iZ.hom = iY.hom ≫ g'
                                                         -- ⊢ (cospan f g).map (𝟙 (some WalkingPair.right)) ≫ iY.hom = iY.hom ≫ (cospan f' …
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align category_theory.limits.cospan_ext CategoryTheory.Limits.cospanExt

variable (wf : iX.hom ≫ f' = f ≫ iZ.hom) (wg : iY.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem cospanExt_app_left : (cospanExt iX iY iZ wf wg).app WalkingCospan.left = iX := by
  dsimp [cospanExt]
  -- 🎉 no goals
#align category_theory.limits.cospan_ext_app_left CategoryTheory.Limits.cospanExt_app_left

@[simp]
theorem cospanExt_app_right : (cospanExt iX iY iZ wf wg).app WalkingCospan.right = iY := by
  dsimp [cospanExt]
  -- 🎉 no goals
#align category_theory.limits.cospan_ext_app_right CategoryTheory.Limits.cospanExt_app_right

@[simp]
theorem cospanExt_app_one : (cospanExt iX iY iZ wf wg).app WalkingCospan.one = iZ := by
  dsimp [cospanExt]
  -- 🎉 no goals
#align category_theory.limits.cospan_ext_app_one CategoryTheory.Limits.cospanExt_app_one

@[simp]
theorem cospanExt_hom_app_left : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.left = iX.hom :=
  by dsimp [cospanExt]
     -- 🎉 no goals
#align category_theory.limits.cospan_ext_hom_app_left CategoryTheory.Limits.cospanExt_hom_app_left

@[simp]
theorem cospanExt_hom_app_right : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.right = iY.hom :=
  by dsimp [cospanExt]
     -- 🎉 no goals
#align category_theory.limits.cospan_ext_hom_app_right CategoryTheory.Limits.cospanExt_hom_app_right

@[simp]
theorem cospanExt_hom_app_one : (cospanExt iX iY iZ wf wg).hom.app WalkingCospan.one = iZ.hom := by
  dsimp [cospanExt]
  -- 🎉 no goals
#align category_theory.limits.cospan_ext_hom_app_one CategoryTheory.Limits.cospanExt_hom_app_one

@[simp]
theorem cospanExt_inv_app_left : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.left = iX.inv :=
  by dsimp [cospanExt]
     -- 🎉 no goals
#align category_theory.limits.cospan_ext_inv_app_left CategoryTheory.Limits.cospanExt_inv_app_left

@[simp]
theorem cospanExt_inv_app_right : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.right = iY.inv :=
  by dsimp [cospanExt]
     -- 🎉 no goals
#align category_theory.limits.cospan_ext_inv_app_right CategoryTheory.Limits.cospanExt_inv_app_right

@[simp]
theorem cospanExt_inv_app_one : (cospanExt iX iY iZ wf wg).inv.app WalkingCospan.one = iZ.inv := by
  dsimp [cospanExt]
  -- 🎉 no goals
#align category_theory.limits.cospan_ext_inv_app_one CategoryTheory.Limits.cospanExt_inv_app_one

end

section

variable {f : X ⟶ Y} {g : X ⟶ Z} {f' : X' ⟶ Y'} {g' : X' ⟶ Z'}

/-- Construct an isomorphism of spans from components. -/
def spanExt (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom) :
    span f g ≅ span f' g' :=
  NatIso.ofComponents (by rintro (⟨⟩ | ⟨⟨⟩⟩); exacts [iX, iY, iZ])
                                              -- 🎉 no goals
    (by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) f <;> cases f <;> dsimp <;> simp [wf, wg])
                                             -- ⊢ (span f g).map (WidePushoutShape.Hom.id none) ≫ (Option.casesOn none iX fun  …
                                             -- ⊢ (span f g).map (init WalkingPair.left) ≫ (Option.casesOn (some WalkingPair.l …
                                             -- ⊢ (span f g).map (init WalkingPair.right) ≫ (Option.casesOn (some WalkingPair. …
                                             -- 🎉 no goals
                                             -- ⊢ (span f g).map (WidePushoutShape.Hom.id (some WalkingPair.left)) ≫ (Option.c …
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ (span f g).map (WidePushoutShape.Hom.id (some WalkingPair.right)) ≫ (Option. …
                                                         -- ⊢ (span f g).map (𝟙 none) ≫ iX.hom = iX.hom ≫ (span f' g').map (𝟙 none)
                                                         -- ⊢ f ≫ iY.hom = iX.hom ≫ f'
                                                         -- ⊢ g ≫ iZ.hom = iX.hom ≫ g'
                                                         -- ⊢ (span f g).map (𝟙 (some WalkingPair.left)) ≫ iY.hom = iY.hom ≫ (span f' g'). …
                                                         -- ⊢ (span f g).map (𝟙 (some WalkingPair.right)) ≫ iZ.hom = iZ.hom ≫ (span f' g') …
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
                                                                   -- 🎉 no goals
#align category_theory.limits.span_ext CategoryTheory.Limits.spanExt

variable (wf : iX.hom ≫ f' = f ≫ iY.hom) (wg : iX.hom ≫ g' = g ≫ iZ.hom)

@[simp]
theorem spanExt_app_left : (spanExt iX iY iZ wf wg).app WalkingSpan.left = iY := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_app_left CategoryTheory.Limits.spanExt_app_left

@[simp]
theorem spanExt_app_right : (spanExt iX iY iZ wf wg).app WalkingSpan.right = iZ := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_app_right CategoryTheory.Limits.spanExt_app_right

@[simp]
theorem spanExt_app_one : (spanExt iX iY iZ wf wg).app WalkingSpan.zero = iX := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_app_one CategoryTheory.Limits.spanExt_app_one

@[simp]
theorem spanExt_hom_app_left : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.left = iY.hom := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_hom_app_left CategoryTheory.Limits.spanExt_hom_app_left

@[simp]
theorem spanExt_hom_app_right : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.right = iZ.hom := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_hom_app_right CategoryTheory.Limits.spanExt_hom_app_right

@[simp]
theorem spanExt_hom_app_zero : (spanExt iX iY iZ wf wg).hom.app WalkingSpan.zero = iX.hom := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_hom_app_zero CategoryTheory.Limits.spanExt_hom_app_zero

@[simp]
theorem spanExt_inv_app_left : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.left = iY.inv := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_inv_app_left CategoryTheory.Limits.spanExt_inv_app_left

@[simp]
theorem spanExt_inv_app_right : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.right = iZ.inv := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_inv_app_right CategoryTheory.Limits.spanExt_inv_app_right

@[simp]
theorem spanExt_inv_app_zero : (spanExt iX iY iZ wf wg).inv.app WalkingSpan.zero = iX.inv := by
  dsimp [spanExt]
  -- 🎉 no goals
#align category_theory.limits.span_ext_inv_app_zero CategoryTheory.Limits.spanExt_inv_app_zero

end

end

variable {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)
#align category_theory.limits.pullback_cone CategoryTheory.Limits.PullbackCone

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left
#align category_theory.limits.pullback_cone.fst CategoryTheory.Limits.PullbackCone.fst

/-- The second projection of a pullback cone. -/
abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right
#align category_theory.limits.pullback_cone.snd CategoryTheory.Limits.PullbackCone.snd

@[simp]
theorem π_app_left (c : PullbackCone f g) : c.π.app WalkingCospan.left = c.fst := rfl
#align category_theory.limits.pullback_cone.π_app_left CategoryTheory.Limits.PullbackCone.π_app_left

@[simp]
theorem π_app_right (c : PullbackCone f g) : c.π.app WalkingCospan.right = c.snd := rfl
#align category_theory.limits.pullback_cone.π_app_right CategoryTheory.Limits.PullbackCone.π_app_right

@[simp]
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f := by
  have w := t.π.naturality WalkingCospan.Hom.inl
  -- ⊢ NatTrans.app t.π WalkingCospan.one = fst t ≫ f
  dsimp at w; simpa using w
  -- ⊢ NatTrans.app t.π WalkingCospan.one = fst t ≫ f
              -- 🎉 no goals
#align category_theory.limits.pullback_cone.condition_one CategoryTheory.Limits.PullbackCone.condition_one

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def isLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.pt ⟶ t.pt)
      (_ : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl, ← t.w inl, ← Category.assoc]
        -- ⊢ (lift s ≫ NatTrans.app t.π WalkingCospan.left) ≫ (cospan f g).map inl = NatT …
        congr
        -- ⊢ lift s ≫ NatTrans.app t.π WalkingCospan.left = NatTrans.app s.π WalkingCospa …
        exact fac_left s)
        -- 🎉 no goals
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }
#align category_theory.limits.pullback_cone.is_limit_aux CategoryTheory.Limits.PullbackCone.isLimitAux

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pullback_cone.is_limit_aux' CategoryTheory.Limits.PullbackCone.isLimitAux'

/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simps]
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : PullbackCone f g where
  pt := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> dsimp <;> simp [eq] }
                                                               -- ⊢ ((Functor.const WalkingCospan).obj W).map (WidePullbackShape.Hom.id none) ≫  …
                                                               -- 🎉 no goals
                                                               -- 🎉 no goals
                                                               -- ⊢ ((Functor.const WalkingCospan).obj W).map (term WalkingPair.left) ≫ (fun j = …
                                                               -- ⊢ ((Functor.const WalkingCospan).obj W).map (WidePullbackShape.Hom.id (some Wa …
                                                               -- 🎉 no goals
                                                               -- ⊢ ((Functor.const WalkingCospan).obj W).map (term WalkingPair.right) ≫ (fun j  …
                                                               -- 🎉 no goals
                                                               -- ⊢ ((Functor.const WalkingCospan).obj W).map (WidePullbackShape.Hom.id (some Wa …
                                                                           -- ⊢ 𝟙 W ≫ fst ≫ f = (fst ≫ f) ≫ (cospan f g).map (𝟙 none)
                                                                           -- ⊢ 𝟙 W ≫ fst ≫ f = fst ≫ f
                                                                           -- ⊢ 𝟙 W ≫ fst = fst ≫ (cospan f g).map (𝟙 (some WalkingPair.left))
                                                                           -- ⊢ 𝟙 W ≫ fst ≫ f = snd ≫ g
                                                                           -- ⊢ 𝟙 W ≫ snd = snd ≫ (cospan f g).map (𝟙 (some WalkingPair.right))
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
                                                                                     -- 🎉 no goals
#align category_theory.limits.pullback_cone.mk CategoryTheory.Limits.PullbackCone.mk

@[simp]
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.left = fst := rfl
#align category_theory.limits.pullback_cone.mk_π_app_left CategoryTheory.Limits.PullbackCone.mk_π_app_left

@[simp]
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.right = snd := rfl
#align category_theory.limits.pullback_cone.mk_π_app_right CategoryTheory.Limits.PullbackCone.mk_π_app_right

@[simp]
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.one = fst ≫ f := rfl
#align category_theory.limits.pullback_cone.mk_π_app_one CategoryTheory.Limits.PullbackCone.mk_π_app_one

@[simp]
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).fst = fst := rfl
#align category_theory.limits.pullback_cone.mk_fst CategoryTheory.Limits.PullbackCone.mk_fst

@[simp]
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).snd = snd := rfl
#align category_theory.limits.pullback_cone.mk_snd CategoryTheory.Limits.PullbackCone.mk_snd

@[reassoc]
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm
#align category_theory.limits.pullback_cone.condition CategoryTheory.Limits.PullbackCone.condition

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w inl]; dsimp [h₀]; simp only [← Category.assoc, congrArg (· ≫ f) h₀]
               -- ⊢ k ≫ NatTrans.app t.π WalkingCospan.left ≫ (cospan f g).map inl = l ≫ NatTran …
                               -- ⊢ k ≫ fst t ≫ f = l ≫ fst t ≫ f
                                           -- 🎉 no goals
#align category_theory.limits.pullback_cone.equalizer_ext CategoryTheory.Limits.PullbackCone.equalizer_ext

theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
    (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext <| equalizer_ext _ h₀ h₁
#align category_theory.limits.pullback_cone.is_limit.hom_ext CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext

theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  -- ⊢ h ≫ fst t = k ≫ fst t
  rw [← cancel_mono f, Category.assoc, Category.assoc, condition]
  -- ⊢ h ≫ snd t ≫ g = k ≫ snd t ≫ g
  have := congrArg (· ≫ g) i; dsimp at this
  -- ⊢ h ≫ snd t ≫ g = k ≫ snd t ≫ g
                              -- ⊢ h ≫ snd t ≫ g = k ≫ snd t ≫ g
  rwa [Category.assoc, Category.assoc] at this
  -- 🎉 no goals
#align category_theory.limits.pullback_cone.mono_snd_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono

theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  -- ⊢ h ≫ snd t = k ≫ snd t
  rw [← cancel_mono g, Category.assoc, Category.assoc, ←condition]
  -- ⊢ h ≫ fst t ≫ f = k ≫ fst t ≫ f
  have := congrArg (· ≫ f) i; dsimp at this
  -- ⊢ h ≫ fst t ≫ f = k ≫ fst t ≫ f
                              -- ⊢ h ≫ fst t ≫ f = k ≫ fst t ≫ f
  rwa [Category.assoc, Category.assoc] at this
  -- 🎉 no goals
#align category_theory.limits.pullback_cone.mono_fst_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono

/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst)
    (w₂ : s.snd = i.hom ≫ t.snd) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂
#align category_theory.limits.pullback_cone.ext CategoryTheory.Limits.PullbackCone.ext

-- porting note: `IsLimit.lift` and the two following simp lemmas were introduced to ease the port
/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
    and `l ≫ snd t = k`, see `IsLimit.lift_fst` and `IsLimit.lift_snd`. -/
def IsLimit.lift {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
lemma IsLimit.lift_fst {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ fst t = h := ht.fac _ _

@[reassoc (attr := simp)]
lemma IsLimit.lift_snd {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ snd t = k := ht.fac _ _

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ t.pt // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨IsLimit.lift ht h k w, by simp⟩
                             -- 🎉 no goals
#align category_theory.limits.pullback_cone.is_limit.lift' CategoryTheory.Limits.PullbackCone.IsLimit.lift'

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a limit cone.
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : PullbackCone f g) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (mk fst snd eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pullback_cone.is_limit.mk CategoryTheory.Limits.PullbackCone.IsLimit.mk

/-- The flip of a pullback square is a pullback square. -/
def flipIsLimit {W : C} {h : W ⟶ X} {k : W ⟶ Y} {comm : h ≫ f = k ≫ g}
    (t : IsLimit (mk _ _ comm.symm)) : IsLimit (mk _ _ comm) :=
  isLimitAux' _ fun s => by
    refine'
      ⟨(IsLimit.lift' t _ _ s.condition.symm).1, (IsLimit.lift' t _ _ _).2.2,
        (IsLimit.lift' t _ _ _).2.1, fun m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).equalizer_ext
    -- ⊢ m✝ ≫ fst (mk k h (_ : k ≫ g = h ≫ f)) = ↑(IsLimit.lift' t (snd s) (fst s) (_ …
    · rwa [(IsLimit.lift' t _ _ _).2.1]
      -- 🎉 no goals
    · rwa [(IsLimit.lift' t _ _ _).2.2]
      -- 🎉 no goals
#align category_theory.limits.pullback_cone.flip_is_limit CategoryTheory.Limits.PullbackCone.flipIsLimit

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
                 -- 🎉 no goals
    simpa using m₁
    -- 🎉 no goals
#align category_theory.limits.pullback_cone.is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.isLimitMkIdId

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `PullbackCone.is_id_of_mono`.
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    -- ⊢ val✝ ≫ fst (mk (𝟙 X) (𝟙 X) (_ : 𝟙 X ≫ f = 𝟙 X ≫ f)) = val✝ ≫ snd (mk (𝟙 X) ( …
    rfl⟩
    -- 🎉 no goals
#align category_theory.limits.pullback_cone.mono_of_is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId

/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by simp only [Category.assoc, hxh, hyh, s.condition])) :=
                                  -- 🎉 no goals
  PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by  -- Porting note: reassoc workaround
      rw [← Category.assoc, ← Category.assoc]
      -- ⊢ (fst t ≫ x) ≫ h = (snd t ≫ y) ≫ h
      apply congrArg (· ≫ h) t.condition
      -- 🎉 no goals
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
                                                -- 🎉 no goals
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun hr hr' => by
        apply PullbackCone.IsLimit.hom_ext hs <;>
        -- ⊢ m✝ ≫ fst s = Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd …
              simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hr hr' ⊢ <;>
              -- ⊢ m✝ ≫ fst s = Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd …
              -- ⊢ m✝ ≫ snd s = Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd …
            simp only [hr, hr'] <;>
            -- ⊢ fst t = Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd t ≫  …
            -- ⊢ snd t = Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd t ≫  …
          symm
          -- ⊢ Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd t ≫ g)) ≫ fs …
          -- ⊢ Limits.IsLimit.lift hs (mk (fst t) (snd t) (_ : fst t ≫ f = snd t ≫ g)) ≫ sn …
        exacts [hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right]⟩⟩
        -- 🎉 no goals
#align category_theory.limits.pullback_cone.is_limit_of_factors CategoryTheory.Limits.PullbackCone.isLimitOfFactors

/-- If `W` is the pullback of `f, g`,
it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← Category.assoc, ← Category.assoc, s.condition])) := by
          -- 🎉 no goals
  apply PullbackCone.isLimitAux'
  -- ⊢ (s_1 : PullbackCone (f ≫ i) (g ≫ i)) → { l // l ≫ fst (mk (fst s) (snd s) (_ …
  intro s
  -- ⊢ { l // l ≫ fst (mk (fst s✝) (snd s✝) (_ : fst s✝ ≫ f ≫ i = snd s✝ ≫ g ≫ i))  …
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  -- ⊢ ∀ {m : s.pt ⟶ (mk (fst s✝) (snd s✝) (_ : fst s✝ ≫ f ≫ i = snd s✝ ≫ g ≫ i)).p …
  intro m hm₁ hm₂
  -- ⊢ m = l
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
  -- 🎉 no goals
#align category_theory.limits.pullback_cone.is_limit_of_comp_mono CategoryTheory.Limits.PullbackCone.isLimitOfCompMono

end PullbackCone

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)
#align category_theory.limits.pushout_cocone CategoryTheory.Limits.PushoutCocone

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.pt :=
  t.ι.app WalkingSpan.left
#align category_theory.limits.pushout_cocone.inl CategoryTheory.Limits.PushoutCocone.inl

/-- The second inclusion of a pushout cocone. -/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
  t.ι.app WalkingSpan.right
#align category_theory.limits.pushout_cocone.inr CategoryTheory.Limits.PushoutCocone.inr

@[simp]
theorem ι_app_left (c : PushoutCocone f g) : c.ι.app WalkingSpan.left = c.inl := rfl
#align category_theory.limits.pushout_cocone.ι_app_left CategoryTheory.Limits.PushoutCocone.ι_app_left

@[simp]
theorem ι_app_right (c : PushoutCocone f g) : c.ι.app WalkingSpan.right = c.inr := rfl
#align category_theory.limits.pushout_cocone.ι_app_right CategoryTheory.Limits.PushoutCocone.ι_app_right

@[simp]
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl := by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  -- ⊢ NatTrans.app t.ι WalkingSpan.zero = f ≫ inl t
  dsimp at w; simpa using w.symm
  -- ⊢ NatTrans.app t.ι WalkingSpan.zero = f ≫ inl t
              -- 🎉 no goals
#align category_theory.limits.pushout_cocone.condition_zero CategoryTheory.Limits.PushoutCocone.condition_zero

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : PushoutCocone f g) (desc : ∀ s : PushoutCocone f g, t.pt ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : t.pt ⟶ s.pt)
    (_ : ∀ j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
                           -- 🎉 no goals
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }
#align category_theory.limits.pushout_cocone.is_colimit_aux CategoryTheory.Limits.PushoutCocone.isColimitAux

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      ∀ s : PushoutCocone f g,
        { l //
          t.inl ≫ l = s.inl ∧
            t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pushout_cocone.is_colimit_aux' CategoryTheory.Limits.PushoutCocone.isColimitAux'

/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
@[simps]
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g where
  pt := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩|⟨⟨⟩⟩) (⟨⟩|⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                         -- ⊢ (span f✝ g).map f ≫ (fun j => Option.casesOn j (f✝ ≫ inl) fun j' => WalkingP …
                                                     -- ⊢ (span f g).map (WidePushoutShape.Hom.id none) ≫ (fun j => Option.casesOn j ( …
                                                     -- ⊢ (span f g).map (init WalkingPair.left) ≫ (fun j => Option.casesOn j (f ≫ inl …
                                                     -- ⊢ (span f g).map (init WalkingPair.right) ≫ (fun j => Option.casesOn j (f ≫ in …
                                                     -- 🎉 no goals
                                                     -- ⊢ (span f g).map (WidePushoutShape.Hom.id (some WalkingPair.left)) ≫ (fun j => …
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- 🎉 no goals
                                                     -- ⊢ (span f g).map (WidePushoutShape.Hom.id (some WalkingPair.right)) ≫ (fun j = …
                                                                 -- ⊢ (span f g).map (𝟙 none) ≫ f ≫ inl = (f ≫ inl) ≫ 𝟙 W
                                                                 -- ⊢ f ≫ inl = (f ≫ inl) ≫ 𝟙 W
                                                                 -- ⊢ g ≫ inr = (f ≫ inl) ≫ 𝟙 W
                                                                 -- ⊢ (span f g).map (𝟙 (some WalkingPair.left)) ≫ inl = inl ≫ 𝟙 W
                                                                 -- ⊢ (span f g).map (𝟙 (some WalkingPair.right)) ≫ inr = inr ≫ 𝟙 W
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
                                                                           -- 🎉 no goals
#align category_theory.limits.pushout_cocone.mk CategoryTheory.Limits.PushoutCocone.mk

@[simp]
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.left = inl := rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_left CategoryTheory.Limits.PushoutCocone.mk_ι_app_left

@[simp]
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.right = inr := rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_right CategoryTheory.Limits.PushoutCocone.mk_ι_app_right

@[simp]
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.zero = f ≫ inl := rfl
#align category_theory.limits.pushout_cocone.mk_ι_app_zero CategoryTheory.Limits.PushoutCocone.mk_ι_app_zero

@[simp]
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inl = inl := rfl
#align category_theory.limits.pushout_cocone.mk_inl CategoryTheory.Limits.PushoutCocone.mk_inl

@[simp]
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inr = inr := rfl
#align category_theory.limits.pushout_cocone.mk_inr CategoryTheory.Limits.PushoutCocone.mk_inr

@[reassoc]
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm
#align category_theory.limits.pushout_cocone.condition CategoryTheory.Limits.PushoutCocone.condition

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
    ∀ j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w fst, Category.assoc, Category.assoc, h₀]
               -- 🎉 no goals
#align category_theory.limits.pushout_cocone.coequalizer_ext CategoryTheory.Limits.PushoutCocone.coequalizer_ext

theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext <| coequalizer_ext _ h₀ h₁
#align category_theory.limits.pushout_cocone.is_colimit.hom_ext CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext

-- porting note: `IsColimit.desc` and the two following simp lemmas were introduced to ease the port
/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`, see `IsColimit.inl_desc` and `IsColimit.inr_desc`-/
def IsColimit.desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : t.pt ⟶ W :=
  ht.desc (PushoutCocone.mk _ _ w)

@[reassoc (attr := simp)]
lemma IsColimit.inl_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inl t ≫ IsColimit.desc ht h k w = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
lemma IsColimit.inr_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inr t ≫ IsColimit.desc ht h k w = k :=
  ht.fac _ _

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : t.pt ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨IsColimit.desc ht h k w, by simp⟩
                               -- 🎉 no goals
#align category_theory.limits.pushout_cocone.is_colimit.desc' CategoryTheory.Limits.PushoutCocone.IsColimit.desc'

theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩
                                             -- 🎉 no goals
#align category_theory.limits.pushout_cocone.epi_inr_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi

theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩
                                               -- 🎉 no goals
#align category_theory.limits.pushout_cocone.epi_inl_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi

/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl)
    (w₂ : s.inr ≫ i.hom = t.inr) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂
#align category_theory.limits.pushout_cocone.ext CategoryTheory.Limits.PushoutCocone.ext

/-- This is a more convenient formulation to show that a `PushoutCocone` constructed using
`PushoutCocone.mk` is a colimit cocone.
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
    (desc : ∀ s : PushoutCocone f g, W ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : PushoutCocone f g) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (mk inl inr eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
#align category_theory.limits.pushout_cocone.is_colimit.mk CategoryTheory.Limits.PushoutCocone.IsColimit.mk

/-- The flip of a pushout square is a pushout square. -/
def flipIsColimit {W : C} {h : Y ⟶ W} {k : Z ⟶ W} {comm : f ≫ h = g ≫ k}
    (t : IsColimit (mk _ _ comm.symm)) : IsColimit (mk _ _ comm) :=
  isColimitAux' _ fun s => by
    refine'
      ⟨(IsColimit.desc' t _ _ s.condition.symm).1, (IsColimit.desc' t _ _ _).2.2,
        (IsColimit.desc' t _ _ _).2.1, fun m₁ m₂ => t.hom_ext _⟩
    apply (mk k h _).coequalizer_ext
    -- ⊢ inl (mk k h (_ : g ≫ k = f ≫ h)) ≫ m✝ = inl (mk k h (_ : g ≫ k = f ≫ h)) ≫ ↑ …
    · rwa [(IsColimit.desc' t _ _ _).2.1]
      -- 🎉 no goals
    · rwa [(IsColimit.desc' t _ _ _).2.2]
      -- 🎉 no goals
#align category_theory.limits.pushout_cocone.flip_is_colimit CategoryTheory.Limits.PushoutCocone.flipIsColimit

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_isColimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun s => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
                 -- 🎉 no goals
    simpa using m₁
    -- 🎉 no goals
#align category_theory.limits.pushout_cocone.is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.isColimitMkIdId

/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `PushoutCocone.isColimitMkIdId`.
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    -- ⊢ inl (mk (𝟙 Y) (𝟙 Y) (_ : f ≫ 𝟙 Y = f ≫ 𝟙 Y)) ≫ val✝ = inr (mk (𝟙 Y) (𝟙 Y) (_ …
    rfl⟩
    -- 🎉 no goals
#align category_theory.limits.pushout_cocone.epi_of_is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.epi_of_isColimitMkIdId

/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
    (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    have reassoc₁ : h ≫ x ≫ inl s = f ≫ inl s := by  -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
      -- ⊢ (h ≫ x) ≫ inl s = f ≫ inl s
                             -- 🎉 no goals
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
      -- ⊢ (h ≫ y) ≫ inr s = g ≫ inr s
                             -- 🎉 no goals
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
          (cancel_epi h).1 <| by rw [reassoc₁, reassoc₂, s.condition])) :=
                                 -- 🎉 no goals
  PushoutCocone.isColimitAux' _ fun t => ⟨hs.desc (PushoutCocone.mk t.inl t.inr <| by
    rw [← hhx, ← hhy, Category.assoc, Category.assoc, t.condition]),
    -- 🎉 no goals
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun hr hr' => by
        apply PushoutCocone.IsColimit.hom_ext hs;
        -- ⊢ inl s ≫ m✝ = inl s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ i …
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          -- ⊢ inl s ≫ m✝ = inl s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ i …
          simp only [hr, hr']
          -- ⊢ inl t = inl s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ inl t  …
          symm
          -- ⊢ inl s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ inl t = g ≫ in …
          exact hs.fac _ WalkingSpan.left
          -- 🎉 no goals
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          -- ⊢ inr s ≫ m✝ = inr s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ i …
          simp only [hr, hr']
          -- ⊢ inr t = inr s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ inl t  …
          symm
          -- ⊢ inr s ≫ Limits.IsColimit.desc hs (mk (inl t) (inr t) (_ : f ≫ inl t = g ≫ in …
          exact hs.fac _ WalkingSpan.right⟩⟩
          -- 🎉 no goals
#align category_theory.limits.pushout_cocone.is_colimit_of_factors CategoryTheory.Limits.PushoutCocone.isColimitOfFactors

/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
    (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [Category.assoc, Category.assoc, s.condition])) := by
          -- 🎉 no goals
  apply PushoutCocone.isColimitAux'
  -- ⊢ (s_1 : PushoutCocone (h ≫ f) (h ≫ g)) → { l // inl (mk (inl s) (inr s) (_ :  …
  intro s
  -- ⊢ { l // inl (mk (inl s✝) (inr s✝) (_ : (h ≫ f) ≫ inl s✝ = (h ≫ g) ≫ inr s✝))  …
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine' ⟨l, h₁, h₂, _⟩
  -- ⊢ ∀ {m : (mk (inl s✝) (inr s✝) (_ : (h ≫ f) ≫ inl s✝ = (h ≫ g) ≫ inr s✝)).pt ⟶ …
  intro m hm₁ hm₂
  -- ⊢ m = l
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
  -- 🎉 no goals
#align category_theory.limits.pushout_cocone.is_colimit_of_epi_comp CategoryTheory.Limits.PushoutCocone.isColimitOfEpiComp

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : WalkingCospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `hasPullbacks_of_hasLimit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simps]
def Cone.ofPullbackCone {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) : Cone F
    where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).inv
#align category_theory.limits.cone.of_pullback_cone CategoryTheory.Limits.Cone.ofPullbackCone

/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : WalkingSpan ⥤ C`, which is really the same as
    `span (F.map fst) (F.map snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `hasPushouts_of_hasColimit_span`, which
    you may find to be an easier way of achieving your goal. -/
@[simps]
def Cocone.ofPushoutCocone {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) :
    Cocone F where
  pt := t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι
#align category_theory.limits.cocone.of_pushout_cocone CategoryTheory.Limits.Cocone.ofPushoutCocone

/-- Given `F : WalkingCospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
def PullbackCone.ofCone {F : WalkingCospan ⥤ C} (t : Cone F) : PullbackCone (F.map inl) (F.map inr)
    where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).hom
#align category_theory.limits.pullback_cone.of_cone CategoryTheory.Limits.PullbackCone.ofCone

/-- A diagram `WalkingCospan ⥤ C` is isomorphic to some `PullbackCone.mk` after
composing with `diagramIsoCospan`. -/
@[simps!]
def PullbackCone.isoMk {F : WalkingCospan ⥤ C} (t : Cone F) :
    (Cones.postcompose (diagramIsoCospan.{v} _).hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr : _)) :=
  Cones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        -- ⊢ NatTrans.app t.π none ≫ 𝟙 (F.obj none) = 𝟙 t.pt ≫ NatTrans.app t.π WalkingCo …
        -- ⊢ NatTrans.app t.π (some WalkingPair.left) ≫ 𝟙 (F.obj (some WalkingPair.left)) …
        -- 🎉 no goals
        -- ⊢ NatTrans.app t.π (some WalkingPair.right) ≫ 𝟙 (F.obj (some WalkingPair.right …
        -- 🎉 no goals
        simp
        -- 🎉 no goals
#align category_theory.limits.pullback_cone.iso_mk CategoryTheory.Limits.PullbackCone.isoMk

/-- Given `F : WalkingSpan ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
def PushoutCocone.ofCocone {F : WalkingSpan ⥤ C} (t : Cocone F) :
    PushoutCocone (F.map fst) (F.map snd) where
  pt := t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι
#align category_theory.limits.pushout_cocone.of_cocone CategoryTheory.Limits.PushoutCocone.ofCocone

/-- A diagram `WalkingSpan ⥤ C` is isomorphic to some `PushoutCocone.mk` after composing with
`diagramIsoSpan`. -/
@[simps!]
def PushoutCocone.isoMk {F : WalkingSpan ⥤ C} (t : Cocone F) :
    (Cocones.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
  Cocones.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;>
      · dsimp
        -- ⊢ (𝟙 (F.obj WalkingSpan.zero) ≫ NatTrans.app t.ι none) ≫ 𝟙 t.pt = F.map fst ≫  …
        -- ⊢ (𝟙 (F.obj WalkingSpan.left) ≫ NatTrans.app t.ι (some WalkingPair.left)) ≫ 𝟙  …
        -- 🎉 no goals
        -- ⊢ (𝟙 (F.obj WalkingSpan.right) ≫ NatTrans.app t.ι (some WalkingPair.right)) ≫  …
        -- 🎉 no goals
        simp
        -- 🎉 no goals
#align category_theory.limits.pushout_cocone.iso_mk CategoryTheory.Limits.PushoutCocone.isoMk

/-- `HasPullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
abbrev HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasLimit (cospan f g)
#align category_theory.limits.has_pullback CategoryTheory.Limits.HasPullback

/-- `HasPushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
abbrev HasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :=
  HasColimit (span f g)
#align category_theory.limits.has_pushout CategoryTheory.Limits.HasPushout

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
abbrev pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :=
  limit (cospan f g)
#align category_theory.limits.pullback CategoryTheory.Limits.pullback

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
abbrev pushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :=
  colimit (span f g)
#align category_theory.limits.pushout CategoryTheory.Limits.pushout

/-- The first projection of the pullback of `f` and `g`. -/
abbrev pullback.fst {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) WalkingCospan.left
#align category_theory.limits.pullback.fst CategoryTheory.Limits.pullback.fst

/-- The second projection of the pullback of `f` and `g`. -/
abbrev pullback.snd {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) WalkingCospan.right
#align category_theory.limits.pullback.snd CategoryTheory.Limits.pullback.snd

/-- The first inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inl {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.left
#align category_theory.limits.pushout.inl CategoryTheory.Limits.pushout.inl

/-- The second inclusion into the pushout of `f` and `g`. -/
abbrev pushout.inr {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) WalkingSpan.right
#align category_theory.limits.pushout.inr CategoryTheory.Limits.pushout.inr

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
abbrev pullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift _ (PullbackCone.mk h k w)
#align category_theory.limits.pullback.lift CategoryTheory.Limits.pullback.lift

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
abbrev pushout.desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc _ (PushoutCocone.mk h k w)
#align category_theory.limits.pushout.desc CategoryTheory.Limits.pushout.desc

@[simp]
theorem PullbackCone.fst_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasLimit (cospan f g)] : PullbackCone.fst (limit.cone (cospan f g)) = pullback.fst := rfl
#align category_theory.limits.pullback_cone.fst_colimit_cocone CategoryTheory.Limits.PullbackCone.fst_colimit_cocone

@[simp]
theorem PullbackCone.snd_colimit_cocone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasLimit (cospan f g)] : PullbackCone.snd (limit.cone (cospan f g)) = pullback.snd := rfl
#align category_theory.limits.pullback_cone.snd_colimit_cocone CategoryTheory.Limits.PullbackCone.snd_colimit_cocone

-- Porting note: simp can prove this; removed simp
theorem PushoutCocone.inl_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inl (colimit.cocone (span f g)) = pushout.inl := rfl
#align category_theory.limits.pushout_cocone.inl_colimit_cocone CategoryTheory.Limits.PushoutCocone.inl_colimit_cocone

-- Porting note: simp can prove this; removed simp
theorem PushoutCocone.inr_colimit_cocone {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)
    [HasColimit (span f g)] : PushoutCocone.inr (colimit.cocone (span f g)) = pushout.inr := rfl
#align category_theory.limits.pushout_cocone.inr_colimit_cocone CategoryTheory.Limits.PushoutCocone.inr_colimit_cocone

-- Porting note: simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.fst = h :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_fst CategoryTheory.Limits.pullback.lift_fst

-- Porting note: simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : pullback.lift h k w ≫ pullback.snd = k :=
  limit.lift_π _ _
#align category_theory.limits.pullback.lift_snd CategoryTheory.Limits.pullback.lift_snd

-- Porting note: simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pushout.inl_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inl ≫ pushout.desc h k w = h :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inl_desc CategoryTheory.Limits.pushout.inl_desc

-- Porting note: simp can prove this and reassoced version; removed simp
@[reassoc]
theorem pushout.inr_desc {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W)
    (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout.inr ≫ pushout.desc h k w = k :=
  colimit.ι_desc _ _
#align category_theory.limits.pushout.inr_desc CategoryTheory.Limits.pushout.inr_desc

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ pullback f g // l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k } :=
  ⟨pullback.lift h k w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
#align category_theory.limits.pullback.lift' CategoryTheory.Limits.pullback.lift'

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : pushout f g ⟶ W // pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k } :=
  ⟨pushout.desc h k w, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩
#align category_theory.limits.pullback.desc' CategoryTheory.Limits.pullback.desc'

@[reassoc]
theorem pullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] :
    (pullback.fst : pullback f g ⟶ X) ≫ f = pullback.snd ≫ g :=
  PullbackCone.condition _
#align category_theory.limits.pullback.condition CategoryTheory.Limits.pullback.condition

@[reassoc]
theorem pushout.condition {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] :
    f ≫ (pushout.inl : Y ⟶ pushout f g) = g ≫ pushout.inr :=
  PushoutCocone.condition _
#align category_theory.limits.pushout.condition CategoryTheory.Limits.pushout.condition

/-- Given such a diagram, then there is a natural morphism `W ×ₛ X ⟶ Y ×ₜ Z`.

    W ⟶ Y
      ↘      ↘
        S ⟶ T
      ↗      ↗
    X ⟶ Z

-/
abbrev pullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂] (g₁ : Y ⟶ T)
    (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ i₂)
    (by simp [← eq₁, ← eq₂, pullback.condition_assoc])
        -- 🎉 no goals
#align category_theory.limits.pullback.map CategoryTheory.Limits.pullback.map

/-- The canonical map `X ×ₛ Y ⟶ X ×ₜ Y` given `S ⟶ T`. -/
abbrev pullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasPullback f g]
    [HasPullback (f ≫ i) (g ≫ i)] : pullback f g ⟶ pullback (f ≫ i) (g ≫ i) :=
  pullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm (Category.id_comp _).symm
#align category_theory.limits.pullback.map_desc CategoryTheory.Limits.pullback.mapDesc

/-- Given such a diagram, then there is a natural morphism `W ⨿ₛ X ⟶ Y ⨿ₜ Z`.

        W ⟶ Y
      ↗      ↗
    S ⟶ T
      ↘      ↘
        X ⟶ Z

-/
abbrev pushout.map {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y)
    (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) : pushout f₁ f₂ ⟶ pushout g₁ g₂ :=
  pushout.desc (i₁ ≫ pushout.inl) (i₂ ≫ pushout.inr)
    (by
      simp only [← Category.assoc, eq₁, eq₂]
      -- ⊢ (i₃ ≫ g₁) ≫ inl = (i₃ ≫ g₂) ≫ inr
      simp [pushout.condition])
      -- 🎉 no goals
#align category_theory.limits.pushout.map CategoryTheory.Limits.pushout.map

/-- The canonical map `X ⨿ₛ Y ⟶ X ⨿ₜ Y` given `S ⟶ T`. -/
abbrev pushout.mapLift {X Y S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) [HasPushout f g]
    [HasPushout (i ≫ f) (i ≫ g)] : pushout (i ≫ f) (i ≫ g) ⟶ pushout f g :=
  pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (Category.comp_id _) (Category.comp_id _)
#align category_theory.limits.pushout.map_lift CategoryTheory.Limits.pushout.mapLift

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
@[ext 1100]
theorem pullback.hom_ext {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] {W : C}
    {k l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst)
    (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext <| PullbackCone.equalizer_ext _ h₀ h₁
#align category_theory.limits.pullback.hom_ext CategoryTheory.Limits.pullback.hom_ext

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullbackIsPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (PullbackCone.mk (pullback.fst : pullback f g ⟶ _) pullback.snd pullback.condition) :=
  PullbackCone.IsLimit.mk _ (fun s => pullback.lift s.fst s.snd s.condition) (by simp) (by simp)
                                                                                 -- 🎉 no goals
                                                                                           -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
#align category_theory.limits.pullback_is_pullback CategoryTheory.Limits.pullbackIsPullback

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst : pullback f g ⟶ X) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.fst_of_mono CategoryTheory.Limits.pullback.fst_of_mono

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd : pullback f g ⟶ Y) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.snd_of_mono CategoryTheory.Limits.pullback.snd_of_mono

/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    -- ⊢ i₁ ≫ pullback.fst = i₂ ≫ pullback.fst
    · simpa using congrArg (fun f => f ≫ prod.fst) h
      -- 🎉 no goals
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩
      -- 🎉 no goals
#align category_theory.limits.mono_pullback_to_prod CategoryTheory.Limits.mono_pullback_to_prod

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
@[ext 1100]
theorem pushout.hom_ext {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] {W : C}
    {k l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l)
    (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext <| PushoutCocone.coequalizer_ext _ h₀ h₁
#align category_theory.limits.pushout.hom_ext CategoryTheory.Limits.pushout.hom_ext

/-- The pushout cocone built from the pushout coprojections is a pushout. -/
def pushoutIsPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (PushoutCocone.mk (pushout.inl : _ ⟶ pushout f g) pushout.inr pushout.condition) :=
  PushoutCocone.IsColimit.mk _ (fun s => pushout.desc s.inl s.inr s.condition) (by simp) (by simp)
                                                                                   -- 🎉 no goals
                                                                                             -- 🎉 no goals
    (by aesop_cat)
        -- 🎉 no goals
#align category_theory.limits.pushout_is_pushout CategoryTheory.Limits.pushoutIsPushout

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl : Y ⟶ pushout f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inl_of_epi CategoryTheory.Limits.pushout.inl_of_epi

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inr_of_epi CategoryTheory.Limits.pushout.inr_of_epi

/-- The map ` X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    -- ⊢ pushout.inl ≫ i₁ = pushout.inl ≫ i₂
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
      -- 🎉 no goals
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩
      -- 🎉 no goals
#align category_theory.limits.epi_coprod_to_pushout CategoryTheory.Limits.epi_coprod_to_pushout

instance pullback.map_isIso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine' ⟨⟨pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
    -- 🎉 no goals
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
    -- 🎉 no goals
  · aesop_cat
    -- 🎉 no goals
  · aesop_cat
    -- 🎉 no goals
#align category_theory.limits.pullback.map_is_iso CategoryTheory.Limits.pullback.map_isIso

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pullback f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pullback.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] : pullback f₁ g₁ ≅ pullback f₂ g₂ :=
  asIso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
                                                      -- 🎉 no goals
                                                                     -- 🎉 no goals
#align category_theory.limits.pullback.congr_hom CategoryTheory.Limits.pullback.congrHom

@[simp]
theorem pullback.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPullback f₁ g₁] [HasPullback f₂ g₂] :
    (pullback.congrHom h₁ h₂).inv =
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
                                                 -- 🎉 no goals
                                                                -- 🎉 no goals
  ext
  -- ⊢ (congrHom h₁ h₂).inv ≫ fst = map f₂ g₂ f₁ g₁ (𝟙 X) (𝟙 Y) (𝟙 Z) (_ : f₂ ≫ 𝟙 Z …
  · erw [pullback.lift_fst]
    -- ⊢ (congrHom h₁ h₂).inv ≫ fst = fst ≫ 𝟙 X
    rw [Iso.inv_comp_eq]
    -- ⊢ fst = (congrHom h₁ h₂).hom ≫ fst ≫ 𝟙 X
    erw [pullback.lift_fst_assoc]
    -- ⊢ fst = (fst ≫ 𝟙 X) ≫ 𝟙 X
    rw [Category.comp_id, Category.comp_id]
    -- 🎉 no goals
  · erw [pullback.lift_snd]
    -- ⊢ (congrHom h₁ h₂).inv ≫ snd = snd ≫ 𝟙 Y
    rw [Iso.inv_comp_eq]
    -- ⊢ snd = (congrHom h₁ h₂).hom ≫ snd ≫ 𝟙 Y
    erw [pullback.lift_snd_assoc]
    -- ⊢ snd = (snd ≫ 𝟙 Y) ≫ 𝟙 Y
    rw [Category.comp_id, Category.comp_id]
    -- 🎉 no goals
#align category_theory.limits.pullback.congr_hom_inv CategoryTheory.Limits.pullback.congrHom_inv

instance pushout.map_isIso {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁) (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) [IsIso i₁] [IsIso i₂] [IsIso i₃] :
    IsIso (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) := by
  refine' ⟨⟨pushout.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _, _, _⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₁, IsIso.inv_hom_id_assoc]
    -- 🎉 no goals
  · rw [IsIso.comp_inv_eq, Category.assoc, eq₂, IsIso.inv_hom_id_assoc]
    -- 🎉 no goals
  · aesop_cat
    -- 🎉 no goals
  · aesop_cat
    -- 🎉 no goals
#align category_theory.limits.pushout.map_is_iso CategoryTheory.Limits.pushout.map_isIso

theorem pullback.mapDesc_comp {X Y S T S' : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S) (i' : S ⟶ S')
    [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)] [HasPullback (f ≫ i ≫ i') (g ≫ i ≫ i')]
    [HasPullback ((f ≫ i) ≫ i') ((g ≫ i) ≫ i')] :
    pullback.mapDesc f g (i ≫ i') = pullback.mapDesc f g i ≫ pullback.mapDesc _ _ i' ≫
    (pullback.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom := by
  aesop_cat
  -- 🎉 no goals
#align category_theory.limits.pullback.map_desc_comp CategoryTheory.Limits.pullback.mapDesc_comp

/-- If `f₁ = f₂` and `g₁ = g₂`, we may construct a canonical
isomorphism `pushout f₁ g₁ ≅ pullback f₂ g₂` -/
@[simps! hom]
def pushout.congrHom {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂) (h₂ : g₁ = g₂)
    [HasPushout f₁ g₁] [HasPushout f₂ g₂] : pushout f₁ g₁ ≅ pushout f₂ g₂ :=
  asIso <| pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂])
                                                     -- 🎉 no goals
                                                                    -- 🎉 no goals
#align category_theory.limits.pushout.congr_hom CategoryTheory.Limits.pushout.congrHom

@[simp]
theorem pushout.congrHom_inv {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f₁ = f₂)
    (h₂ : g₁ = g₂) [HasPushout f₁ g₁] [HasPushout f₂ g₂] :
    (pushout.congrHom h₁ h₂).inv =
      pushout.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp [h₁]) (by simp [h₂]) := by
                                                -- 🎉 no goals
                                                               -- 🎉 no goals
  ext
  -- ⊢ inl ≫ (congrHom h₁ h₂).inv = inl ≫ map f₂ g₂ f₁ g₁ (𝟙 Y) (𝟙 Z) (𝟙 X) (_ : f₂ …
  · erw [pushout.inl_desc]
    -- ⊢ inl ≫ (congrHom h₁ h₂).inv = 𝟙 Y ≫ inl
    rw [Iso.comp_inv_eq, Category.id_comp]
    -- ⊢ inl = inl ≫ (congrHom h₁ h₂).hom
    erw [pushout.inl_desc]
    -- ⊢ inl = 𝟙 Y ≫ inl
    rw [Category.id_comp]
    -- 🎉 no goals
  · erw [pushout.inr_desc]
    -- ⊢ inr ≫ (congrHom h₁ h₂).inv = 𝟙 Z ≫ inr
    rw [Iso.comp_inv_eq, Category.id_comp]
    -- ⊢ inr = inr ≫ (congrHom h₁ h₂).hom
    erw [pushout.inr_desc]
    -- ⊢ inr = 𝟙 Z ≫ inr
    rw [Category.id_comp]
    -- 🎉 no goals
#align category_theory.limits.pushout.congr_hom_inv CategoryTheory.Limits.pushout.congrHom_inv

theorem pushout.mapLift_comp {X Y S T S' : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) (i' : S' ⟶ S)
    [HasPushout f g] [HasPushout (i ≫ f) (i ≫ g)] [HasPushout (i' ≫ i ≫ f) (i' ≫ i ≫ g)]
    [HasPushout ((i' ≫ i) ≫ f) ((i' ≫ i) ≫ g)] :
    pushout.mapLift f g (i' ≫ i) =
      (pushout.congrHom (Category.assoc _ _ _) (Category.assoc _ _ _)).hom ≫
        pushout.mapLift _ _ i' ≫ pushout.mapLift f g i := by
  aesop_cat
  -- 🎉 no goals
#align category_theory.limits.pushout.map_lift_comp CategoryTheory.Limits.pushout.mapLift_comp

section

variable (G : C ⥤ D)

/-- The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [HasPullback (G.map f) (G.map g)] :
    G.obj (pullback f g) ⟶ pullback (G.map f) (G.map g) :=
  pullback.lift (G.map pullback.fst) (G.map pullback.snd)
    (by simp only [← G.map_comp, pullback.condition])
        -- 🎉 no goals
#align category_theory.limits.pullback_comparison CategoryTheory.Limits.pullbackComparison

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_fst (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.fst = G.map pullback.fst :=
  pullback.lift_fst _ _ _
#align category_theory.limits.pullback_comparison_comp_fst CategoryTheory.Limits.pullbackComparison_comp_fst

@[reassoc (attr := simp)]
theorem pullbackComparison_comp_snd (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] :
    pullbackComparison G f g ≫ pullback.snd = G.map pullback.snd :=
  pullback.lift_snd _ _ _
#align category_theory.limits.pullback_comparison_comp_snd CategoryTheory.Limits.pullbackComparison_comp_snd

@[reassoc (attr := simp)]
theorem map_lift_pullbackComparison (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [HasPullback (G.map f) (G.map g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) :
    G.map (pullback.lift _ _ w) ≫ pullbackComparison G f g =
      pullback.lift (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
                                            -- 🎉 no goals
  ext <;> simp [← G.map_comp]
  -- ⊢ (G.map (pullback.lift h k w) ≫ pullbackComparison G f g) ≫ pullback.fst = pu …
          -- 🎉 no goals
          -- 🎉 no goals
#align category_theory.limits.map_lift_pullback_comparison CategoryTheory.Limits.map_lift_pullbackComparison

/-- The comparison morphism for the pushout of `f,g`.
This is an isomorphism iff `G` preserves the pushout of `f,g`; see
`CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean`
-/
def pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] [HasPushout (G.map f) (G.map g)] :
    pushout (G.map f) (G.map g) ⟶ G.obj (pushout f g) :=
  pushout.desc (G.map pushout.inl) (G.map pushout.inr)
    (by simp only [← G.map_comp, pushout.condition])
        -- 🎉 no goals
#align category_theory.limits.pushout_comparison CategoryTheory.Limits.pushoutComparison

@[reassoc (attr := simp)]
theorem inl_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inl ≫ pushoutComparison G f g = G.map pushout.inl :=
  pushout.inl_desc _ _ _
#align category_theory.limits.inl_comp_pushout_comparison CategoryTheory.Limits.inl_comp_pushoutComparison

@[reassoc (attr := simp)]
theorem inr_comp_pushoutComparison (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] : pushout.inr ≫ pushoutComparison G f g = G.map pushout.inr :=
  pushout.inr_desc _ _ _
#align category_theory.limits.inr_comp_pushout_comparison CategoryTheory.Limits.inr_comp_pushoutComparison

@[reassoc (attr := simp)]
theorem pushoutComparison_map_desc (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [HasPushout (G.map f) (G.map g)] {W : C} {h : Y ⟶ W} {k : Z ⟶ W} (w : f ≫ h = g ≫ k) :
    pushoutComparison G f g ≫ G.map (pushout.desc _ _ w) =
      pushout.desc (G.map h) (G.map k) (by simp only [← G.map_comp, w]) := by
                                           -- 🎉 no goals
  ext <;> simp [← G.map_comp]
  -- ⊢ pushout.inl ≫ pushoutComparison G f g ≫ G.map (pushout.desc h k w) = pushout …
          -- 🎉 no goals
          -- 🎉 no goals
#align category_theory.limits.pushout_comparison_map_desc CategoryTheory.Limits.pushoutComparison_map_desc

end

section PullbackSymmetry

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPullback_symmetry [HasPullback f g] : HasPullback g f :=
  ⟨⟨⟨PullbackCone.mk _ _ pullback.condition.symm,
        PullbackCone.flipIsLimit (pullbackIsPullback _ _)⟩⟩⟩
#align category_theory.limits.has_pullback_symmetry CategoryTheory.Limits.hasPullback_symmetry

attribute [local instance] hasPullback_symmetry

/-- The isomorphism `X ×[Z] Y ≅ Y ×[Z] X`. -/
def pullbackSymmetry [HasPullback f g] : pullback f g ≅ pullback g f :=
  IsLimit.conePointUniqueUpToIso
    (PullbackCone.flipIsLimit (pullbackIsPullback f g) :
      IsLimit (PullbackCone.mk _ _ pullback.condition.symm))
    (limit.isLimit _)
#align category_theory.limits.pullback_symmetry CategoryTheory.Limits.pullbackSymmetry

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.fst = pullback.snd := by simp [pullbackSymmetry]
                                                                   -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_hom_comp_fst CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst

@[reassoc (attr := simp)]
theorem pullbackSymmetry_hom_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).hom ≫ pullback.snd = pullback.fst := by simp [pullbackSymmetry]
                                                                   -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_hom_comp_snd CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_fst [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.fst = pullback.snd := by simp [Iso.inv_comp_eq]
                                                                   -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_inv_comp_fst CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst

@[reassoc (attr := simp)]
theorem pullbackSymmetry_inv_comp_snd [HasPullback f g] :
    (pullbackSymmetry f g).inv ≫ pullback.snd = pullback.fst := by simp [Iso.inv_comp_eq]
                                                                   -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_inv_comp_snd CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd

end PullbackSymmetry

section PushoutSymmetry

open WalkingCospan

variable (f : X ⟶ Y) (g : X ⟶ Z)

/-- Making this a global instance would make the typeclass search go in an infinite loop. -/
theorem hasPushout_symmetry [HasPushout f g] : HasPushout g f :=
  ⟨⟨⟨PushoutCocone.mk _ _ pushout.condition.symm,
        PushoutCocone.flipIsColimit (pushoutIsPushout _ _)⟩⟩⟩
#align category_theory.limits.has_pushout_symmetry CategoryTheory.Limits.hasPushout_symmetry

attribute [local instance] hasPushout_symmetry

/-- The isomorphism `Y ⨿[X] Z ≅ Z ⨿[X] Y`. -/
def pushoutSymmetry [HasPushout f g] : pushout f g ≅ pushout g f :=
  IsColimit.coconePointUniqueUpToIso
    (PushoutCocone.flipIsColimit (pushoutIsPushout f g) :
      IsColimit (PushoutCocone.mk _ _ pushout.condition.symm))
    (colimit.isColimit _)
#align category_theory.limits.pushout_symmetry CategoryTheory.Limits.pushoutSymmetry

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).hom = pushout.inr :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inl_comp_pushout_symmetry_hom CategoryTheory.Limits.inl_comp_pushoutSymmetry_hom

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_hom [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).hom = pushout.inl :=
  (colimit.isColimit (span f g)).comp_coconePointUniqueUpToIso_hom
    (PushoutCocone.flipIsColimit (pushoutIsPushout g f)) _
#align category_theory.limits.inr_comp_pushout_symmetry_hom CategoryTheory.Limits.inr_comp_pushoutSymmetry_hom

@[reassoc (attr := simp)]
theorem inl_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inl ≫ (pushoutSymmetry f g).inv = pushout.inr := by simp [Iso.comp_inv_eq]
                                                                -- 🎉 no goals
#align category_theory.limits.inl_comp_pushout_symmetry_inv CategoryTheory.Limits.inl_comp_pushoutSymmetry_inv

@[reassoc (attr := simp)]
theorem inr_comp_pushoutSymmetry_inv [HasPushout f g] :
    pushout.inr ≫ (pushoutSymmetry f g).inv = pushout.inl := by simp [Iso.comp_inv_eq]
                                                                -- 🎉 no goals
#align category_theory.limits.inr_comp_pushout_symmetry_inv CategoryTheory.Limits.inr_comp_pushoutSymmetry_inv

end PushoutSymmetry

section PullbackLeftIso

open WalkingCospan

/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk pullback.fst pullback.snd
      (show pullback.fst ≫ f ≫ i = pullback.snd ≫ g ≫ i from by -- Porting note: used to be _
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition )) :=
        -- ⊢ (pullback.fst ≫ f) ≫ i = (pullback.snd ≫ g) ≫ i
                                                        -- 🎉 no goals
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))
#align category_theory.limits.pullback_is_pullback_of_comp_mono CategoryTheory.Limits.pullbackIsPullbackOfCompMono

instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩
#align category_theory.limits.has_pullback_of_comp_mono CategoryTheory.Limits.hasPullback_of_comp_mono

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Z` is iso, then `X ×[Z] Y ≅ Y`. This is the explicit limit cone. -/
def pullbackConeOfLeftIso : PullbackCone f g :=
  PullbackCone.mk (g ≫ inv f) (𝟙 _) <| by simp
                                          -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_left_iso CategoryTheory.Limits.pullbackConeOfLeftIso

@[simp]
theorem pullbackConeOfLeftIso_x : (pullbackConeOfLeftIso f g).pt = Y := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pullback_cone_of_left_iso_X CategoryTheory.Limits.pullbackConeOfLeftIso_x

@[simp]
theorem pullbackConeOfLeftIso_fst : (pullbackConeOfLeftIso f g).fst = g ≫ inv f := rfl
#align category_theory.limits.pullback_cone_of_left_iso_fst CategoryTheory.Limits.pullbackConeOfLeftIso_fst

@[simp]
theorem pullbackConeOfLeftIso_snd : (pullbackConeOfLeftIso f g).snd = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_left_iso_snd CategoryTheory.Limits.pullbackConeOfLeftIso_snd

-- Porting note: simp can prove this; removed simp
theorem pullbackConeOfLeftIso_π_app_none : (pullbackConeOfLeftIso f g).π.app none = g := by simp
                                                                                            -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_left_iso_π_app_none CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_none

@[simp]
theorem pullbackConeOfLeftIso_π_app_left : (pullbackConeOfLeftIso f g).π.app left = g ≫ inv f :=
  rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_left CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_left

@[simp]
theorem pullbackConeOfLeftIso_π_app_right : (pullbackConeOfLeftIso f g).π.app right = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_left_iso_π_app_right CategoryTheory.Limits.pullbackConeOfLeftIso_π_app_right

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfLeftIsoIsLimit : IsLimit (pullbackConeOfLeftIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.snd, by simp [← s.condition_assoc]⟩
                                                 -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_left_iso_is_limit CategoryTheory.Limits.pullbackConeOfLeftIsoIsLimit

theorem hasPullback_of_left_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_left_iso CategoryTheory.Limits.hasPullback_of_left_iso

attribute [local instance] hasPullback_of_left_iso

instance pullback_snd_iso_of_left_iso : IsIso (pullback.snd : pullback f g ⟶ _) := by
  refine' ⟨⟨pullback.lift (g ≫ inv f) (𝟙 _) (by simp), _, by simp⟩⟩
  -- ⊢ pullback.snd ≫ pullback.lift (g ≫ inv f) (𝟙 Y) (_ : (g ≫ inv f) ≫ f = 𝟙 Y ≫  …
  ext
  -- ⊢ (pullback.snd ≫ pullback.lift (g ≫ inv f) (𝟙 Y) (_ : (g ≫ inv f) ≫ f = 𝟙 Y ≫ …
  · simp [← pullback.condition_assoc]
    -- 🎉 no goals
  · simp [pullback.condition_assoc]
    -- 🎉 no goals
#align category_theory.limits.pullback_snd_iso_of_left_iso CategoryTheory.Limits.pullback_snd_iso_of_left_iso

variable (i : Z ⟶ W) [Mono i]

instance hasPullback_of_right_factors_mono (f : X ⟶ Z) : HasPullback i (f ≫ i) := by
  conv =>
    congr
    rw [← Category.id_comp i]
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.has_pullback_of_right_factors_mono CategoryTheory.Limits.hasPullback_of_right_factors_mono

instance pullback_snd_iso_of_right_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.snd : pullback i (f ≫ i) ⟶ _) := by
  convert (congrArg IsIso (show _ ≫ pullback.snd = _ from
    limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right)).mp
    inferInstance;
  · exact (Category.id_comp _).symm
    -- 🎉 no goals
  · exact (Category.id_comp _).symm
    -- 🎉 no goals
#align category_theory.limits.pullback_snd_iso_of_right_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono

end PullbackLeftIso

section PullbackRightIso

open WalkingCospan

variable (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g]

/-- If `g : Y ⟶ Z` is iso, then `X ×[Z] Y ≅ X`. This is the explicit limit cone. -/
def pullbackConeOfRightIso : PullbackCone f g :=
  PullbackCone.mk (𝟙 _) (f ≫ inv g) <| by simp
                                          -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_right_iso CategoryTheory.Limits.pullbackConeOfRightIso

@[simp]
theorem pullbackConeOfRightIso_x : (pullbackConeOfRightIso f g).pt = X := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pullback_cone_of_right_iso_X CategoryTheory.Limits.pullbackConeOfRightIso_x

@[simp]
theorem pullbackConeOfRightIso_fst : (pullbackConeOfRightIso f g).fst = 𝟙 _ := rfl
#align category_theory.limits.pullback_cone_of_right_iso_fst CategoryTheory.Limits.pullbackConeOfRightIso_fst

@[simp]
theorem pullbackConeOfRightIso_snd : (pullbackConeOfRightIso f g).snd = f ≫ inv g := rfl
#align category_theory.limits.pullback_cone_of_right_iso_snd CategoryTheory.Limits.pullbackConeOfRightIso_snd

-- Porting note: simp can prove this; removed simps
theorem pullbackConeOfRightIso_π_app_none : (pullbackConeOfRightIso f g).π.app none = f := by simp
                                                                                              -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_right_iso_π_app_none CategoryTheory.Limits.pullbackConeOfRightIso_π_app_none

@[simp]
theorem pullbackConeOfRightIso_π_app_left : (pullbackConeOfRightIso f g).π.app left = 𝟙 _ :=
  rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_left CategoryTheory.Limits.pullbackConeOfRightIso_π_app_left

@[simp]
theorem pullbackConeOfRightIso_π_app_right : (pullbackConeOfRightIso f g).π.app right = f ≫ inv g
  := rfl
#align category_theory.limits.pullback_cone_of_right_iso_π_app_right CategoryTheory.Limits.pullbackConeOfRightIso_π_app_right

/-- Verify that the constructed limit cone is indeed a limit. -/
def pullbackConeOfRightIsoIsLimit : IsLimit (pullbackConeOfRightIso f g) :=
  PullbackCone.isLimitAux' _ fun s => ⟨s.fst, by simp [s.condition_assoc]⟩
                                                 -- 🎉 no goals
#align category_theory.limits.pullback_cone_of_right_iso_is_limit CategoryTheory.Limits.pullbackConeOfRightIsoIsLimit

theorem hasPullback_of_right_iso : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pullback_of_right_iso CategoryTheory.Limits.hasPullback_of_right_iso

attribute [local instance] hasPullback_of_right_iso

instance pullback_snd_iso_of_right_iso : IsIso (pullback.fst : pullback f g ⟶ _) := by
  refine' ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) (by simp), _, by simp⟩⟩
  -- ⊢ pullback.fst ≫ pullback.lift (𝟙 X) (f ≫ inv g) (_ : 𝟙 X ≫ f = (f ≫ inv g) ≫  …
  ext
  -- ⊢ (pullback.fst ≫ pullback.lift (𝟙 X) (f ≫ inv g) (_ : 𝟙 X ≫ f = (f ≫ inv g) ≫ …
  · simp
    -- 🎉 no goals
  · simp [pullback.condition_assoc]
    -- 🎉 no goals
#align category_theory.limits.pullback_snd_iso_of_right_iso CategoryTheory.Limits.pullback_snd_iso_of_right_iso

variable (i : Z ⟶ W) [Mono i]

instance hasPullback_of_left_factors_mono (f : X ⟶ Z) : HasPullback (f ≫ i) i := by
  conv =>
    congr
    case g => rw [← Category.id_comp i]
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.has_pullback_of_left_factors_mono CategoryTheory.Limits.hasPullback_of_left_factors_mono

instance pullback_snd_iso_of_left_factors_mono (f : X ⟶ Z) :
    IsIso (pullback.fst : pullback (f ≫ i) i ⟶ _) := by
  convert (congrArg IsIso (show _ ≫ pullback.fst = _ from
    limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left)).mp
    inferInstance;
  · exact (Category.id_comp _).symm
    -- 🎉 no goals
  · exact (Category.id_comp _).symm
    -- 🎉 no goals
#align category_theory.limits.pullback_snd_iso_of_left_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono

end PullbackRightIso

section PushoutLeftIso

open WalkingSpan

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk pushout.inl pushout.inr
    (show (h ≫ f) ≫ pushout.inl = (h ≫ g) ≫ pushout.inr from by
    simp only [Category.assoc]; rw [cancel_epi]; exact pushout.condition)) :=
    -- ⊢ h ≫ f ≫ pushout.inl = h ≫ g ≫ pushout.inr
                                                 -- 🎉 no goals
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))
#align category_theory.limits.pushout_is_pushout_of_epi_comp CategoryTheory.Limits.pushoutIsPushoutOfEpiComp

instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩
#align category_theory.limits.has_pushout_of_epi_comp CategoryTheory.Limits.hasPushout_of_epi_comp

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso f]

/-- If `f : X ⟶ Y` is iso, then `Y ⨿[X] Z ≅ Z`. This is the explicit colimit cocone. -/
def pushoutCoconeOfLeftIso : PushoutCocone f g :=
  PushoutCocone.mk (inv f ≫ g) (𝟙 _) <| by simp
                                           -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_left_iso CategoryTheory.Limits.pushoutCoconeOfLeftIso

@[simp]
theorem pushoutCoconeOfLeftIso_x : (pushoutCoconeOfLeftIso f g).pt = Z := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pushout_cocone_of_left_iso_X CategoryTheory.Limits.pushoutCoconeOfLeftIso_x

@[simp]
theorem pushoutCoconeOfLeftIso_inl : (pushoutCoconeOfLeftIso f g).inl = inv f ≫ g := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inl CategoryTheory.Limits.pushoutCoconeOfLeftIso_inl

@[simp]
theorem pushoutCoconeOfLeftIso_inr : (pushoutCoconeOfLeftIso f g).inr = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_inr CategoryTheory.Limits.pushoutCoconeOfLeftIso_inr

-- Porting note: simp can prove this; removed simp
theorem pushoutCoconeOfLeftIso_ι_app_none : (pushoutCoconeOfLeftIso f g).ι.app none = g := by
  simp
  -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_none

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_left : (pushoutCoconeOfLeftIso f g).ι.app left = inv f ≫ g :=
  rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_left

@[simp]
theorem pushoutCoconeOfLeftIso_ι_app_right : (pushoutCoconeOfLeftIso f g).ι.app right = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_left_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfLeftIso_ι_app_right

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfLeftIsoIsLimit : IsColimit (pushoutCoconeOfLeftIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inr, by simp [← s.condition]⟩
                                                    -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_left_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfLeftIsoIsLimit

theorem hasPushout_of_left_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfLeftIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_left_iso CategoryTheory.Limits.hasPushout_of_left_iso

attribute [local instance] hasPushout_of_left_iso

instance pushout_inr_iso_of_left_iso : IsIso (pushout.inr : _ ⟶ pushout f g) := by
  refine' ⟨⟨pushout.desc (inv f ≫ g) (𝟙 _) (by simp), by simp, _⟩⟩
  -- ⊢ pushout.desc (inv f ≫ g) (𝟙 Z) (_ : f ≫ inv f ≫ g = g ≫ 𝟙 Z) ≫ pushout.inr = …
  ext
  -- ⊢ pushout.inl ≫ pushout.desc (inv f ≫ g) (𝟙 Z) (_ : f ≫ inv f ≫ g = g ≫ 𝟙 Z) ≫ …
  · simp [← pushout.condition]
    -- 🎉 no goals
  · simp [pushout.condition_assoc]
    -- 🎉 no goals
#align category_theory.limits.pushout_inr_iso_of_left_iso CategoryTheory.Limits.pushout_inr_iso_of_left_iso

variable (h : W ⟶ X) [Epi h]

instance hasPushout_of_right_factors_epi (f : X ⟶ Y) : HasPushout h (h ≫ f) := by
  conv =>
    congr
    rw [← Category.comp_id h]
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.has_pushout_of_right_factors_epi CategoryTheory.Limits.hasPushout_of_right_factors_epi

instance pushout_inr_iso_of_right_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inr : _ ⟶ pushout h (h ≫ f)) := by
  convert (congrArg IsIso (show pushout.inr ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩ WalkingSpan.right)).mp
    inferInstance
  · apply (Category.comp_id _).symm
    -- 🎉 no goals
  · apply (Category.comp_id _).symm
    -- 🎉 no goals
#align category_theory.limits.pushout_inr_iso_of_right_factors_epi CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi

end PushoutLeftIso

section PushoutRightIso

open WalkingSpan

variable (f : X ⟶ Y) (g : X ⟶ Z) [IsIso g]

/-- If `f : X ⟶ Z` is iso, then `Y ⨿[X] Z ≅ Y`. This is the explicit colimit cocone. -/
def pushoutCoconeOfRightIso : PushoutCocone f g :=
  PushoutCocone.mk (𝟙 _) (inv g ≫ f) <| by simp
                                           -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_right_iso CategoryTheory.Limits.pushoutCoconeOfRightIso

@[simp]
theorem pushoutCoconeOfRightIso_x : (pushoutCoconeOfRightIso f g).pt = Y := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.limits.pushout_cocone_of_right_iso_X CategoryTheory.Limits.pushoutCoconeOfRightIso_x

@[simp]
theorem pushoutCoconeOfRightIso_inl : (pushoutCoconeOfRightIso f g).inl = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inl CategoryTheory.Limits.pushoutCoconeOfRightIso_inl

@[simp]
theorem pushoutCoconeOfRightIso_inr : (pushoutCoconeOfRightIso f g).inr = inv g ≫ f := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_inr CategoryTheory.Limits.pushoutCoconeOfRightIso_inr

-- Porting note: simp can prove this; removed simp
theorem pushoutCoconeOfRightIso_ι_app_none : (pushoutCoconeOfRightIso f g).ι.app none = f := by
  simp
  -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_none CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_none

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_left : (pushoutCoconeOfRightIso f g).ι.app left = 𝟙 _ := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_left CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_left

@[simp]
theorem pushoutCoconeOfRightIso_ι_app_right :
    (pushoutCoconeOfRightIso f g).ι.app right = inv g ≫ f := rfl
#align category_theory.limits.pushout_cocone_of_right_iso_ι_app_right CategoryTheory.Limits.pushoutCoconeOfRightIso_ι_app_right

/-- Verify that the constructed cocone is indeed a colimit. -/
def pushoutCoconeOfRightIsoIsLimit : IsColimit (pushoutCoconeOfRightIso f g) :=
  PushoutCocone.isColimitAux' _ fun s => ⟨s.inl, by simp [← s.condition]⟩
                                                    -- 🎉 no goals
#align category_theory.limits.pushout_cocone_of_right_iso_is_limit CategoryTheory.Limits.pushoutCoconeOfRightIsoIsLimit

theorem hasPushout_of_right_iso : HasPushout f g :=
  ⟨⟨⟨_, pushoutCoconeOfRightIsoIsLimit f g⟩⟩⟩
#align category_theory.limits.has_pushout_of_right_iso CategoryTheory.Limits.hasPushout_of_right_iso

attribute [local instance] hasPushout_of_right_iso

instance pushout_inl_iso_of_right_iso : IsIso (pushout.inl : _ ⟶ pushout f g) := by
  refine' ⟨⟨pushout.desc (𝟙 _) (inv g ≫ f) (by simp), by simp, _⟩⟩
  -- ⊢ pushout.desc (𝟙 Y) (inv g ≫ f) (_ : f ≫ 𝟙 Y = g ≫ inv g ≫ f) ≫ pushout.inl = …
  ext
  -- ⊢ pushout.inl ≫ pushout.desc (𝟙 Y) (inv g ≫ f) (_ : f ≫ 𝟙 Y = g ≫ inv g ≫ f) ≫ …
  · simp [← pushout.condition]
    -- 🎉 no goals
  · simp [pushout.condition]
    -- 🎉 no goals
#align category_theory.limits.pushout_inl_iso_of_right_iso CategoryTheory.Limits.pushout_inl_iso_of_right_iso

variable (h : W ⟶ X) [Epi h]

instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  conv =>
    congr
    case g => rw [← Category.comp_id h]
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.has_pushout_of_left_factors_epi CategoryTheory.Limits.hasPushout_of_left_factors_epi

instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl : _ ⟶ pushout (h ≫ f) h) := by
  convert (congrArg IsIso (show pushout.inl ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩ WalkingSpan.left)).mp
        inferInstance;
  · exact (Category.comp_id _).symm
    -- 🎉 no goals
  · exact (Category.comp_id _).symm
    -- 🎉 no goals
#align category_theory.limits.pushout_inl_iso_of_left_factors_epi CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi

end PushoutRightIso

section

open WalkingCospan

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [Mono f] : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_kernel_pair_of_mono CategoryTheory.Limits.has_kernel_pair_of_mono

theorem fst_eq_snd_of_mono_eq [Mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
  ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).cone left).symm.trans
    ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).cone right : _)
#align category_theory.limits.fst_eq_snd_of_mono_eq CategoryTheory.Limits.fst_eq_snd_of_mono_eq

@[simp]
theorem pullbackSymmetry_hom_of_mono_eq [Mono f] : (pullbackSymmetry f f).hom = 𝟙 _ := by
  ext; simp [fst_eq_snd_of_mono_eq]; simp [fst_eq_snd_of_mono_eq]
  -- ⊢ (pullbackSymmetry f f).hom ≫ pullback.fst = 𝟙 (pullback f f) ≫ pullback.fst
       -- ⊢ (pullbackSymmetry f f).hom ≫ pullback.snd = 𝟙 (pullback f f) ≫ pullback.snd
                                     -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_hom_of_mono_eq CategoryTheory.Limits.pullbackSymmetry_hom_of_mono_eq

instance fst_iso_of_mono_eq [Mono f] : IsIso (pullback.fst : pullback f f ⟶ _) := by
  refine' ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), _, by simp⟩⟩
  -- ⊢ pullback.fst ≫ pullback.lift (𝟙 X) (𝟙 X) (_ : 𝟙 X ≫ f = 𝟙 X ≫ f) = 𝟙 (pullba …
  ext
  -- ⊢ (pullback.fst ≫ pullback.lift (𝟙 X) (𝟙 X) (_ : 𝟙 X ≫ f = 𝟙 X ≫ f)) ≫ pullbac …
  · simp
    -- 🎉 no goals
  · simp [fst_eq_snd_of_mono_eq]
    -- 🎉 no goals
#align category_theory.limits.fst_iso_of_mono_eq CategoryTheory.Limits.fst_iso_of_mono_eq

instance snd_iso_of_mono_eq [Mono f] : IsIso (pullback.snd : pullback f f ⟶ _) := by
  rw [← fst_eq_snd_of_mono_eq]
  -- ⊢ IsIso pullback.fst
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.snd_iso_of_mono_eq CategoryTheory.Limits.snd_iso_of_mono_eq

end

section

open WalkingSpan

variable (f : X ⟶ Y)

instance has_cokernel_pair_of_epi [Epi f] : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_cokernel_pair_of_epi CategoryTheory.Limits.has_cokernel_pair_of_epi

theorem inl_eq_inr_of_epi_eq [Epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
  ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).cocone left).symm.trans
    ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).cocone right : _)
#align category_theory.limits.inl_eq_inr_of_epi_eq CategoryTheory.Limits.inl_eq_inr_of_epi_eq

@[simp]
theorem pullback_symmetry_hom_of_epi_eq [Epi f] : (pushoutSymmetry f f).hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]
  -- ⊢ pushout.inl ≫ (pushoutSymmetry f f).hom = pushout.inl ≫ 𝟙 (pushout f f)
          -- 🎉 no goals
          -- 🎉 no goals
#align category_theory.limits.pullback_symmetry_hom_of_epi_eq CategoryTheory.Limits.pullback_symmetry_hom_of_epi_eq

instance inl_iso_of_epi_eq [Epi f] : IsIso (pushout.inl : _ ⟶ pushout f f) := by
  refine' ⟨⟨pushout.desc (𝟙 _) (𝟙 _) (by simp), by simp, _⟩⟩
  -- ⊢ pushout.desc (𝟙 Y) (𝟙 Y) (_ : f ≫ 𝟙 Y = f ≫ 𝟙 Y) ≫ pushout.inl = 𝟙 (pushout  …
  apply pushout.hom_ext
  -- ⊢ pushout.inl ≫ pushout.desc (𝟙 Y) (𝟙 Y) (_ : f ≫ 𝟙 Y = f ≫ 𝟙 Y) ≫ pushout.inl …
  · simp
    -- 🎉 no goals
  · simp [inl_eq_inr_of_epi_eq]
    -- 🎉 no goals
#align category_theory.limits.inl_iso_of_epi_eq CategoryTheory.Limits.inl_iso_of_epi_eq

instance inr_iso_of_epi_eq [Epi f] : IsIso (pushout.inr : _ ⟶ pushout f f) := by
  rw [← inl_eq_inr_of_epi_eq]
  -- ⊢ IsIso pushout.inl
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.inr_iso_of_epi_eq CategoryTheory.Limits.inr_iso_of_epi_eq

end

section PasteLemma

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)

variable (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)

variable (h₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pullback if both the small squares are.
-/
def bigSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' : IsLimit (PullbackCone.mk _ _ h₁)) :
    IsLimit
      (PullbackCone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])) := by
          -- 🎉 no goals
  fapply PullbackCone.isLimitAux'
  -- ⊢ (s : PullbackCone (g₁ ≫ g₂) i₃) → { l // l ≫ PullbackCone.fst (PullbackCone. …
  intro s
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂  …
  have : (s.fst ≫ g₁) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, Category.assoc]
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂  …
  rcases PullbackCone.IsLimit.lift' H (s.fst ≫ g₁) s.snd this with ⟨l₁, hl₁, hl₁'⟩
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂  …
  rcases PullbackCone.IsLimit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂  …
  use l₂
  -- ⊢ l₂ ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂ = (f₁  …
  use hl₂
  -- ⊢ l₂ ≫ PullbackCone.snd (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂ = (f₁  …
  use
    show l₂ ≫ f₁ ≫ f₂ = s.snd by
      rw [← hl₁', ← hl₂', Category.assoc]
      rfl
  intro m hm₁ hm₂
  -- ⊢ m = l₂
  apply PullbackCone.IsLimit.hom_ext H'
  -- ⊢ m ≫ PullbackCone.fst (PullbackCone.mk i₁ f₁ h₁) = l₂ ≫ PullbackCone.fst (Pul …
  · erw [hm₁, hl₂]
    -- 🎉 no goals
  · apply PullbackCone.IsLimit.hom_ext H
    -- ⊢ (m ≫ PullbackCone.snd (PullbackCone.mk i₁ f₁ h₁)) ≫ PullbackCone.fst (Pullba …
    · erw [Category.assoc, ← h₁, ← Category.assoc, hm₁, ← hl₂, Category.assoc, Category.assoc, h₁]
      -- ⊢ l₂ ≫ f₁ ≫ i₂ = l₂ ≫ PullbackCone.snd (PullbackCone.mk i₁ f₁ h₁) ≫ PullbackCo …
      rfl
      -- 🎉 no goals
    · erw [Category.assoc, hm₂, ← hl₁', ← hl₂']
      -- 🎉 no goals
#align category_theory.limits.big_square_is_pullback CategoryTheory.Limits.bigSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the big square is a pushout if both the small squares are.
-/
def bigSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₂))
    (H' : IsColimit (PushoutCocone.mk _ _ h₁)) :
    IsColimit
      (PushoutCocone.mk _ _
        (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc])) := by
          -- 🎉 no goals
  fapply PushoutCocone.isColimitAux'
  -- ⊢ (s : PushoutCocone i₁ (f₁ ≫ f₂)) → { l // PushoutCocone.inl (PushoutCocone.m …
  intro s
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ =  …
  have : i₁ ≫ s.inl = f₁ ≫ f₂ ≫ s.inr := by rw [s.condition, Category.assoc]
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ =  …
  rcases PushoutCocone.IsColimit.desc' H' s.inl (f₂ ≫ s.inr) this with ⟨l₁, hl₁, hl₁'⟩
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ =  …
  rcases PushoutCocone.IsColimit.desc' H l₁ s.inr hl₁' with ⟨l₂, hl₂, hl₂'⟩
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ =  …
  use l₂
  -- ⊢ PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f …
  use
    show (g₁ ≫ g₂) ≫ l₂ = s.inl by
      rw [← hl₁, ← hl₂, Category.assoc]
      rfl
  use hl₂'
  -- ⊢ ∀ {m : (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃)).p …
  intro m hm₁ hm₂
  -- ⊢ m = l₂
  apply PushoutCocone.IsColimit.hom_ext H
  -- ⊢ PushoutCocone.inl (PushoutCocone.mk g₂ i₃ h₂) ≫ m = PushoutCocone.inl (Pusho …
  · apply PushoutCocone.IsColimit.hom_ext H'
    -- ⊢ PushoutCocone.inl (PushoutCocone.mk g₁ i₂ h₁) ≫ PushoutCocone.inl (PushoutCo …
    · erw [← Category.assoc, hm₁, hl₂, hl₁]
      -- 🎉 no goals
    · erw [← Category.assoc, h₂, Category.assoc, hm₂, ← hl₂', ← Category.assoc, ← Category.assoc, ←
        h₂]
      rfl
      -- 🎉 no goals
  · erw [hm₂, hl₂']
    -- 🎉 no goals
#align category_theory.limits.big_square_is_pushout CategoryTheory.Limits.bigSquareIsPushout

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the left square is a pullback if the right square and the big square are.
-/
def leftSquareIsPullback (H : IsLimit (PullbackCone.mk _ _ h₂))
    (H' :
      IsLimit
        (PullbackCone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
            -- 🎉 no goals
    IsLimit (PullbackCone.mk _ _ h₁) := by
  fapply PullbackCone.isLimitAux'
  -- ⊢ (s : PullbackCone g₁ i₂) → { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ f …
  intro s
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ f₁ h₁) = PullbackCone.fst s  …
  have : s.fst ≫ g₁ ≫ g₂ = (s.snd ≫ f₂) ≫ i₃ := by
    rw [← Category.assoc, s.condition, Category.assoc, Category.assoc, h₂]
  rcases PullbackCone.IsLimit.lift' H' s.fst (s.snd ≫ f₂) this with ⟨l₁, hl₁, hl₁'⟩
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk i₁ f₁ h₁) = PullbackCone.fst s  …
  use l₁
  -- ⊢ l₁ ≫ PullbackCone.fst (PullbackCone.mk i₁ f₁ h₁) = PullbackCone.fst s ∧ l₁ ≫ …
  use hl₁
  -- ⊢ l₁ ≫ PullbackCone.snd (PullbackCone.mk i₁ f₁ h₁) = PullbackCone.snd s ∧ ∀ {m …
  constructor
  -- ⊢ l₁ ≫ PullbackCone.snd (PullbackCone.mk i₁ f₁ h₁) = PullbackCone.snd s
  · apply PullbackCone.IsLimit.hom_ext H
    -- ⊢ (l₁ ≫ PullbackCone.snd (PullbackCone.mk i₁ f₁ h₁)) ≫ PullbackCone.fst (Pullb …
    · erw [Category.assoc, ← h₁, ← Category.assoc, hl₁, s.condition]
      -- ⊢ PullbackCone.snd s ≫ i₂ = PullbackCone.snd s ≫ PullbackCone.fst (PullbackCon …
      rfl
      -- 🎉 no goals
    · erw [Category.assoc, hl₁']
      -- ⊢ PullbackCone.snd s ≫ f₂ = PullbackCone.snd s ≫ PullbackCone.snd (PullbackCon …
      rfl
      -- 🎉 no goals
  · intro m hm₁ hm₂
    -- ⊢ m = l₁
    apply PullbackCone.IsLimit.hom_ext H'
    -- ⊢ m ≫ PullbackCone.fst (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ …
    · erw [hm₁, hl₁]
      -- 🎉 no goals
    · erw [hl₁', ← hm₂]
      -- ⊢ m ≫ PullbackCone.snd (PullbackCone.mk i₁ (f₁ ≫ f₂) (_ : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ …
      exact (Category.assoc _ _ _).symm
      -- 🎉 no goals
#align category_theory.limits.left_square_is_pullback CategoryTheory.Limits.leftSquareIsPullback

/-- Given

X₁ - f₁ -> X₂ - f₂ -> X₃
|          |          |
i₁         i₂         i₃
∨          ∨          ∨
Y₁ - g₁ -> Y₂ - g₂ -> Y₃

Then the right square is a pushout if the left square and the big square are.
-/
def rightSquareIsPushout (H : IsColimit (PushoutCocone.mk _ _ h₁))
    (H' :
      IsColimit
        (PushoutCocone.mk _ _
          (show i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ by
            rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]))) :
            -- 🎉 no goals
    IsColimit (PushoutCocone.mk _ _ h₂) := by
  fapply PushoutCocone.isColimitAux'
  -- ⊢ (s : PushoutCocone i₂ f₂) → { l // PushoutCocone.inl (PushoutCocone.mk g₂ i₃ …
  intro s
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk g₂ i₃ h₂) ≫ l = PushoutCocone.inl …
  have : i₁ ≫ g₁ ≫ s.inl = (f₁ ≫ f₂) ≫ s.inr := by
    rw [Category.assoc, ← s.condition, ← Category.assoc, ← Category.assoc, h₁]
  rcases PushoutCocone.IsColimit.desc' H' (g₁ ≫ s.inl) s.inr this with ⟨l₁, hl₁, hl₁'⟩
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk g₂ i₃ h₂) ≫ l = PushoutCocone.inl …
  dsimp at *
  -- ⊢ { l // g₂ ≫ l = PushoutCocone.inl s ∧ i₃ ≫ l = PushoutCocone.inr s ∧ ∀ {m :  …
  use l₁
  -- ⊢ g₂ ≫ l₁ = PushoutCocone.inl s ∧ i₃ ≫ l₁ = PushoutCocone.inr s ∧ ∀ {m : Y₃ ⟶  …
  refine' ⟨_, _, _⟩
  · apply PushoutCocone.IsColimit.hom_ext H
    -- ⊢ PushoutCocone.inl (PushoutCocone.mk g₁ i₂ h₁) ≫ g₂ ≫ l₁ = PushoutCocone.inl  …
    · erw [← Category.assoc, hl₁]
      -- ⊢ g₁ ≫ PushoutCocone.inl s = PushoutCocone.inl (PushoutCocone.mk g₁ i₂ h₁) ≫ P …
      rfl
      -- 🎉 no goals
    · erw [← Category.assoc, h₂, Category.assoc, hl₁', s.condition]
      -- 🎉 no goals
  · exact hl₁'
    -- 🎉 no goals
  · intro m hm₁ hm₂
    -- ⊢ m = l₁
    apply PushoutCocone.IsColimit.hom_ext H'
    -- ⊢ PushoutCocone.inl (PushoutCocone.mk (g₁ ≫ g₂) i₃ (_ : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f …
    · erw [hl₁, Category.assoc, hm₁]
      -- 🎉 no goals
    · erw [hm₂, hl₁']
      -- 🎉 no goals
#align category_theory.limits.right_square_is_pushout CategoryTheory.Limits.rightSquareIsPushout

end PasteLemma

section

variable (f : X ⟶ Z) (g : Y ⟶ Z) (f' : W ⟶ X)

variable [HasPullback f g] [HasPullback f' (pullback.fst : pullback f g ⟶ _)]

variable [HasPullback (f' ≫ f) g]

/-- The canonical isomorphism `W ×[X] (X ×[Z] Y) ≅ W ×[Z] Y` -/
noncomputable def pullbackRightPullbackFstIso :
    pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g := by
  let this :=
    bigSquareIsPullback (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _)
      pullback.snd f' f pullback.fst pullback.fst g pullback.condition pullback.condition
      (pullbackIsPullback _ _) (pullbackIsPullback _ _)
  exact (this.conePointUniqueUpToIso (pullbackIsPullback _ _) : _)
  -- 🎉 no goals
#align category_theory.limits.pullback_right_pullback_fst_iso CategoryTheory.Limits.pullbackRightPullbackFstIso

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_fst :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_hom_snd :
    (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_hom_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst = pullback.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_snd :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.right
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_snd CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd

@[reassoc (attr := simp)]
theorem pullbackRightPullbackFstIso_inv_snd_fst :
    (pullbackRightPullbackFstIso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' := by
  rw [← pullback.condition]
  -- ⊢ (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst ≫ f' = pullback.fst  …
  exact pullbackRightPullbackFstIso_inv_fst_assoc _ _ _ _
  -- 🎉 no goals
#align category_theory.limits.pullback_right_pullback_fst_iso_inv_snd_fst CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst

end

section

variable (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)

variable [HasPushout f g] [HasPushout (pushout.inr : _ ⟶ pushout f g) g']

variable [HasPushout f (g ≫ g')]

/-- The canonical isomorphism `(Y ⨿[X] Z) ⨿[Z] W ≅ Y ×[X] W` -/
noncomputable def pushoutLeftPushoutInrIso :
    pushout (pushout.inr : _ ⟶ pushout f g) g' ≅ pushout f (g ≫ g') :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).coconePointUniqueUpToIso
      (pushoutIsPushout _ _) :
    _)
#align category_theory.limits.pushout_left_pushout_inr_iso CategoryTheory.Limits.pushoutLeftPushoutInrIso

@[reassoc (attr := simp)]
theorem inl_pushoutLeftPushoutInrIso_inv :
    pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inl ≫ pushout.inl :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_inv
      (pushoutIsPushout _ _) WalkingSpan.left :
    _)
#align category_theory.limits.inl_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inl_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inr :=
  ((bigSquareIsPushout g g' _ _ f _ _ pushout.condition pushout.condition (pushoutIsPushout _ _)
          (pushoutIsPushout _ _)).comp_coconePointUniqueUpToIso_hom
      (pushoutIsPushout _ _) WalkingSpan.right :
    _)
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_pushoutLeftPushoutInrIso_inv :
    pushout.inr ≫ (pushoutLeftPushoutInrIso f g g').inv = pushout.inr := by
  rw [Iso.comp_inv_eq, inr_pushoutLeftPushoutInrIso_hom]
  -- 🎉 no goals
#align category_theory.limits.inr_pushout_left_pushout_inr_iso_inv CategoryTheory.Limits.inr_pushoutLeftPushoutInrIso_inv

@[reassoc (attr := simp)]
theorem inl_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inl ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = pushout.inl := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, inl_pushoutLeftPushoutInrIso_inv]
  -- 🎉 no goals
#align category_theory.limits.inl_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inl_inl_pushoutLeftPushoutInrIso_hom

@[reassoc (attr := simp)]
theorem inr_inl_pushoutLeftPushoutInrIso_hom :
    pushout.inr ≫ pushout.inl ≫ (pushoutLeftPushoutInrIso f g g').hom = g' ≫ pushout.inr := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, Category.assoc, inr_pushoutLeftPushoutInrIso_inv,
    pushout.condition]
#align category_theory.limits.inr_inl_pushout_left_pushout_inr_iso_hom CategoryTheory.Limits.inr_inl_pushoutLeftPushoutInrIso_hom

end

section PullbackAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pullbacks.

We can then construct the pullback squares

W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂

and

W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)

variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

-- include f₁ f₂ f₃ f₄ Porting note: removed

local notation "Z₁" => pullback f₁ f₂

local notation "Z₂" => pullback f₃ f₄

local notation "g₁" => (pullback.fst : Z₁ ⟶ X₁)

local notation "g₂" => (pullback.snd : Z₁ ⟶ X₂)

local notation "g₃" => (pullback.fst : Z₂ ⟶ X₂)

local notation "g₄" => (pullback.snd : Z₂ ⟶ X₃)

local notation "W" => pullback (g₂ ≫ f₃) f₄

local notation "W'" => pullback f₁ (g₃ ≫ f₂)

local notation "l₁" => (pullback.fst : W ⟶ Z₁)

local notation "l₂" =>
  (pullback.lift (pullback.fst ≫ g₂) pullback.snd
      (Eq.trans (Category.assoc _ _ _) pullback.condition) :
    W ⟶ Z₂)

local notation "l₁'" =>
  (pullback.lift pullback.fst (pullback.snd ≫ g₃)
      (pullback.condition.trans (Eq.symm (Category.assoc _ _ _))) :
    W' ⟶ Z₁)

local notation "l₂'" => (pullback.snd : W' ⟶ Z₂)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone.mk l₁ l₂
    (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply leftSquareIsPullback
  exact pullbackIsPullback f₃ f₄
  -- ⊢ IsLimit (PullbackCone.mk pullback.fst (pullback.lift (pullback.fst ≫ pullbac …
  convert pullbackIsPullback (g₂ ≫ f₃) f₄
  -- ⊢ pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd (_ : (pullback.fst  …
  rw [pullback.lift_snd]
  -- 🎉 no goals
#align category_theory.limits.pullback_pullback_left_is_pullback CategoryTheory.Limits.pullbackPullbackLeftIsPullback

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
          -- 🎉 no goals
  apply PullbackCone.flipIsLimit
  -- ⊢ IsLimit (PullbackCone.mk (pullback.lift (pullback.fst ≫ pullback.snd) pullba …
  apply bigSquareIsPullback
  · apply PullbackCone.flipIsLimit
    -- ⊢ IsLimit (PullbackCone.mk pullback.fst ?t.i₂ (_ : pullback.fst ≫ f₁ = ?t.i₂ ≫ …
    exact pullbackIsPullback f₁ f₂
    -- 🎉 no goals
  · apply PullbackCone.flipIsLimit
    -- ⊢ IsLimit (PullbackCone.mk pullback.fst (pullback.lift (pullback.fst ≫ pullbac …
    apply pullbackPullbackLeftIsPullback
    -- 🎉 no goals
  · exact pullback.lift_fst _ _ _
    -- 🎉 no goals
  · exact pullback.condition.symm
    -- 🎉 no goals
#align category_theory.limits.pullback_assoc_is_pullback CategoryTheory.Limits.pullbackAssocIsPullback

theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc CategoryTheory.Limits.hasPullback_assoc

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply PullbackCone.flipIsLimit
  -- ⊢ IsLimit (PullbackCone.mk pullback.snd (pullback.lift pullback.fst (pullback. …
  apply leftSquareIsPullback
  · apply PullbackCone.flipIsLimit
    -- ⊢ IsLimit (PullbackCone.mk ?t.f₂ pullback.snd (_ : ?t.f₂ ≫ ?t.i₃ = pullback.sn …
    exact pullbackIsPullback f₁ f₂
    -- 🎉 no goals
  · apply PullbackCone.flipIsLimit
    -- ⊢ IsLimit (PullbackCone.mk (pullback.lift pullback.fst (pullback.snd ≫ pullbac …
    convert pullbackIsPullback f₁ (g₃ ≫ f₂)
    -- ⊢ pullback.lift pullback.fst (pullback.snd ≫ pullback.fst) (_ : pullback.fst ≫ …
    rw [pullback.lift_fst]
    -- 🎉 no goals
  · exact pullback.condition.symm
    -- 🎉 no goals
#align category_theory.limits.pullback_pullback_right_is_pullback CategoryTheory.Limits.pullbackPullbackRightIsPullback

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
          -- 🎉 no goals
  apply bigSquareIsPullback
  exact pullbackIsPullback f₃ f₄
  -- ⊢ IsLimit (PullbackCone.mk (pullback.lift pullback.fst (pullback.snd ≫ pullbac …
  apply pullbackPullbackRightIsPullback
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_symm_is_pullback CategoryTheory.Limits.pullbackAssocSymmIsPullback

theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩
#align category_theory.limits.has_pullback_assoc_symm CategoryTheory.Limits.hasPullback_assoc_symm

/- Porting note : these don't seem to be propagating change from
-- variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ (g₃ ≫ f₂)] -/
variable [HasPullback (g₂ ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)]

/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
noncomputable def pullbackAssoc [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)
#align category_theory.limits.pullback_assoc CategoryTheory.Limits.pullbackAssoc

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_fst_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)]:
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst := by
  trans l₁' ≫ pullback.fst
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.lif …
  rw [← Category.assoc]
  -- ⊢ ((pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst) ≫ pullback.fst = pullback.l …
  congr 1
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst = pullback.lift pullback.fst  …
  exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
  -- ⊢ pullback.lift pullback.fst (pullback.snd ≫ pullback.fst) (_ : pullback.fst ≫ …
  exact pullback.lift_fst _ _ _
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_inv_fst_fst CategoryTheory.Limits.pullbackAssoc_inv_fst_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst = pullback.fst ≫ pullback.fst := by
  rw [← Iso.eq_inv_comp, pullbackAssoc_inv_fst_fst]
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_hom_fst CategoryTheory.Limits.pullbackAssoc_hom_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_snd_fst [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫
    pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  trans l₂ ≫ pullback.fst
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.fst = pullback.lif …
  rw [← Category.assoc]
  -- ⊢ ((pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd) ≫ pullback.fst = pullback.l …
  congr 1
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd = pullback.lift (pullback.fst …
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  -- ⊢ pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd (_ : (pullback.fst  …
  exact pullback.lift_fst _ _ _
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_hom_snd_fst CategoryTheory.Limits.pullbackAssoc_hom_snd_fst

@[reassoc (attr := simp)]
theorem pullbackAssoc_hom_snd_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  trans l₂ ≫ pullback.snd
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.lif …
  rw [← Category.assoc]
  -- ⊢ ((pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd) ≫ pullback.snd = pullback.l …
  congr 1
  -- ⊢ (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd = pullback.lift (pullback.fst …
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  -- ⊢ pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd (_ : (pullback.fst  …
  exact pullback.lift_snd _ _ _
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_hom_snd_snd CategoryTheory.Limits.pullbackAssoc_hom_snd_snd

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_fst_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst :=
  by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]
     -- 🎉 no goals
#align category_theory.limits.pullback_assoc_inv_fst_snd CategoryTheory.Limits.pullbackAssoc_inv_fst_snd

@[reassoc (attr := simp)]
theorem pullbackAssoc_inv_snd [HasPullback ((pullback.snd : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_snd]
  -- 🎉 no goals
#align category_theory.limits.pullback_assoc_inv_snd CategoryTheory.Limits.pullbackAssoc_inv_snd

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁

where the two squares are pushouts.

We can then construct the pushout squares

Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)

variable (g₄ : Z₂ ⟶ X₃) [HasPushout g₁ g₂] [HasPushout g₃ g₄]

-- include g₁ g₂ g₃ g₄ Porting note: removed

local notation "Y₁" => pushout g₁ g₂

local notation "Y₂" => pushout g₃ g₄

local notation "f₁" => (pushout.inl : X₁ ⟶ Y₁)

local notation "f₂" => (pushout.inr : X₂ ⟶ Y₁)

local notation "f₃" => (pushout.inl : X₂ ⟶ Y₂)

local notation "f₄" => (pushout.inr : X₃ ⟶ Y₂)

local notation "W" => pushout g₁ (g₂ ≫ f₃)

local notation "W'" => pushout (g₃ ≫ f₂) g₄

local notation "l₁" =>
  (pushout.desc pushout.inl (f₃ ≫ pushout.inr) (pushout.condition.trans (Category.assoc _ _ _)) :
    Y₁ ⟶ W)

local notation "l₂" => (pushout.inr : Y₂ ⟶ W)

local notation "l₁'" => (pushout.inl : Y₁ ⟶ W')

local notation "l₂'" =>
  (pushout.desc (f₂ ≫ pushout.inl) pushout.inr
      (Eq.trans (Eq.symm (Category.assoc _ _ _)) pushout.condition) :
    Y₂ ⟶ W')

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) := by
  apply PushoutCocone.flipIsColimit
  -- ⊢ IsColimit (PushoutCocone.mk (pushout.desc (pushout.inr ≫ pushout.inl) pushou …
  apply rightSquareIsPushout
  · apply PushoutCocone.flipIsColimit
    -- ⊢ IsColimit (PushoutCocone.mk pushout.inl ?t.g₁ (_ : ?t.f₁ ≫ pushout.inl = ?t. …
    exact pushoutIsPushout _ _
    -- 🎉 no goals
  · apply PushoutCocone.flipIsColimit
    -- ⊢ IsColimit (PushoutCocone.mk pushout.inl (pushout.inr ≫ pushout.desc (pushout …
    convert pushoutIsPushout (g₃ ≫ f₂) g₄
    -- ⊢ pushout.inr ≫ pushout.desc (pushout.inr ≫ pushout.inl) pushout.inr (_ : g₃ ≫ …
    exact pushout.inr_desc _ _ _
    -- 🎉 no goals
  · exact pushout.condition.symm
    -- 🎉 no goals
#align category_theory.limits.pushout_pushout_left_is_pushout CategoryTheory.Limits.pushoutPushoutLeftIsPushout

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [Category.assoc, pushout.inl_desc, pushout.condition_assoc])) := by
          -- 🎉 no goals
  apply bigSquareIsPushout
  · apply pushoutPushoutLeftIsPushout
    -- 🎉 no goals
  · exact pushoutIsPushout _ _
    -- 🎉 no goals
#align category_theory.limits.pushout_assoc_is_pushout CategoryTheory.Limits.pushoutAssocIsPushout

theorem hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc CategoryTheory.Limits.hasPushout_assoc

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) := by
  apply rightSquareIsPushout
  · exact pushoutIsPushout _ _
    -- 🎉 no goals
  · convert pushoutIsPushout g₁ (g₂ ≫ f₃)
    -- ⊢ pushout.inl ≫ pushout.desc pushout.inl (pushout.inl ≫ pushout.inr) (_ : g₁ ≫ …
    rw [pushout.inl_desc]
    -- 🎉 no goals
#align category_theory.limits.pushout_pushout_right_is_pushout CategoryTheory.Limits.pushoutPushoutRightIsPushout

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [Category.assoc, pushout.inr_desc, pushout.condition_assoc])) := by
          -- 🎉 no goals
  apply PushoutCocone.flipIsColimit
  -- ⊢ IsColimit (PushoutCocone.mk (pushout.inr ≫ pushout.inr) (pushout.desc pushou …
  apply bigSquareIsPushout
  · apply PushoutCocone.flipIsColimit
    -- ⊢ IsColimit (PushoutCocone.mk (pushout.desc pushout.inl (pushout.inl ≫ pushout …
    apply pushoutPushoutRightIsPushout
    -- 🎉 no goals
  · apply PushoutCocone.flipIsColimit
    -- ⊢ IsColimit (PushoutCocone.mk pushout.inl pushout.inr (_ : g₃ ≫ pushout.inl =  …
    exact pushoutIsPushout _ _
    -- 🎉 no goals
  · exact pushout.condition.symm
    -- 🎉 no goals
  · exact (pushout.inr_desc _ _ _).symm
    -- 🎉 no goals
#align category_theory.limits.pushout_assoc_symm_is_pushout CategoryTheory.Limits.pushoutAssocSymmIsPushout

theorem hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩
#align category_theory.limits.has_pushout_assoc_symm CategoryTheory.Limits.hasPushout_assoc_symm

-- Porting note: these are not propagating so moved into statements
-- variable [HasPushout (g₃ ≫ f₂) g₄] [HasPushout g₁ (g₂ ≫ f₃)]

/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
noncomputable def pushoutAssoc [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))]:
    pushout (g₃ ≫ pushout.inr : _ ⟶ pushout g₁ g₂) g₄ ≅
      pushout g₁ (g₂ ≫ pushout.inl : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)
#align category_theory.limits.pushout_assoc CategoryTheory.Limits.pushoutAssoc

@[reassoc (attr := simp)]
theorem inl_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl := by
  trans f₁ ≫ l₁
  -- ⊢ pushout.inl ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl ≫ p …
  · congr 1
    -- ⊢ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.desc pushout.inl (pus …
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inl_desc _ _ _
    -- 🎉 no goals
#align category_theory.limits.inl_inl_pushout_assoc_hom CategoryTheory.Limits.inl_inl_pushoutAssoc_hom

@[reassoc (attr := simp)]
theorem inr_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl ≫ pushout.inr := by
  trans f₂ ≫ l₁
  -- ⊢ pushout.inr ≫ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inr ≫ p …
  · congr 1
    -- ⊢ pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.desc pushout.inl (pus …
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inr_desc _ _ _
    -- 🎉 no goals
#align category_theory.limits.inr_inl_pushout_assoc_hom CategoryTheory.Limits.inr_inl_pushoutAssoc_hom

@[reassoc (attr := simp)]
theorem inr_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr := by
  trans f₄ ≫ l₂'
  -- ⊢ pushout.inr ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ p …
  · congr 1
    -- ⊢ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.desc (pushout.inr ≫ p …
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄) WalkingCospan.right
  · exact pushout.inr_desc _ _ _
    -- 🎉 no goals
#align category_theory.limits.inr_inr_pushout_assoc_inv CategoryTheory.Limits.inr_inr_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inl_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl ≫ pushout.inl := by
  rw [Iso.comp_inv_eq, Category.assoc, inl_inl_pushoutAssoc_hom]
  -- 🎉 no goals
#align category_theory.limits.inl_pushout_assoc_inv CategoryTheory.Limits.inl_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inl_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inl ≫ pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr ≫ pushout.inl := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, inr_inl_pushoutAssoc_hom]
  -- 🎉 no goals
#align category_theory.limits.inl_inr_pushout_assoc_inv CategoryTheory.Limits.inl_inr_pushoutAssoc_inv

@[reassoc (attr := simp)]
theorem inr_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl : X₂ ⟶ Y₂))] :
    pushout.inr ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inr ≫ pushout.inr := by
  rw [← Iso.eq_comp_inv, Category.assoc, inr_inr_pushoutAssoc_inv]
  -- 🎉 no goals
#align category_theory.limits.inr_pushout_assoc_hom CategoryTheory.Limits.inr_pushoutAssoc_hom

end PushoutAssoc

variable (C)

/-- `HasPullbacks` represents a choice of pullback for every pair of morphisms

See <https://stacks.math.columbia.edu/tag/001W>
-/
abbrev HasPullbacks :=
  HasLimitsOfShape WalkingCospan C
#align category_theory.limits.has_pullbacks CategoryTheory.Limits.HasPullbacks

/-- `HasPushouts` represents a choice of pushout for every pair of morphisms -/
abbrev HasPushouts :=
  HasColimitsOfShape WalkingSpan C
#align category_theory.limits.has_pushouts CategoryTheory.Limits.HasPushouts

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem hasPullbacks_of_hasLimit_cospan
    [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, HasLimit (cospan f g)] : HasPullbacks C :=
  { has_limit := fun F => hasLimitOfIso (diagramIsoCospan F).symm }
#align category_theory.limits.has_pullbacks_of_has_limit_cospan CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem hasPushouts_of_hasColimit_span
    [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g)] : HasPushouts C :=
  { has_colimit := fun F => hasColimitOfIso (diagramIsoSpan F) }
#align category_theory.limits.has_pushouts_of_has_colimit_span CategoryTheory.Limits.hasPushouts_of_hasColimit_span

/-- The duality equivalence `WalkingSpanᵒᵖ ≌ WalkingCospan` -/
@[simps!]
def walkingSpanOpEquiv : WalkingSpanᵒᵖ ≌ WalkingCospan :=
  widePushoutShapeOpEquiv _
#align category_theory.limits.walking_span_op_equiv CategoryTheory.Limits.walkingSpanOpEquiv

/-- The duality equivalence `WalkingCospanᵒᵖ ≌ WalkingSpan` -/
@[simps!]
def walkingCospanOpEquiv : WalkingCospanᵒᵖ ≌ WalkingSpan :=
  widePullbackShapeOpEquiv _
#align category_theory.limits.walking_cospan_op_equiv CategoryTheory.Limits.walkingCospanOpEquiv

-- see Note [lower instance priority]
/-- Having wide pullback at any universe level implies having binary pullbacks. -/
instance (priority := 100) hasPullbacks_of_hasWidePullbacks (D : Type u) [h : Category.{v} D]
    [h' : HasWidePullbacks.{w} D] : HasPullbacks.{v,u} D := by
  haveI I := @hasWidePullbacks_shrink.{0, w} D h h'
  -- ⊢ HasPullbacks D
  infer_instance
  -- 🎉 no goals
#align category_theory.limits.has_pullbacks_of_has_wide_pullbacks CategoryTheory.Limits.hasPullbacks_of_hasWidePullbacks

-- see Note [lower instance priority]
/-- Having wide pushout at any universe level implies having binary pushouts. -/
instance (priority := 100) hasPushouts_of_hasWidePushouts (D : Type u) [h : Category.{v} D]
    [h' : HasWidePushouts.{w} D] : HasPushouts.{v,u} D := by
  haveI I := @hasWidePushouts_shrink.{0, w} D h h'
  -- ⊢ HasPushouts D
  infer_instance
  -- 🎉 no goals

variable {C}

-- Porting note: removed semireducible from the simps config
/-- Given a morphism `f : X ⟶ Y`, we can take morphisms over `Y` to morphisms over `X` via
pullbacks. This is right adjoint to `over.map` (TODO) -/
@[simps! (config := { simpRhs := true}) obj_left obj_hom map_left]
def baseChange [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd : pullback g.hom f ⟶ _)
  map i := Over.homMk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp))
                                                                   -- 🎉 no goals
                                                                             -- 🎉 no goals
  map_id Z := by
    apply Over.OverMorphism.ext; apply pullback.hom_ext
    -- ⊢ ({ obj := fun g => Over.mk pullback.snd, map := fun {X_1 Y_1} i => Over.homM …
                                 -- ⊢ ({ obj := fun g => Over.mk pullback.snd, map := fun {X_1 Y_1} i => Over.homM …
    · dsimp; simp
      -- ⊢ pullback.map Z.hom f Z.hom f (𝟙 Z.left) (𝟙 X) (𝟙 Y) (_ : Z.hom ≫ 𝟙 Y = 𝟙 Z.l …
             -- 🎉 no goals
    · dsimp; simp
      -- ⊢ pullback.map Z.hom f Z.hom f (𝟙 Z.left) (𝟙 X) (𝟙 Y) (_ : Z.hom ≫ 𝟙 Y = 𝟙 Z.l …
             -- 🎉 no goals
  map_comp f g := by
    apply Over.OverMorphism.ext; apply pullback.hom_ext
    -- ⊢ ({ obj := fun g => Over.mk pullback.snd, map := fun {X_1 Y_1} i => Over.homM …
                                 -- ⊢ ({ obj := fun g => Over.mk pullback.snd, map := fun {X_1 Y_1} i => Over.homM …
    · dsimp; simp
      -- ⊢ pullback.map X✝.hom f✝ Z✝.hom f✝ (f.left ≫ g.left) (𝟙 X) (𝟙 Y) (_ : X✝.hom ≫ …
             -- 🎉 no goals
    · dsimp; simp
      -- ⊢ pullback.map X✝.hom f✝ Z✝.hom f✝ (f.left ≫ g.left) (𝟙 X) (𝟙 Y) (_ : X✝.hom ≫ …
             -- 🎉 no goals
#align category_theory.limits.base_change CategoryTheory.Limits.baseChange

end CategoryTheory.Limits
