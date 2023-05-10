/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.sites.cover_preserving
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.Flat
import Mathbin.CategoryTheory.Sites.Sheaf
import Mathbin.Tactic.ApplyFun

/-!
# Cover-preserving functors between sites.

We define cover-preserving functors between sites as functors that push covering sieves to
covering sieves. A cover-preserving and compatible-preserving functor `G : C ⥤ D` then pulls
sheaves on `D` back to sheaves on `C` via `G.op ⋙ -`.

## Main definitions

* `category_theory.cover_preserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves
* `category_theory.compatible_preserving`: a functor between sites is compatible-preserving
if it pushes compatible families of elements to compatible families.
* `category_theory.pullback_sheaf`: the pullback of a sheaf along a cover-preserving and
compatible-preserving functor.
* `category_theory.sites.pullback`: the induced functor `Sheaf K A ⥤ Sheaf J A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.

## Main results

- `category_theory.sites.whiskering_left_is_sheaf_of_cover_preserving`: If `G : C ⥤ D` is
cover-preserving and compatible-preserving, then `G ⋙ -` (`uᵖ`) as a functor
`(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WW

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {A : Type u₃} [Category.{v₃} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology A}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.pushforward_functor G` is a covering sieve in `D`.
-/
@[nolint has_nonempty_instance]
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (hS : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)
#align category_theory.cover_preserving CategoryTheory.CoverPreserving

/-- The identity functor on a site is cover-preserving. -/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun U S hS => by simpa using hS⟩
#align category_theory.id_cover_preserving CategoryTheory.idCoverPreserving

variable (J) (K)

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun U S hS => by
    rw [sieve.functor_pushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩
#align category_theory.cover_preserving.comp CategoryTheory.CoverPreserving.comp

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functor_pushforward` used.
-/
@[nolint has_nonempty_instance]
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  Compatible :
    ∀ (ℱ : SheafOfTypes.{w} K) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T}
      (h : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (eq : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
#align category_theory.compatible_preserving CategoryTheory.CompatiblePreserving

variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : SheafOfTypes.{w} K) {Z : C}

variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T} (h : x.Compatible)

include h hG

/-- `compatible_preserving` functors indeed preserve compatible families. -/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible :=
  by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold family_of_elements.functor_pushforward
  rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices : ℱ.val.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.val.map (g₂ ≫ h₂).op (x f₂ hf₂)
  simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using Eq
#align category_theory.presieve.family_of_elements.compatible.functor_pushforward CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPushforward

@[simp]
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf :=
  by
  unfold family_of_elements.functor_pushforward
  rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.compatible ℱ h f' (𝟙 _) hg hf (by simp [Eq])
#align category_theory.compatible_preserving.apply_map CategoryTheory.CompatiblePreserving.apply_map

omit h hG

open Limits.WalkingCospan

theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G :=
  by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : cone (cospan g₁ g₂ ⋙ G) :=
    (cones.postcompose (diagram_iso_cospan (cospan g₁ g₂ ⋙ G)).inv).obj (pullback_cone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `structured_arrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := is_cofiltered.cone (structured_arrow_cone.to_diagram c ⋙ structured_arrow.pre _ _ _)
  have eq₁ : f₁ = (c'.X.hom ≫ G.map (c'.π.app left).right) ≫ eq_to_hom (by simp) :=
    by
    erw [← (c'.π.app left).w]
    dsimp
    simp
  have eq₂ : f₂ = (c'.X.hom ≫ G.map (c'.π.app right).right) ≫ eq_to_hom (by simp) :=
    by
    erw [← (c'.π.app right).w]
    dsimp
    simp
  conv_lhs => rw [eq₁]
  conv_rhs => rw [eq₂]
  simp only [op_comp, functor.map_comp, types_comp_apply, eq_to_hom_op, eq_to_hom_map]
  congr 1
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality walking_cospan.hom.inl with _ e₁
  injection c'.π.naturality walking_cospan.hom.inr with _ e₂
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)
#align category_theory.compatible_preserving_of_flat CategoryTheory.compatiblePreservingOfFlat

theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [Full F] [Faithful F]
    (hF : ∀ {c : C} {d : D} (f : d ⟶ F.obj c), Σc', F.obj c' ≅ d) : CompatiblePreserving K F :=
  by
  constructor
  introv hx he
  obtain ⟨X', e⟩ := hF f₁
  apply (ℱ.1.mapIso e.op).toEquiv.Injective
  simp only [iso.op_hom, iso.to_equiv_fun, ℱ.1.mapIso_hom, ← functor_to_types.map_comp_apply]
  simpa using
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using he)
#align category_theory.compatible_preserving_of_downwards_closed CategoryTheory.compatiblePreservingOfDownwardsClosed

/-- If `G` is cover-preserving and compatible-preserving,
then `G.op ⋙ _` pulls sheaves back to sheaves.

This result is basically <https://stacks.math.columbia.edu/tag/00WW>.
-/
theorem pullback_isSheaf_of_coverPreserving {G : C ⥤ D} (hG₁ : CompatiblePreserving.{v₃} K G)
    (hG₂ : CoverPreserving J K G) (ℱ : Sheaf K A) : Presheaf.IsSheaf J (G.op ⋙ ℱ.val) :=
  by
  intro X U S hS x hx
  change family_of_elements (G.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) _ at x
  let H := ℱ.2 X _ (hG₂.cover_preserve hS)
  let hx' := hx.functor_pushforward hG₁ (sheaf_over ℱ X)
  constructor; swap
  · apply H.amalgamate (x.functor_pushforward G)
    exact hx'
  constructor
  · intro V f hf
    convert H.is_amalgamation hx' (G.map f) (image_mem_functor_pushforward G S hf)
    rw [hG₁.apply_map (sheaf_over ℱ X) hx]
  · intro y hy
    refine'
      H.is_separated_for _ y _ _ (H.is_amalgamation (hx.functor_pushforward hG₁ (sheaf_over ℱ X)))
    rintro V f ⟨Z, f', g', h, rfl⟩
    erw [family_of_elements.comp_of_compatible (S.functor_pushforward G) hx'
        (image_mem_functor_pushforward G S h) g']
    dsimp
    simp [hG₁.apply_map (sheaf_over ℱ X) hx h, ← hy f' h]
#align category_theory.pullback_is_sheaf_of_cover_preserving CategoryTheory.pullback_isSheaf_of_coverPreserving

/-- The pullback of a sheaf along a cover-preserving and compatible-preserving functor. -/
def pullbackSheaf {G : C ⥤ D} (hG₁ : CompatiblePreserving K G) (hG₂ : CoverPreserving J K G)
    (ℱ : Sheaf K A) : Sheaf J A :=
  ⟨G.op ⋙ ℱ.val, pullback_isSheaf_of_coverPreserving hG₁ hG₂ ℱ⟩
#align category_theory.pullback_sheaf CategoryTheory.pullbackSheaf

variable (A)

/-- The induced functor from `Sheaf K A ⥤ Sheaf J A` given by `G.op ⋙ _`
if `G` is cover-preserving and compatible-preserving.
-/
@[simps]
def Sites.pullback {G : C ⥤ D} (hG₁ : CompatiblePreserving K G) (hG₂ : CoverPreserving J K G) :
    Sheaf K A ⥤ Sheaf J A where
  obj ℱ := pullbackSheaf hG₁ hG₂ ℱ
  map _ _ f := ⟨((whiskeringLeft _ _ _).obj G.op).map f.val⟩
  map_id' ℱ := by
    ext1
    apply ((whiskering_left _ _ _).obj G.op).map_id
  map_comp' _ _ _ f g := by
    ext1
    apply ((whiskering_left _ _ _).obj G.op).map_comp
#align category_theory.sites.pullback CategoryTheory.Sites.pullback

end CategoryTheory

