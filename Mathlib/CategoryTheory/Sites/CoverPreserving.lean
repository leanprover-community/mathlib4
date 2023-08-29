/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.ApplyFun

#align_import category_theory.sites.cover_preserving from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"
/-!
# Cover-preserving functors between sites.

We define cover-preserving functors between sites as functors that push covering sieves to
covering sieves. A cover-preserving and compatible-preserving functor `G : C ⥤ D` then pulls
sheaves on `D` back to sheaves on `C` via `G.op ⋙ -`.

## Main definitions

* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
if it pushes compatible families of elements to compatible families.
* `CategoryTheory.pullbackSheaf`: the pullback of a sheaf along a cover-preserving and
compatible-preserving functor.
* `CategoryTheory.Sites.pullback`: the induced functor `Sheaf K A ⥤ Sheaf J A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.

## Main results

- `CategoryTheory.pullback_isSheaf_of_coverPreserving`: If `G : C ⥤ D` is
cover-preserving and compatible-preserving, then `G ⋙ -` (`uᵖ`) as a functor
`(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WW

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory Opposite CategoryTheory.Presieve.FamilyOfElements CategoryTheory.Presieve
  CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {A : Type u₃} [Category.{v₃} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology A}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.functorPushforward G` is a covering sieve in `D`.
-/
-- porting note: removed `@[nolint has_nonempty_instance]`
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (_ : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)
#align category_theory.cover_preserving CategoryTheory.CoverPreserving

/-- The identity functor on a site is cover-preserving. -/
theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using hS⟩
                -- 🎉 no goals
#align category_theory.id_cover_preserving CategoryTheory.idCoverPreserving

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    -- ⊢ Sieve.functorPushforward G (Sieve.functorPushforward F S✝) ∈ GrothendieckTop …
    exact hG.cover_preserve (hF.cover_preserve hS)⟩
    -- 🎉 no goals
#align category_theory.cover_preserving.comp CategoryTheory.CoverPreserving.comp

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functorPushforward` used.
-/
-- porting note: this doesn't work yet @[nolint has_nonempty_instance]
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  Compatible :
    ∀ (ℱ : SheafOfTypes.{w} K) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
#align category_theory.compatible_preserving CategoryTheory.CompatiblePreserving

variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : SheafOfTypes.{w} K) {Z : C}

variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T} (h : x.Compatible)

/-- `CompatiblePreserving` functors indeed preserve compatible families. -/
theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  -- ⊢ ℱ.val.map g₁.op (FamilyOfElements.functorPushforward G x f₁' H₁) = ℱ.val.map …
  unfold FamilyOfElements.functorPushforward
  -- ⊢ ℱ.val.map g₁.op (FunctorPushforwardStructure.casesOn (getFunctorPushforwardS …
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  -- ⊢ ℱ.val.map g₁.op (FunctorPushforwardStructure.casesOn { preobj := X₁, premap  …
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  -- ⊢ ℱ.val.map g₁.op (FunctorPushforwardStructure.casesOn { preobj := X₁, premap  …
  suffices ℱ.val.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.val.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.Compatible ℱ h _ _ hf₁ hf₂
  -- ⊢ (g₁ ≫ h₁) ≫ G.map f₁ = (g₂ ≫ h₂) ≫ G.map f₂
  simpa using eq
  -- 🎉 no goals
#align category_theory.presieve.family_of_elements.compatible.functor_pushforward CategoryTheory.Presieve.FamilyOfElements.Compatible.functorPushforward

@[simp]
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.functorPushforward G (G.map f) (image_mem_functorPushforward G T hf) = x f hf := by
  unfold FamilyOfElements.functorPushforward
  -- ⊢ (FunctorPushforwardStructure.casesOn (getFunctorPushforwardStructure (_ : Pr …
  rcases e₁ : getFunctorPushforwardStructure (image_mem_functorPushforward G T hf) with
    ⟨X, g, f', hg, eq⟩
  simpa using hG.Compatible ℱ h f' (𝟙 _) hg hf (by simp [eq])
  -- 🎉 no goals
#align category_theory.compatible_preserving.apply_map CategoryTheory.CompatiblePreserving.apply_map

open Limits.WalkingCospan

theorem compatiblePreservingOfFlat {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₁} D]
    (K : GrothendieckTopology D) (G : C ⥤ D) [RepresentablyFlat G] : CompatiblePreserving K G := by
  constructor
  -- ⊢ ∀ (ℱ : SheafOfTypes K) {Z : C} {T : Presieve Z} {x : FamilyOfElements (G.op  …
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
  -- ⊢ ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  -- First, `f₁` and `f₂` form a cone over `cospan g₁ g₂ ⋙ u`.
  let c : Cone (cospan g₁ g₂ ⋙ G) :=
    (Cones.postcompose (diagramIsoCospan (cospan g₁ g₂ ⋙ G)).inv).obj (PullbackCone.mk f₁ f₂ e)
  /-
    This can then be viewed as a cospan of structured arrows, and we may obtain an arbitrary cone
    over it since `StructuredArrow W u` is cofiltered.
    Then, it suffices to prove that it is compatible when restricted onto `u(c'.X.right)`.
    -/
  let c' := IsCofiltered.cone (c.toStructuredArrow ⋙ StructuredArrow.pre _ _ _)
  -- ⊢ ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  have eq₁ : f₁ = (c'.pt.hom ≫ G.map (c'.π.app left).right) ≫ eqToHom (by simp) := by
    erw [← (c'.π.app left).w]
    dsimp
    simp
  have eq₂ : f₂ = (c'.pt.hom ≫ G.map (c'.π.app right).right) ≫ eqToHom (by simp) := by
    erw [← (c'.π.app right).w]
    dsimp
    simp
  conv_lhs => rw [eq₁]
  -- ⊢ ℱ.val.map ((c'.pt.hom ≫ G.map (NatTrans.app c'.π left).right) ≫ eqToHom (_ : …
  conv_rhs => rw [eq₂]
  -- ⊢ ℱ.val.map ((c'.pt.hom ≫ G.map (NatTrans.app c'.π left).right) ≫ eqToHom (_ : …
  simp only [op_comp, Functor.map_comp, types_comp_apply, eqToHom_op, eqToHom_map]
  -- ⊢ ℱ.val.map (IsCofiltered.cone (Cone.toStructuredArrow ((Cones.postcompose (di …
  apply congr_arg -- porting note: was `congr 1` which for some reason doesn't do anything here
  -- ⊢ ℱ.val.map (G.map (NatTrans.app (IsCofiltered.cone (Cone.toStructuredArrow (( …
  -- despite goal being of the form f a = f b, with f=`ℱ.val.map (Quiver.Hom.op c'.pt.hom)`
  /-
    Since everything now falls in the image of `u`,
    the result follows from the compatibility of `x` in the image of `u`.
    -/
  injection c'.π.naturality WalkingCospan.Hom.inl with _ e₁
  -- ⊢ ℱ.val.map (G.map (NatTrans.app (IsCofiltered.cone (Cone.toStructuredArrow (( …
  injection c'.π.naturality WalkingCospan.Hom.inr with _ e₂
  -- ⊢ ℱ.val.map (G.map (NatTrans.app (IsCofiltered.cone (Cone.toStructuredArrow (( …
  exact hx (c'.π.app left).right (c'.π.app right).right hg₁ hg₂ (e₁.symm.trans e₂)
  -- 🎉 no goals
#align category_theory.compatible_preserving_of_flat CategoryTheory.compatiblePreservingOfFlat

theorem compatiblePreservingOfDownwardsClosed (F : C ⥤ D) [Full F] [Faithful F]
    (hF : ∀ {c : C} {d : D} (_ : d ⟶ F.obj c), Σc', F.obj c' ≅ d) : CompatiblePreserving K F := by
  constructor
  -- ⊢ ∀ (ℱ : SheafOfTypes K) {Z : C} {T : Presieve Z} {x : FamilyOfElements (F.op  …
  introv hx he
  -- ⊢ ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  obtain ⟨X', e⟩ := hF f₁
  -- ⊢ ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  apply (ℱ.1.mapIso e.op).toEquiv.injective
  -- ⊢ ↑(ℱ.val.mapIso (Iso.op e)).toEquiv (ℱ.val.map f₁.op (x g₁ hg₁)) = ↑(ℱ.val.ma …
  simp only [Iso.op_hom, Iso.toEquiv_fun, ℱ.1.mapIso_hom, ← FunctorToTypes.map_comp_apply]
  -- ⊢ ℱ.val.map (f₁.op ≫ e.hom.op) (x g₁ hg₁) = ℱ.val.map (f₂.op ≫ e.hom.op) (x g₂ …
  simpa using
    hx (F.preimage <| e.hom ≫ f₁) (F.preimage <| e.hom ≫ f₂) hg₁ hg₂
      (F.map_injective <| by simpa using he)
#align category_theory.compatible_preserving_of_downwards_closed CategoryTheory.compatiblePreservingOfDownwardsClosed

/-- If `G` is cover-preserving and compatible-preserving,
then `G.op ⋙ _` pulls sheaves back to sheaves.

This result is basically <https://stacks.math.columbia.edu/tag/00WW>.
-/
theorem pullback_isSheaf_of_coverPreserving {G : C ⥤ D} (hG₁ : CompatiblePreserving.{v₃} K G)
    (hG₂ : CoverPreserving J K G) (ℱ : Sheaf K A) : Presheaf.IsSheaf J (G.op ⋙ ℱ.val) := by
  intro X U S hS x hx
  -- ⊢ ∃! t, IsAmalgamation x t
  change FamilyOfElements (G.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) _ at x
  -- ⊢ ∃! t, IsAmalgamation x t
  let H := ℱ.2 X _ (hG₂.cover_preserve hS)
  -- ⊢ ∃! t, IsAmalgamation x t
  let hx' := hx.functorPushforward hG₁ (sheafOver ℱ X)
  -- ⊢ ∃! t, IsAmalgamation x t
  constructor; swap
  -- ⊢ (fun t => IsAmalgamation x t) ?w ∧ ∀ (y : ((G.op ⋙ ℱ.val) ⋙ coyoneda.obj (op …
               -- ⊢ ((G.op ⋙ ℱ.val) ⋙ coyoneda.obj (op X)).obj (op U)
  · apply H.amalgamate (x.functorPushforward G)
    -- ⊢ Compatible (FamilyOfElements.functorPushforward G x)
    exact hx'
    -- 🎉 no goals
  constructor
  -- ⊢ (fun t => IsAmalgamation x t) (IsSheafFor.amalgamate H (FamilyOfElements.fun …
  · intro V f hf
    -- ⊢ ((G.op ⋙ ℱ.val) ⋙ coyoneda.obj (op X)).map f.op (IsSheafFor.amalgamate H (Fa …
    convert H.isAmalgamation hx' (G.map f) (image_mem_functorPushforward G S hf)
    -- ⊢ x f hf = FamilyOfElements.functorPushforward G x (G.map f) (_ : Presieve.fun …
    rw [hG₁.apply_map (sheafOver ℱ X) hx]
    -- 🎉 no goals
  · intro y hy
    -- ⊢ y = IsSheafFor.amalgamate H (FamilyOfElements.functorPushforward G x) hx'
    refine'
      H.isSeparatedFor _ y _ _ (H.isAmalgamation (hx.functorPushforward hG₁ (sheafOver ℱ X)))
    rintro V f ⟨Z, f', g', h, rfl⟩
    -- ⊢ (ℱ.val ⋙ coyoneda.obj (op X)).map (g' ≫ G.map f').op y = FamilyOfElements.fu …
    -- porting note: didn't need coercion (S : Presieve U) in Lean 3
    erw [FamilyOfElements.comp_of_compatible (S.functorPushforward G) hx'
        (image_mem_functorPushforward G (S : Presieve U) h) g']
    dsimp
    -- ⊢ y ≫ ℱ.val.map ((G.map f').op ≫ g'.op) = FamilyOfElements.functorPushforward  …
    simp [hG₁.apply_map (sheafOver ℱ X) hx h, ← hy f' h]
    -- 🎉 no goals
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
  map f := ⟨((whiskeringLeft _ _ _).obj G.op).map f.val⟩
  map_id ℱ := by
    ext1
    -- ⊢ ({ obj := fun ℱ => pullbackSheaf hG₁ hG₂ ℱ, map := fun {X Y} f => { val := ( …
    apply ((whiskeringLeft _ _ _).obj G.op).map_id
    -- 🎉 no goals
  map_comp f g := by
    ext1
    -- ⊢ ({ obj := fun ℱ => pullbackSheaf hG₁ hG₂ ℱ, map := fun {X Y} f => { val := ( …
    apply ((whiskeringLeft _ _ _).obj G.op).map_comp
    -- 🎉 no goals
#align category_theory.sites.pullback CategoryTheory.Sites.pullback

end CategoryTheory
