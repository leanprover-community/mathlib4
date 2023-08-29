/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.CategoryTheory.Sites.CoverPreserving

#align_import category_theory.sites.cover_lifting from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Cover-lifting functors between sites.

We define cover-lifting functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cocontinuous functors* or
*cover-reflecting functors*, but we have chosen this name following [MM92] in order to avoid
potential naming collision or confusion with the general definition of cocontinuous functors
between categories as functors preserving small colimits.

The definition given here seems stronger than the definition found elsewhere,
but they are actually equivalent via `CategoryTheory.GrothendieckTopology.superset_covering`.
(The precise statement is not formalized, but follows from it quite trivially).

## Main definitions

* `CategoryTheory.CoverLifting`: a functor between sites is cover-lifting if it
  pulls back covering sieves to covering sieves
* `CategoryTheory.Sites.copullback`: A cover-lifting functor `G : (C, J) ⥤ (D, K)` induces a
  morphism of sites in the same direction as the functor.

## Main results
* `CategoryTheory.ran_isSheaf_of_coverLifting`: If `G : C ⥤ D` is cover_lifting, then
  `Ran G.op` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Sites.pullbackCopullbackAdjunction`: If `G : (C, J) ⥤ (D, K)` is cover-lifting,
  cover-preserving, and compatible-preserving, then `pullback G` and `copullback G` are adjoint.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/


universe w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

section CoverLifting

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology E}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called to have the cover-lifting property
if for all covering sieves `R` in `D`, `R.pullback G` is a covering sieve in `C`.
-/
-- porting note: removed `@[nolint has_nonempty_instance]`
structure CoverLifting (G : C ⥤ D) : Prop where
  cover_lift : ∀ {U : C} {S : Sieve (G.obj U)} (_ : S ∈ K (G.obj U)), S.functorPullback G ∈ J U
#align category_theory.cover_lifting CategoryTheory.CoverLifting

/-- The identity functor on a site is cover-lifting. -/
theorem idCoverLifting : CoverLifting J J (𝟭 _) :=
  ⟨fun h => by simpa using h⟩
               -- 🎉 no goals
#align category_theory.id_cover_lifting CategoryTheory.idCoverLifting

variable {J K}

/-- The composition of two cover-lifting functors are cover-lifting -/
theorem compCoverLifting {F : C ⥤ D} (hu : CoverLifting J K F) {G : D ⥤ E}
    (hv : CoverLifting K L G) : CoverLifting J L (F ⋙ G) :=
  ⟨fun h => hu.cover_lift (hv.cover_lift h)⟩
#align category_theory.comp_cover_lifting CategoryTheory.compCoverLifting

end CoverLifting

/-!
We will now prove that `Ran G.op` (`ₚu`) maps sheaves to sheaves if `G` is cover-lifting. This can
be found in <https://stacks.math.columbia.edu/tag/00XK>. However, the proof given here uses the
amalgamation definition of sheaves, and thus does not require that `C` or `D` has categorical
pullbacks.

For the following proof sketch, `⊆` denotes the homs on `C` and `D` as in the topological analogy.
By definition, the presheaf `𝒢 : Dᵒᵖ ⥤ A` is a sheaf if for every sieve `S` of `U : D`, and every
compatible family of morphisms `X ⟶ 𝒢(V)` for each `V ⊆ U : S` with a fixed source `X`,
we can glue them into a morphism `X ⟶ 𝒢(U)`.

Since the presheaf `𝒢 := (Ran G.op).obj ℱ.val` is defined via `𝒢(U) = lim_{G(V) ⊆ U} ℱ(V)`, for
gluing the family `x` into a `X ⟶ 𝒢(U)`, it suffices to provide a `X ⟶ ℱ(Y)` for each
`G(Y) ⊆ U`. This can be done since `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}` is a covering sieve for `Y` on
`C` (by the cover-lifting property of `G`). Thus the morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` can be
glued into a morphism `X ⟶ ℱ(Y)`. This is done in `get_sections`.

In `glued_limit_cone`, we verify these obtained sections are indeed compatible, and thus we obtain
A `X ⟶ 𝒢(U)`. The remaining work is to verify that this is indeed the amalgamation and is unique.
-/


variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable {A : Type w} [Category.{max u v} A] [HasLimits A]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace RanIsSheafOfCoverLifting

variable {G : C ⥤ D} (hu : CoverLifting J K G) (ℱ : Sheaf J A)

variable {X : A} {U : D} (S : Sieve U) (hS : S ∈ K U)

instance (X : Dᵒᵖ) : HasLimitsOfShape (StructuredArrow X G.op) A :=
  haveI := Limits.hasLimitsOfSizeShrink.{v, max u v, max u v, max u v} A
  HasLimitsOfSize.has_limits_of_shape _

variable (x : S.arrows.FamilyOfElements ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)))

variable (hx : x.Compatible)

/-- The family of morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` defined on `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}`. -/
def pulledbackFamily (Y : StructuredArrow (op U) G.op) :=
  ((x.pullback Y.hom.unop).functorPullback G).compPresheafMap
    (show _ ⟶ _ from whiskerRight ((Ran.adjunction A G.op).counit.app ℱ.val) (coyoneda.obj (op X)))
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family CategoryTheory.RanIsSheafOfCoverLifting.pulledbackFamily

@[simp]
theorem pulledbackFamily_apply (Y : StructuredArrow (op U) G.op) {W} {f : W ⟶ _} (Hf) :
    pulledbackFamily ℱ S x Y f Hf =
      x (G.map f ≫ Y.hom.unop) Hf ≫ ((Ran.adjunction A G.op).counit.app ℱ.val).app (op W) :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family_apply CategoryTheory.RanIsSheafOfCoverLifting.pulledbackFamily_apply

variable {x} {S}

-- porting note: no longer needed
-- include hu hS hx

/-- Given a `G(Y) ⊆ U`, we can find a unique section `X ⟶ ℱ(Y)` that agrees with `x`. -/
def getSection (Y : StructuredArrow (op U) G.op) : X ⟶ ℱ.val.obj Y.right := by
  letI hom_sh := whiskerRight ((Ran.adjunction A G.op).counit.app ℱ.val) (coyoneda.obj (op X))
  -- ⊢ X ⟶ ℱ.val.obj Y.right
  haveI S' := K.pullback_stable Y.hom.unop hS
  -- ⊢ X ⟶ ℱ.val.obj Y.right
  haveI hs' := ((hx.pullback Y.3.unop).functorPullback G).compPresheafMap hom_sh
  -- ⊢ X ⟶ ℱ.val.obj Y.right
  exact (ℱ.2 X _ (hu.cover_lift S')).amalgamate _ hs'
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section CategoryTheory.RanIsSheafOfCoverLifting.getSection

theorem getSection_isAmalgamation (Y : StructuredArrow (op U) G.op) :
    (pulledbackFamily ℱ S x Y).IsAmalgamation (getSection hu ℱ hS hx Y) :=
  IsSheafFor.isAmalgamation _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_amalgamation CategoryTheory.RanIsSheafOfCoverLifting.getSection_isAmalgamation

theorem getSection_is_unique (Y : StructuredArrow (op U) G.op) {y}
    (H : (pulledbackFamily ℱ S x Y).IsAmalgamation y) : y = getSection hu ℱ hS hx Y := by
  apply IsSheafFor.isSeparatedFor _ (pulledbackFamily ℱ S x Y)
  · exact H
    -- 🎉 no goals
  · apply getSection_isAmalgamation
    -- 🎉 no goals
  · exact ℱ.2 X _ (hu.cover_lift (K.pullback_stable Y.hom.unop hS))
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_unique CategoryTheory.RanIsSheafOfCoverLifting.getSection_is_unique

@[simp]
theorem getSection_commute {Y Z : StructuredArrow (op U) G.op} (f : Y ⟶ Z) :
    getSection hu ℱ hS hx Y ≫ ℱ.val.map f.right = getSection hu ℱ hS hx Z := by
  apply getSection_is_unique
  -- ⊢ IsAmalgamation (pulledbackFamily ℱ S x Z) (getSection hu ℱ hS hx Y ≫ ℱ.val.m …
  intro V' fV' hV'
  -- ⊢ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV'.op (getSection hu ℱ  …
  have eq : Z.hom = Y.hom ≫ (G.map f.right.unop).op := by
    convert f.w
    erw [Category.id_comp]
  rw [eq] at hV'
  -- ⊢ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV'.op (getSection hu ℱ  …
  convert getSection_isAmalgamation hu ℱ hS hx Y (fV' ≫ f.right.unop) _ using 1
  · aesop_cat
    -- 🎉 no goals
  -- porting note: the below proof was mildly rewritten because `simp` changed behaviour
  -- slightly (a rewrite which seemed to work in Lean 3, didn't work in Lean 4 because of
  -- motive is not type correct issues)
  · rw [pulledbackFamily_apply, pulledbackFamily_apply]
    · congr 2
      -- ⊢ G.map fV' ≫ Z.hom.unop = G.map (fV' ≫ f.right.unop) ≫ Y.hom.unop
      simp [eq]
      -- 🎉 no goals
    · change S (G.map _ ≫ Y.hom.unop)
      -- ⊢ S.arrows (G.map (fV' ≫ f.right.unop) ≫ Y.hom.unop)
      simpa only [Functor.map_comp, Category.assoc] using hV'
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_commute CategoryTheory.RanIsSheafOfCoverLifting.getSection_commute

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
def gluedLimitCone : Limits.Cone (Ran.diagram G.op ℱ.val (op U)) :=
  { pt := X -- porting note: autoporter got this wrong
    π := { app := fun Y => getSection hu ℱ hS hx Y } }
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone CategoryTheory.RanIsSheafOfCoverLifting.gluedLimitCone

@[simp]
theorem gluedLimitCone_π_app (W) : (gluedLimitCone hu ℱ hS hx).π.app W = getSection hu ℱ hS hx W :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone_π_app CategoryTheory.RanIsSheafOfCoverLifting.gluedLimitCone_π_app

/-- The section obtained by passing `glued_limit_cone` into `CategoryTheory.Limits.limit.lift`. -/
def gluedSection : X ⟶ ((ran G.op).obj ℱ.val).obj (op U) :=
  limit.lift _ (gluedLimitCone hu ℱ hS hx)
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section CategoryTheory.RanIsSheafOfCoverLifting.gluedSection

/--
A helper lemma for the following two lemmas. Basically stating that if the section `y : X ⟶ 𝒢(V)`
coincides with `x` on `G(V')` for all `G(V') ⊆ V ∈ S`, then `X ⟶ 𝒢(V) ⟶ ℱ(W)` is indeed the
section obtained in `get_sections`. That said, this is littered with some more categorical jargon
in order to be applied in the following lemmas easier.
-/
theorem helper {V} (f : V ⟶ U) (y : X ⟶ ((ran G.op).obj ℱ.val).obj (op V)) (W)
    (H : ∀ {V'} {fV : G.obj V' ⟶ V} (hV), y ≫ ((ran G.op).obj ℱ.val).map fV.op = x (fV ≫ f) hV) :
    y ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W =
      (gluedLimitCone hu ℱ hS hx).π.app ((StructuredArrow.map f.op).obj W) := by
  dsimp only [gluedLimitCone_π_app]
  -- ⊢ y ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W = getSection hu ℱ hS hx ((Stru …
  apply getSection_is_unique hu ℱ hS hx ((StructuredArrow.map f.op).obj W)
  -- ⊢ IsAmalgamation (pulledbackFamily ℱ S x ((StructuredArrow.map f.op).obj W)) ( …
  intro V' fV' hV'
  -- ⊢ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV'.op (y ≫ limit.π (Ran …
  dsimp only [Ran.adjunction, Ran.equiv, pulledbackFamily_apply]
  -- ⊢ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV'.op (y ≫ limit.π (Ran …
  erw [Adjunction.adjunctionOfEquivRight_counit_app]
  -- ⊢ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV'.op (y ≫ limit.π (Ran …
  have :
    y ≫ ((ran G.op).obj ℱ.val).map (G.map fV' ≫ W.hom.unop).op =
      x (G.map fV' ≫ W.hom.unop ≫ f) (by simpa only using hV') := by
    convert H (show S ((G.map fV' ≫ W.hom.unop) ≫ f) by simpa only [Category.assoc] using hV')
      using 2
    simp only [Category.assoc]
  simp only [Quiver.Hom.unop_op, Equiv.symm_symm, StructuredArrow.map_obj_hom, unop_comp,
    Equiv.coe_fn_mk, Functor.comp_map, coyoneda_obj_map, Category.assoc, ← this, op_comp,
    ran_obj_map, NatTrans.id_app]
  erw [Category.id_comp, limit.pre_π]
  -- ⊢ y ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W ≫ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val).ma …
  congr
  -- ⊢ limit.π (Ran.diagram G.op ℱ.val (op V)) W ≫ ((𝟭 (Cᵒᵖ ⥤ A)).obj ℱ.val).map fV …
  convert limit.w (Ran.diagram G.op ℱ.val (op V)) (StructuredArrow.homMk' W fV'.op)
  -- ⊢ (StructuredArrow.map (W.hom.unop.op ≫ (G.map fV').op)).obj (StructuredArrow. …
  rw [StructuredArrow.map_mk]
  -- ⊢ StructuredArrow.mk ((W.hom.unop.op ≫ (G.map fV').op) ≫ 𝟙 (G.op.obj (op V'))) …
  erw [Category.comp_id]
  -- ⊢ StructuredArrow.mk (W.hom.unop.op ≫ (G.map fV').op) = StructuredArrow.mk (W. …
  simp only [Quiver.Hom.unop_op, Functor.op_map, Quiver.Hom.op_unop]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.helper CategoryTheory.RanIsSheafOfCoverLifting.helper

/-- Verify that the `glued_section` is an amalgamation of `x`. -/
theorem gluedSection_isAmalgamation : x.IsAmalgamation (gluedSection hu ℱ hS hx) := by
  intro V fV hV
  -- ⊢ ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV.op (gluedSection hu ℱ hS …
  -- porting note: next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  refine limit.hom_ext (λ (W : StructuredArrow (op V) G.op) => ?_)
  -- ⊢ ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)).map fV.op (gluedSection hu ℱ hS …
  simp only [Functor.comp_map, limit.lift_pre, coyoneda_obj_map, ran_obj_map, gluedSection]
  -- ⊢ limit.lift (StructuredArrow.map fV.op ⋙ Ran.diagram G.op ℱ.val (op U)) (Cone …
  erw [limit.lift_π]
  -- ⊢ NatTrans.app (Cone.whisker (StructuredArrow.map fV.op) (gluedLimitCone hu ℱ  …
  symm
  -- ⊢ x fV hV ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W = NatTrans.app (Cone.whi …
  convert helper hu ℱ hS hx _ (x fV hV) _ _ using 1
  -- ⊢ ∀ {V' : C} {fV_1 : G.obj V' ⟶ V} (hV_1 : S.arrows (fV_1 ≫ fV)), x fV hV ≫ (( …
  intro V' fV' hV'
  -- ⊢ x fV hV ≫ ((ran G.op).obj ℱ.val).map fV'.op = x (fV' ≫ fV) hV'
  convert hx fV' (𝟙 _) hV hV' (by rw [Category.id_comp])
  -- ⊢ x (fV' ≫ fV) hV' = ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)).map (𝟙 (G.ob …
  simp only [op_id, FunctorToTypes.map_id_apply]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_amalgamation CategoryTheory.RanIsSheafOfCoverLifting.gluedSection_isAmalgamation

/-- Verify that the amalgamation is indeed unique. -/
theorem gluedSection_is_unique (y) (hy : x.IsAmalgamation y) : y = gluedSection hu ℱ hS hx := by
  unfold gluedSection limit.lift
  -- ⊢ y = IsLimit.lift (limit.isLimit (Ran.diagram G.op ℱ.val (op U))) (gluedLimit …
  -- porting note: next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  refine limit.hom_ext (λ (W : StructuredArrow (op U) G.op) => ?_)
  -- ⊢ y ≫ limit.π (Ran.diagram G.op ℱ.val (op U)) W = IsLimit.lift (limit.isLimit  …
  erw [limit.lift_π]
  -- ⊢ y ≫ limit.π (Ran.diagram G.op ℱ.val (op U)) W = NatTrans.app (gluedLimitCone …
  convert helper hu ℱ hS hx (𝟙 _) y W _
  -- ⊢ W = (StructuredArrow.map (𝟙 U).op).obj W
  · simp only [op_id, StructuredArrow.map_id]
    -- 🎉 no goals
  · intro V' fV' hV'
    -- ⊢ y ≫ ((ran G.op).obj ℱ.val).map fV'.op = x (fV' ≫ 𝟙 U) hV'
    convert hy fV' (by simpa only [Category.comp_id] using hV')
    -- ⊢ fV' ≫ 𝟙 U = fV'
    erw [Category.comp_id]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_unique CategoryTheory.RanIsSheafOfCoverLifting.gluedSection_is_unique

end RanIsSheafOfCoverLifting

/-- If `G` is cover_lifting, then `Ran G.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem ran_isSheaf_of_coverLifting {G : C ⥤ D} (hG : CoverLifting J K G) (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K ((ran G.op).obj ℱ.val) := by
  intro X U S hS x hx
  -- ⊢ ∃! t, IsAmalgamation x t
  constructor; swap
  -- ⊢ (fun t => IsAmalgamation x t) ?w ∧ ∀ (y : ((ran G.op).obj ℱ.val ⋙ coyoneda.o …
               -- ⊢ ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)).obj (op U)
  · apply RanIsSheafOfCoverLifting.gluedSection hG ℱ hS hx
    -- 🎉 no goals
  constructor
  -- ⊢ (fun t => IsAmalgamation x t) (RanIsSheafOfCoverLifting.gluedSection hG ℱ hS …
  · apply RanIsSheafOfCoverLifting.gluedSection_isAmalgamation
    -- 🎉 no goals
  · apply RanIsSheafOfCoverLifting.gluedSection_is_unique
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting CategoryTheory.ran_isSheaf_of_coverLifting

variable (A)

/-- A cover-lifting functor induces a morphism of sites in the same direction as the functor. -/
def Sites.copullback {G : C ⥤ D} (hG : CoverLifting J K G) : Sheaf J A ⥤ Sheaf K A where
  obj ℱ := ⟨(ran G.op).obj ℱ.val, ran_isSheaf_of_coverLifting hG ℱ⟩
  map f := ⟨(ran G.op).map f.val⟩
  map_id ℱ := Sheaf.Hom.ext _ _ <| (ran G.op).map_id ℱ.val
  map_comp f g := Sheaf.Hom.ext _ _ <| (ran G.op).map_comp f.val g.val
#align category_theory.sites.copullback CategoryTheory.Sites.copullback

/--
Given a functor between sites that is cover-preserving, cover-lifting, and compatible-preserving,
the pullback and copullback along `G` are adjoint to each other
-/
@[simps unit_app_val counit_app_val]
noncomputable def Sites.pullbackCopullbackAdjunction {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CoverLifting J K G) (Hc : CompatiblePreserving K G) :
    Sites.pullback A Hc Hp ⊣ Sites.copullback A Hl where
  homEquiv X Y :=
    { toFun := fun f => ⟨(Ran.adjunction A G.op).homEquiv X.val Y.val f.val⟩
      invFun := fun f => ⟨((Ran.adjunction A G.op).homEquiv X.val Y.val).symm f.val⟩
      left_inv := fun f => by
        ext1
        -- ⊢ ((fun f => { val := ↑(Adjunction.homEquiv (Ran.adjunction A G.op) X.val Y.va …
        dsimp
        -- ⊢ ↑(Adjunction.homEquiv (Ran.adjunction A G.op) X.val Y.val).symm (↑(Adjunctio …
        rw [Equiv.symm_apply_apply]
        -- 🎉 no goals
      right_inv := fun f => by
        ext1
        -- ⊢ ((fun f => { val := ↑(Adjunction.homEquiv (Ran.adjunction A G.op) X.val Y.va …
        dsimp
        -- ⊢ ↑(Adjunction.homEquiv (Ran.adjunction A G.op) X.val Y.val) (↑(Adjunction.hom …
        rw [Equiv.apply_symm_apply] }
        -- 🎉 no goals
  unit :=
    { app := fun X => ⟨(Ran.adjunction A G.op).unit.app X.val⟩
      naturality := fun _ _ f =>
        Sheaf.Hom.ext _ _ <| (Ran.adjunction A G.op).unit.naturality f.val }
  counit :=
    { app := fun X => ⟨(Ran.adjunction A G.op).counit.app X.val⟩
      naturality := fun _ _ f =>
        Sheaf.Hom.ext _ _ <| (Ran.adjunction A G.op).counit.naturality f.val }
  homEquiv_unit := by
    -- porting note: next line was `ext1`
    refine Sheaf.Hom.ext _ _ ?_
    -- ⊢ (↑((fun X Y => { toFun := fun f => { val := ↑(Adjunction.homEquiv (Ran.adjun …
    apply (Ran.adjunction A G.op).homEquiv_unit
    -- 🎉 no goals
  homEquiv_counit := by
    -- porting note: next line was `ext1`
    refine Sheaf.Hom.ext _ _ ?_
    -- ⊢ (↑((fun X Y => { toFun := fun f => { val := ↑(Adjunction.homEquiv (Ran.adjun …
    apply (Ran.adjunction A G.op).homEquiv_counit
    -- 🎉 no goals
#align category_theory.sites.pullback_copullback_adjunction CategoryTheory.Sites.pullbackCopullbackAdjunction

namespace Sites

variable
  [ConcreteCategory.{max v u} A]
  [PreservesLimits (forget A)]
  [ReflectsIsomorphisms (forget A)]
  [∀ (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)]
  [∀ (X : C), HasColimitsOfShape (J.Cover X)ᵒᵖ A]
  [∀ (X : D), PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget A)]
  [∀ (X : D), HasColimitsOfShape (K.Cover X)ᵒᵖ A]

/-- The natural isomorphism exhibiting compatibility between pullback and sheafification. -/
def pullbackSheafificationCompatibility
    {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CoverLifting J K G) (Hc : CompatiblePreserving K G) :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ pullback A Hc Hp :=
  letI A1 : (whiskeringLeft _ _ A).obj G.op ⊣ _ := Ran.adjunction _ _
  letI A2 : presheafToSheaf J A ⊣ _ := sheafificationAdjunction _ _
  letI B1 : presheafToSheaf K A ⊣ _ := sheafificationAdjunction _ _
  letI B2 : pullback A Hc Hp ⊣ _ := pullbackCopullbackAdjunction _ _ Hl _
  letI A12 := A1.comp A2
  letI B12 := B1.comp B2
  A12.leftAdjointUniq B12

/- Implementation: This is primarily used to prove the lemma
`pullbackSheafificationCompatibility_hom_app_val`. -/
lemma toSheafify_pullbackSheafificationCompatibility
    {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CoverLifting J K G) (Hc : CompatiblePreserving K G) (F) :
    J.toSheafify (G.op ⋙ F) ≫
    ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).hom.app F).val =
    whiskerLeft _ (K.toSheafify _) := by
  dsimp [pullbackSheafificationCompatibility, Adjunction.leftAdjointUniq]
  -- ⊢ GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ (coyoneda.preimage (NatTrans. …
  apply Quiver.Hom.op_inj
  -- ⊢ (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ (coyoneda.preimage (NatTrans …
  apply coyoneda.map_injective
  -- ⊢ coyoneda.map (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ (coyoneda.preim …
  ext E : 2
  -- ⊢ NatTrans.app (coyoneda.map (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ ( …
  dsimp [Functor.preimage, Full.preimage, coyoneda, Adjunction.leftAdjointsCoyonedaEquiv]
  -- ⊢ (fun g => (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ (↑(Adjunction.homE …
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
  -- ⊢ (fun g => (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ (((whiskeringLeft  …
  dsimp [Adjunction.comp]
  -- ⊢ (fun g => (GrothendieckTopology.toSheafify J (G.op ⋙ F) ≫ GrothendieckTopolo …
  simp only [sheafificationAdjunction_unit_app, Category.comp_id, Functor.map_id,
    whiskerLeft_id', GrothendieckTopology.sheafifyMap_comp,
    GrothendieckTopology.sheafifyMap_sheafifyLift, Category.id_comp,
    Category.assoc, GrothendieckTopology.toSheafify_sheafifyLift]
  ext t s : 3
  -- ⊢ NatTrans.app (whiskerLeft G.op (GrothendieckTopology.toSheafify K F) ≫ whisk …
  dsimp [pullbackSheaf]
  -- ⊢ NatTrans.app (GrothendieckTopology.toSheafify K F) (op (G.obj s.unop)) ≫ Nat …
  congr 1
  -- ⊢ NatTrans.app (NatTrans.app (Ran.adjunction A G.op).unit (GrothendieckTopolog …
  simp only [← Category.assoc]
  -- ⊢ (NatTrans.app (NatTrans.app (Ran.adjunction A G.op).unit (GrothendieckTopolo …
  convert Category.id_comp (obj := A) _
  -- ⊢ NatTrans.app (NatTrans.app (Ran.adjunction A G.op).unit (GrothendieckTopolog …
  have := (Ran.adjunction A G.op).left_triangle
  -- ⊢ NatTrans.app (NatTrans.app (Ran.adjunction A G.op).unit (GrothendieckTopolog …
  apply_fun (fun e => (e.app (K.sheafify F)).app s) at this
  -- ⊢ NatTrans.app (NatTrans.app (Ran.adjunction A G.op).unit (GrothendieckTopolog …
  exact this
  -- 🎉 no goals

@[simp]
lemma pullbackSheafificationCompatibility_hom_app_val
    {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CoverLifting J K G) (Hc : CompatiblePreserving K G) (F : Dᵒᵖ ⥤ A) :
    ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).hom.app F).val =
    J.sheafifyLift (whiskerLeft G.op <| K.toSheafify F)
      ((presheafToSheaf K A ⋙ pullback A Hc Hp).obj F).cond := by
  apply J.sheafifyLift_unique
  -- ⊢ GrothendieckTopology.toSheafify J (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj …
  apply toSheafify_pullbackSheafificationCompatibility
  -- 🎉 no goals

end Sites

end CategoryTheory
