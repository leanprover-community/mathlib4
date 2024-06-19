/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.KanExtension
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Sheafification

#align_import category_theory.sites.cover_lifting from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Cocontinuous functors between sites.

We define cocontinuous functors between sites as functors that pull covering sieves back to
covering sieves. This concept is also known as *cover-lifting* or
*cover-reflecting functors*. We use the original terminology and definition of SGA 4 III 2.1.
However, the notion of cocontinuous functor should not be confused with
the general definition of cocontinuous functors between categories as functors preserving
small colimits.

## Main definitions

* `CategoryTheory.Functor.IsCocontinuous`: a functor between sites is cocontinuous if it
  pulls back covering sieves to covering sieves
* `CategoryTheory.Functor.sheafPushforwardCocontinuous`: A cocontinuous functor
  `G : (C, J) ⥤ (D, K)` induces a functor `Sheaf J A ⥤ Sheaf K A`.

## Main results
* `CategoryTheory.ran_isSheaf_of_isCocontinuous`: If `G : C ⥤ D` is cocontinuous, then
  `Ran G.op` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Sites.pullbackCopullbackAdjunction`: If `G : (C, J) ⥤ (D, K)` is cocontinuous
  and continuous, then `G.sheafPushforwardContinuous A J K` and
  `G.sheafPushforwardCocontinuous A J K` are adjoint.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://stacks.math.columbia.edu/tag/00XI

-/


universe w' w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

section IsCocontinuous

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E] (G : C ⥤ D)
  (G' : D ⥤ E)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called cocontinuous (SGA 4 III 2.1)
if for all covering sieves `R` in `D`, `R.pullback G` is a covering sieve in `C`.
-/
-- Porting note(#5171): removed `@[nolint has_nonempty_instance]`
class Functor.IsCocontinuous : Prop where
  cover_lift : ∀ {U : C} {S : Sieve (G.obj U)} (_ : S ∈ K (G.obj U)), S.functorPullback G ∈ J U
#align category_theory.cover_lifting CategoryTheory.Functor.IsCocontinuous

lemma Functor.cover_lift [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
    (hS : S ∈ K (G.obj U)) : S.functorPullback G ∈ J U :=
  IsCocontinuous.cover_lift hS

/-- The identity functor on a site is cocontinuous. -/
instance isCocontinuous_id : Functor.IsCocontinuous (𝟭 C) J J :=
  ⟨fun h => by simpa using h⟩
#align category_theory.id_cover_lifting CategoryTheory.isCocontinuous_id

/-- The composition of two cocontinuous functors is cocontinuous. -/
theorem isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] :
    (G ⋙ G').IsCocontinuous J L where
  cover_lift h := G.cover_lift J K (G'.cover_lift K L h)
#align category_theory.comp_cover_lifting CategoryTheory.isCocontinuous_comp

end IsCocontinuous

/-!
We will now prove that `Ran G.op` (`ₚu`) maps sheaves to sheaves if `G`
is cocontinuous (SGA 4 III 2.2). This can also be be found in
<https://stacks.math.columbia.edu/tag/00XK>. However, the proof given there uses the
amalgamation definition of sheaves, and thus does not require that `C` or `D` has categorical
pullbacks.

For the following proof sketch, `⊆` denotes the homs on `C` and `D` as in the topological analogy.
By definition, the presheaf `𝒢 : Dᵒᵖ ⥤ A` is a sheaf if for every sieve `S` of `U : D`, and every
compatible family of morphisms `X ⟶ 𝒢(V)` for each `V ⊆ U : S` with a fixed source `X`,
we can glue them into a morphism `X ⟶ 𝒢(U)`.

Since the presheaf `𝒢 := (Ran G.op).obj ℱ.val` is defined via `𝒢(U) = lim_{G(V) ⊆ U} ℱ(V)`, for
gluing the family `x` into a `X ⟶ 𝒢(U)`, it suffices to provide a `X ⟶ ℱ(Y)` for each
`G(Y) ⊆ U`. This can be done since `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}` is a covering sieve for `Y` on
`C` (by the cocontinuity `G`). Thus the morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` can be
glued into a morphism `X ⟶ ℱ(Y)`. This is done in `get_sections`.

In `glued_limit_cone`, we verify these obtained sections are indeed compatible, and thus we obtain
A `X ⟶ 𝒢(U)`. The remaining work is to verify that this is indeed the amalgamation and is unique.
-/

variable {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
variable {A : Type w} [Category.{w'} A] [∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [G.IsCocontinuous J K]

namespace RanIsSheafOfIsCocontinuous

variable {G}
variable (ℱ : Sheaf J A)
variable {X : A} {U : D} (S : Sieve U) (hS : S ∈ K U)

variable (x : S.arrows.FamilyOfElements ((ran G.op).obj ℱ.val ⋙ coyoneda.obj (op X)))
variable (hx : x.Compatible)

/-- The family of morphisms `X ⟶ 𝒢(G(Y')) ⟶ ℱ(Y')` defined on `{ Y' ⊆ Y : G(Y') ⊆ U ∈ S}`. -/
def pulledbackFamily (Y : StructuredArrow (op U) G.op) :=
  ((x.pullback Y.hom.unop).functorPullback G).compPresheafMap
    (show _ ⟶ _ from whiskerRight ((Ran.adjunction A G.op).counit.app ℱ.val) (coyoneda.obj (op X)))
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family CategoryTheory.RanIsSheafOfIsCocontinuous.pulledbackFamily

@[simp]
theorem pulledbackFamily_apply (Y : StructuredArrow (op U) G.op) {W} {f : W ⟶ _} (Hf) :
    pulledbackFamily ℱ S x Y f Hf =
      x (G.map f ≫ Y.hom.unop) Hf ≫ ((Ran.adjunction A G.op).counit.app ℱ.val).app (op W) :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.pulledback_family_apply CategoryTheory.RanIsSheafOfIsCocontinuous.pulledbackFamily_apply

variable {x} {S}

/-- Given a `G(Y) ⊆ U`, we can find a unique section `X ⟶ ℱ(Y)` that agrees with `x`. -/
def getSection (Y : StructuredArrow (op U) G.op) : X ⟶ ℱ.val.obj Y.right := by
  letI hom_sh := whiskerRight ((Ran.adjunction A G.op).counit.app ℱ.val) (coyoneda.obj (op X))
  haveI S' := K.pullback_stable Y.hom.unop hS
  haveI hs' := ((hx.pullback Y.3.unop).functorPullback G).compPresheafMap hom_sh
  exact (ℱ.2 X _ (G.cover_lift _ _ S')).amalgamate _ hs'
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section CategoryTheory.RanIsSheafOfIsCocontinuous.getSection

theorem getSection_isAmalgamation (Y : StructuredArrow (op U) G.op) :
    (pulledbackFamily ℱ S x Y).IsAmalgamation (getSection ℱ hS hx Y) :=
  IsSheafFor.isAmalgamation _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_amalgamation CategoryTheory.RanIsSheafOfIsCocontinuous.getSection_isAmalgamation

theorem getSection_is_unique (Y : StructuredArrow (op U) G.op) {y}
    (H : (pulledbackFamily ℱ S x Y).IsAmalgamation y) : y = getSection ℱ hS hx Y := by
  apply IsSheafFor.isSeparatedFor _ (pulledbackFamily ℱ S x Y)
  · exact H
  · apply getSection_isAmalgamation
  · exact ℱ.2 X _ (G.cover_lift _ _ (K.pullback_stable Y.hom.unop hS))
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_is_unique CategoryTheory.RanIsSheafOfIsCocontinuous.getSection_is_unique

@[simp]
theorem getSection_commute {Y Z : StructuredArrow (op U) G.op} (f : Y ⟶ Z) :
    getSection ℱ hS hx Y ≫ ℱ.val.map f.right = getSection ℱ hS hx Z := by
  apply getSection_is_unique
  intro V' fV' hV'
  have eq : Z.hom = Y.hom ≫ (G.map f.right.unop).op := by
    convert f.w using 1
    erw [Category.id_comp]
  rw [eq] at hV'
  convert getSection_isAmalgamation ℱ hS hx Y (fV' ≫ f.right.unop) _ using 1
  · aesop_cat
  -- Porting note: the below proof was mildly rewritten because `simp` changed behaviour
  -- slightly (a rewrite which seemed to work in Lean 3, didn't work in Lean 4 because of
  -- motive is not type correct issues)
  · rw [pulledbackFamily_apply, pulledbackFamily_apply]
    · congr 2
      simp [eq]
  · change S (G.map _ ≫ Y.hom.unop)
    simpa only [Functor.map_comp, Category.assoc] using hV'
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.get_section_commute CategoryTheory.RanIsSheafOfIsCocontinuous.getSection_commute

/-- The limit cone in order to glue the sections obtained via `get_section`. -/
def gluedLimitCone : Limits.Cone (Ran.diagram G.op ℱ.val (op U)) :=
  { pt := X -- Porting note: autoporter got this wrong
    π := { app := fun Y => getSection ℱ hS hx Y } }
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone CategoryTheory.RanIsSheafOfIsCocontinuous.gluedLimitCone

@[simp]
theorem gluedLimitCone_π_app (W) : (gluedLimitCone ℱ hS hx).π.app W = getSection ℱ hS hx W :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_limit_cone_π_app CategoryTheory.RanIsSheafOfIsCocontinuous.gluedLimitCone_π_app

/-- The section obtained by passing `glued_limit_cone` into `CategoryTheory.Limits.limit.lift`. -/
def gluedSection : X ⟶ ((ran G.op).obj ℱ.val).obj (op U) :=
  limit.lift _ (gluedLimitCone ℱ hS hx)
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section CategoryTheory.RanIsSheafOfIsCocontinuous.gluedSection

/--
A helper lemma for the following two lemmas. Basically stating that if the section `y : X ⟶ 𝒢(V)`
coincides with `x` on `G(V')` for all `G(V') ⊆ V ∈ S`, then `X ⟶ 𝒢(V) ⟶ ℱ(W)` is indeed the
section obtained in `get_sections`. That said, this is littered with some more categorical jargon
in order to be applied in the following lemmas easier.
-/
theorem helper {V} (f : V ⟶ U) (y : X ⟶ ((ran G.op).obj ℱ.val).obj (op V)) (W)
    (H : ∀ {V'} {fV : G.obj V' ⟶ V} (hV), y ≫ ((ran G.op).obj ℱ.val).map fV.op = x (fV ≫ f) hV) :
    y ≫ limit.π (Ran.diagram G.op ℱ.val (op V)) W =
      (gluedLimitCone ℱ hS hx).π.app ((StructuredArrow.map f.op).obj W) := by
  dsimp only [gluedLimitCone_π_app]
  apply getSection_is_unique ℱ hS hx ((StructuredArrow.map f.op).obj W)
  intro V' fV' hV'
  dsimp only [Ran.adjunction, Ran.equiv, pulledbackFamily_apply]
  erw [Adjunction.adjunctionOfEquivRight_counit_app]
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
  congr
  convert limit.w (Ran.diagram G.op ℱ.val (op V)) (StructuredArrow.homMk' W fV'.op)
  rw [StructuredArrow.map_mk]
  erw [Category.comp_id]
  simp only [Quiver.Hom.unop_op, Functor.op_map, Quiver.Hom.op_unop]
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.helper CategoryTheory.RanIsSheafOfIsCocontinuous.helper

/-- Verify that the `glued_section` is an amalgamation of `x`. -/
theorem gluedSection_isAmalgamation : x.IsAmalgamation (gluedSection ℱ hS hx) := by
  intro V fV hV
  -- Porting note: next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  refine limit.hom_ext (fun (W : StructuredArrow (op V) G.op) ↦ ?_)
  simp only [Functor.comp_map, limit.lift_pre, coyoneda_obj_map, ran_obj_map, gluedSection]
  erw [limit.lift_π]
  symm
  convert helper ℱ hS hx _ (x fV hV) _ _ using 1
  intro V' fV' hV'
  convert hx fV' (𝟙 _) hV hV' (by rw [Category.id_comp])
  simp only [op_id, FunctorToTypes.map_id_apply]
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_amalgamation CategoryTheory.RanIsSheafOfIsCocontinuous.gluedSection_isAmalgamation

/-- Verify that the amalgamation is indeed unique. -/
theorem gluedSection_is_unique (y) (hy : x.IsAmalgamation y) : y = gluedSection ℱ hS hx := by
  unfold gluedSection limit.lift
  -- Porting note: next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
  -- See https://github.com/leanprover-community/mathlib4/issues/5229
  refine limit.hom_ext (fun (W : StructuredArrow (op U) G.op) ↦ ?_)
  erw [limit.lift_π]
  convert helper ℱ hS hx (𝟙 _) y W _
  · simp only [op_id, StructuredArrow.map_id]
  · intro V' fV' hV'
    convert hy fV' (by simpa only [Category.comp_id] using hV')
    erw [Category.comp_id]
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_unique CategoryTheory.RanIsSheafOfIsCocontinuous.gluedSection_is_unique

end RanIsSheafOfIsCocontinuous

variable (K)

/-- If `G` is cocontinuous, then `Ran G.op` pushes sheaves to sheaves.

This result is basically https://stacks.math.columbia.edu/tag/00XK,
but without the condition that `C` or `D` has pullbacks.
-/
theorem ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K ((ran G.op).obj ℱ.val) := by
  intro X U S hS x hx
  constructor; swap
  · apply RanIsSheafOfIsCocontinuous.gluedSection ℱ hS hx
  constructor
  · apply RanIsSheafOfIsCocontinuous.gluedSection_isAmalgamation
  · apply RanIsSheafOfIsCocontinuous.gluedSection_is_unique
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting CategoryTheory.ran_isSheaf_of_isCocontinuous

variable (A J)

/-- A cover-lifting functor induces a pushforward functor on categories of sheaves. -/
def Functor.sheafPushforwardCocontinuous : Sheaf J A ⥤ Sheaf K A where
  obj ℱ := ⟨(ran G.op).obj ℱ.val, ran_isSheaf_of_isCocontinuous _ K ℱ⟩
  map f := ⟨(ran G.op).map f.val⟩
  map_id ℱ := Sheaf.Hom.ext _ _ <| (ran G.op).map_id ℱ.val
  map_comp f g := Sheaf.Hom.ext _ _ <| (ran G.op).map_comp f.val g.val
#align category_theory.sites.copullback CategoryTheory.Functor.sheafPushforwardCocontinuous

/-

Given a cocontinuous functor `G`, the precomposition with `G.op` induces a functor
on presheaves with leads to a "pullback" functor `Sheaf K A ⥤ Sheaf J A` (TODO: formalize
this as `G.sheafPullbackCocontinuous A J K`) using the associated sheaf functor.
It is shown in SGA 4 III 2.3 that this pullback functor is
left adjoint to `G.sheafPushforwardCocontinuous A J K`. This adjunction may replace
`Functor.sheafAdjunctionCocontinuous` below, and then, it could be shown that if
`G` is also continuous, then we have an isomorphism
`G.sheafPullbackCocontinuous A J K ≅ G.sheafPushforwardContinuous A J K` (TODO).

-/

/--
Given a functor between sites that is continuous and cocontinuous,
the pushforward for the continuous functor `G` is left adjoint to
the pushforward for the cocontinuous functor `G`. -/
@[simps unit_app_val counit_app_val]
noncomputable def Functor.sheafAdjunctionCocontinuous [G.IsCocontinuous J K]
    [G.IsContinuous J K] :
    G.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardCocontinuous A J K where
  homEquiv X Y :=
    { toFun := fun f => ⟨(Ran.adjunction A G.op).homEquiv X.val Y.val f.val⟩
      invFun := fun f => ⟨((Ran.adjunction A G.op).homEquiv X.val Y.val).symm f.val⟩
      left_inv := fun f => by
        ext1
        dsimp
        rw [Equiv.symm_apply_apply]
      right_inv := fun f => by
        ext1
        dsimp
        rw [Equiv.apply_symm_apply] }
  unit :=
    { app := fun X => ⟨(Ran.adjunction A G.op).unit.app X.val⟩
      naturality := fun _ _ f =>
        Sheaf.Hom.ext _ _ <| (Ran.adjunction A G.op).unit.naturality f.val }
  counit :=
    { app := fun X => ⟨(Ran.adjunction A G.op).counit.app X.val⟩
      naturality := fun _ _ f =>
        Sheaf.Hom.ext _ _ <| (Ran.adjunction A G.op).counit.naturality f.val }
  homEquiv_unit := by
    -- Porting note: next line was `ext1`
    refine Sheaf.Hom.ext _ _ ?_
    apply (Ran.adjunction A G.op).homEquiv_unit
  homEquiv_counit := by
    -- Porting note: next line was `ext1`
    refine Sheaf.Hom.ext _ _ ?_
    apply (Ran.adjunction A G.op).homEquiv_counit
#align category_theory.sites.pullback_copullback_adjunction CategoryTheory.Functor.sheafAdjunctionCocontinuous

variable
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsCocontinuous J K] [G.IsContinuous J K]

/-- The natural isomorphism exhibiting compatibility between pushforward and sheafification. -/
def Functor.pushforwardContinuousSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K :=
  letI A1 : (whiskeringLeft _ _ A).obj G.op ⊣ _ := Ran.adjunction _ _
  letI A2 : presheafToSheaf J A ⊣ _ := sheafificationAdjunction _ _
  letI B1 : presheafToSheaf K A ⊣ _ := sheafificationAdjunction _ _
  letI B2 := G.sheafAdjunctionCocontinuous A J K
  letI A12 := A1.comp A2
  letI B12 := B1.comp B2
  A12.leftAdjointUniq B12

/- Implementation: This is primarily used to prove the lemma
`pullbackSheafificationCompatibility_hom_app_val`. -/
lemma Functor.toSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ F) ≫
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).val =
    whiskerLeft _ (toSheafify K _) := by
  dsimp [pushforwardContinuousSheafificationCompatibility]
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom, Adjunction.natIsoEquiv_apply_inv,
    Iso.refl_inv, Adjunction.natTransEquiv_apply_app, comp_obj, whiskeringLeft_obj_obj,
    sheafToPresheaf_obj, whiskerLeft_id', Category.comp_id, comp_map, whiskeringLeft_obj_map,
    Sheaf.instCategorySheaf_comp_val]
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective
  ext E : 2
  dsimp [Functor.preimage, Coyoneda.preimage, coyoneda, Adjunction.comp]
  simp only [Category.comp_id, map_id, whiskerLeft_id', map_comp, Sheaf.instCategorySheaf_comp_val,
    sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift,
    Category.id_comp, Category.assoc, toSheafify_sheafifyLift]
  ext t s : 3
  dsimp [sheafPushforwardContinuous]
  congr 1
  simp only [← Category.assoc]
  convert Category.id_comp (obj := A) _
  have := (Ran.adjunction A G.op).left_triangle
  apply_fun (fun e => (e.app (sheafify K F)).app s) at this
  exact this

@[simp]
lemma Functor.pushforwardContinuousSheafificationCompatibility_hom_app_val (F : Dᵒᵖ ⥤ A) :
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).val =
    sheafifyLift J (whiskerLeft G.op <| toSheafify K F)
      ((presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K).obj F).cond := by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

end CategoryTheory
