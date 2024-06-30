/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
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
variable {A : Type w} [Category.{w'} A] --[∀ X, HasLimitsOfShape (StructuredArrow X G.op) A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsCocontinuous J K]
variable [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]

namespace RanIsSheafOfIsCocontinuous

variable {G}
variable {X : D} (S : K.Cover X) {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)
variable {R : Dᵒᵖ ⥤ A} {α : G.op ⋙ R ⟶ F}
variable (hR : (Functor.RightExtension.mk _ α).IsPointwiseRightKanExtension)

-- should be moved
def _root_.CategoryTheory.Presheaf.IsSheaf.isLimitMultifork {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F) {X : C} (S : J.Cover X) : IsLimit (S.multifork F) := by
  rw [Presheaf.isSheaf_iff_multifork] at hF
  exact (hF X S).some

section

variable (s : Multifork (S.index R))

variable {S} in
def liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y) :=
  Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k ↦ s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      have := hR
      sorry)

variable {S} in
lemma liftAux_fac {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
    (h : G.obj W ⟶ i.Y) (w : h ≫ i.f = G.map g ≫ f) :
    liftAux hF hR s f ≫ F.map g.op = s.ι i ≫ R.map h.op ≫ α.app _ := by
  sorry

def lift : s.pt ⟶ R.obj (op X) :=
  (hR (op X)).lift (Cone.mk _
    { app := fun j ↦ liftAux hF hR s j.hom.unop
      naturality := fun j j' φ ↦ by
        dsimp
        simp only [Category.id_comp]
        sorry })

@[simp]
lemma fac (i : S.Arrow) : lift S hF hR s ≫ R.map i.f.op = s.ι i := by
  sorry

variable (K) in
lemma hom_ext {W : A} {f g : W ⟶ R.obj (op X)}
    (h : ∀ (i : S.Arrow), f ≫ R.map i.f.op = g ≫ R.map i.f.op) : f = g := by
  have := hF
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    Functor.op_map, Quiver.Hom.unop_op]
  rw [reassoc_of% eq]

end

def isLimitMultifork : IsLimit (S.multifork R) :=
  Multifork.IsLimit.mk _ (lift S hF hR) (fac S hF hR)
    (fun s _ hm ↦ hom_ext K S hF hR (fun i ↦ (hm i).trans (fac S hF hR s i).symm))

end RanIsSheafOfIsCocontinuous

/-namespace RanIsSheafOfIsCocontinuous

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
  -- Porting note (#11041): next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
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
  -- Porting note (#11041): next line was `ext W`
  -- Now `ext` can't see that `ran` is defined as a limit.
  refine limit.hom_ext (fun (W : StructuredArrow (op U) G.op) ↦ ?_)
  erw [limit.lift_π]
  convert helper ℱ hS hx (𝟙 _) y W _
  · simp only [op_id, StructuredArrow.map_id]
  · intro V' fV' hV'
    convert hy fV' (by simpa only [Category.comp_id] using hV')
    erw [Category.comp_id]
set_option linter.uppercaseLean3 false in
#align category_theory.Ran_is_sheaf_of_cover_lifting.glued_section_is_unique CategoryTheory.RanIsSheafOfIsCocontinuous.gluedSection_is_unique

end RanIsSheafOfIsCocontinuous-/

variable (K)

/-- If `G` is cocontinuous, then `G.op.ran` pushes sheaves to sheaves.

This is SGA 4 III 2.2. An alternative reference is
https://stacks.math.columbia.edu/tag/00XK (where results
are obtained under the additional assumption that
`C` and `D` have pullbacks.
-/
theorem ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K ((G.op.ran).obj ℱ.val) := by
  rw [Presheaf.isSheaf_iff_multifork]
  intros X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork S ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.val)⟩
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

/-- `G.sheafPushforwardCocontinuous A J K : Sheaf J A ⥤ Sheaf K A` is induced
by the right Kan extension functor `G.op.ran` on presheaves. -/
@[simps! hom inv]
def Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso :
    G.sheafPushforwardCocontinuous A J K ⋙ sheafToPresheaf K A ≅
      sheafToPresheaf J A ⋙ G.op.ran := Iso.refl _

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

namespace Functor

variable [G.IsCocontinuous J K] [G.IsContinuous J K]

/--
Given a functor between sites that is continuous and cocontinuous,
the pushforward for the continuous functor `G` is left adjoint to
the pushforward for the cocontinuous functor `G`. -/
noncomputable def sheafAdjunctionCocontinuous :
    G.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardCocontinuous A J K :=
  (G.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm
#align category_theory.sites.pullback_copullback_adjunction CategoryTheory.Functor.sheafAdjunctionCocontinuous

lemma sheafAdjunctionCocontinuous_unit_app_val (F : Sheaf K A) :
    ((G.sheafAdjunctionCocontinuous A J K).unit.app F).val =
      (G.op.ranAdjunction A).unit.app F.val := by
  apply ((G.op.ranAdjunction A).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
  dsimp
  erw [Functor.map_id]
  change _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.comp_id]

lemma sheafAdjunctionCocontinuous_counit_app_val (F : Sheaf J A) :
    ((G.sheafAdjunctionCocontinuous A J K).counit.app F).val =
      (G.op.ranAdjunction A).counit.app F.val :=
  ((G.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans (by simp)

lemma sheafAdjunctionCocontinuous_homEquiv_apply_val {F : Sheaf K A} {H : Sheaf J A}
    (f : (G.sheafPushforwardContinuous A J K).obj F ⟶ H) :
    ((G.sheafAdjunctionCocontinuous A J K).homEquiv F H f).val =
      (G.op.ranAdjunction A).homEquiv F.val H.val f.val :=
  ((sheafToPresheaf K A).congr_map
    (((G.op.ranAdjunction A).restrictFullyFaithful_homEquiv_apply
      (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
      (G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
      (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm f))).trans (by
        dsimp
        erw [Functor.map_id, Category.comp_id, Category.id_comp,
          Adjunction.homEquiv_unit])

variable
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [G.IsCocontinuous J K] [G.IsContinuous J K]

/-- The natural isomorphism exhibiting compatibility between pushforward and sheafification. -/
def pushforwardContinuousSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K :=
  ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

-- should be moved
section

variable {E : Type u₃} [ℰ : Category.{v₃} E] {F₁ : C ⥤ D} {F₂ : D ⥤ E}
  {G₁ : D ⥤ C} {G₂ : E ⥤ D} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂)

@[simp, reassoc]
lemma _root_.CategoryTheory.Adjunction.comp_unit_app (X : C) :
    (adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G₁.map (adj₂.unit.app (F₁.obj X)) := by
  simp [Adjunction.comp]

@[simp, reassoc]
lemma _root_.CategoryTheory.Adjunction.comp_counit_app (X : E) :
    (adj₁.comp adj₂).counit.app X = F₂.map (adj₁.counit.app (G₂.obj X)) ≫ adj₂.counit.app X := by
  simp [Adjunction.comp]

end

/- Implementation: This is primarily used to prove the lemma
`pullbackSheafificationCompatibility_hom_app_val`. -/
lemma toSheafify_pullbackSheafificationCompatibility (F : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ F) ≫
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).val =
    whiskerLeft _ (toSheafify K _) := by
  let adj₁ := G.op.ranAdjunction A
  let adj₂ := sheafificationAdjunction J A
  let adj₃ := sheafificationAdjunction K A
  let adj₄ := G.sheafAdjunctionCocontinuous A J K
  change adj₂.unit.app (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).obj F) ≫
    (sheafToPresheaf J A).map (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F) =
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map (adj₃.unit.app F)
  apply (adj₁.homEquiv _ _).injective
  have eq := (adj₁.comp adj₂).unit_leftAdjointUniq_hom_app (adj₃.comp adj₄) F
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app, comp_map,
    Category.assoc] at eq
  rw [adj₁.homEquiv_unit, Functor.map_comp, eq]
  apply (adj₁.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, map_comp, Category.assoc,
    Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  congr 3
  exact G.sheafAdjunctionCocontinuous_unit_app_val A J K ((presheafToSheaf K A).obj F)

@[simp]
lemma pushforwardContinuousSheafificationCompatibility_hom_app_val (F : Dᵒᵖ ⥤ A) :
    ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app F).val =
    sheafifyLift J (whiskerLeft G.op <| toSheafify K F)
      ((presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K).obj F).cond := by
  apply sheafifyLift_unique
  apply toSheafify_pullbackSheafificationCompatibility

end Functor

end CategoryTheory
