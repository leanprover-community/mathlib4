/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.Sheafification

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
  `G.op.ran` (`ₚu`) as a functor `(Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.
* `CategoryTheory.Functor.sheafAdjunctionCocontinuous`: If `G : (C, J) ⥤ (D, K)` is cocontinuous
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
class Functor.IsCocontinuous : Prop where
  cover_lift : ∀ {U : C} {S : Sieve (G.obj U)} (_ : S ∈ K (G.obj U)), S.functorPullback G ∈ J U

lemma Functor.cover_lift [G.IsCocontinuous J K] {U : C} {S : Sieve (G.obj U)}
    (hS : S ∈ K (G.obj U)) : S.functorPullback G ∈ J U :=
  IsCocontinuous.cover_lift hS

/-- The identity functor on a site is cocontinuous. -/
instance isCocontinuous_id : Functor.IsCocontinuous (𝟭 C) J J :=
  ⟨fun h => by simpa using h⟩

/-- The composition of two cocontinuous functors is cocontinuous. -/
theorem isCocontinuous_comp [G.IsCocontinuous J K] [G'.IsCocontinuous K L] :
    (G ⋙ G').IsCocontinuous J L where
  cover_lift h := G.cover_lift J K (G'.cover_lift K L h)

end IsCocontinuous

/-!
We will now prove that `G.op.ran : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)` maps sheaves
to sheaves when `G : C ⥤ D` is a cocontinuous functor.

We do not follow the proofs in SGA 4 III 2.2 or <https://stacks.math.columbia.edu/tag/00XK>.
Instead, we verify as directly as possible that if `F : Cᵒᵖ ⥤ A` is a sheaf,
then `G.op.ran.obj F` is a sheaf. in order to do this, we use the "multifork"
characterization of sheaves which involves limits in the category `A`.
As `G.op.ran.obj F` is the chosen right Kan extension of `F` along `G.op : Cᵒᵖ ⥤ Dᵒᵖ`,
we actually verify that any pointwise right Kan extension of `F` along `G.op` is a sheaf.

-/

variable {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
variable {A : Type w} [Category.{w'} A]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} [G.IsCocontinuous J K]

namespace RanIsSheafOfIsCocontinuous

variable {G}
variable {F : Cᵒᵖ ⥤ A} (hF : Presheaf.IsSheaf J F)
variable {R : Dᵒᵖ ⥤ A} (α : G.op ⋙ R ⟶ F)
variable (hR : (Functor.RightExtension.mk _ α).IsPointwiseRightKanExtension)
variable {X : D} {S : K.Cover X} (s : Multifork (S.index R))

/-- Auxiliary definition for `lift`. -/
def liftAux {Y : C} (f : G.obj Y ⟶ X) : s.pt ⟶ F.obj (op Y) :=
  Multifork.IsLimit.lift (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩)
    (fun k ↦ s.ι (⟨_, G.map k.f ≫ f, k.hf⟩) ≫ α.app (op k.Y)) (by
      intro { fst := ⟨Y₁, p₁, hp₁⟩, snd := ⟨Y₂, p₂, hp₂⟩, r := ⟨W, g₁, g₂, w⟩ }
      dsimp at g₁ g₂ w ⊢
      simp only [Category.assoc, ← α.naturality, Functor.comp_map,
        Functor.op_map, Quiver.Hom.unop_op]
      apply s.condition_assoc
        { fst.hf := hp₁
          snd.hf := hp₂
          r.g₁ := G.map g₁
          r.g₂ := G.map g₂
          r.w := by simpa using G.congr_map w =≫ f
          .. })

lemma liftAux_map {Y : C} (f : G.obj Y ⟶ X) {W : C} (g : W ⟶ Y) (i : S.Arrow)
    (h : G.obj W ⟶ i.Y) (w : h ≫ i.f = G.map g ≫ f) :
    liftAux hF α s f ≫ F.map g.op = s.ι i ≫ R.map h.op ≫ α.app _ :=
  (Multifork.IsLimit.fac
    (hF.isLimitMultifork ⟨_, G.cover_lift J K (K.pullback_stable f S.2)⟩) _ _
      ⟨W, g, by simpa only [Sieve.functorPullback_apply, functorPullback_mem,
        Sieve.pullback_apply, ← w] using S.1.downward_closed i.hf h⟩).trans (by
        dsimp
        simp only [← Category.assoc]
        congr 1
        let r : S.Relation :=
          { fst.f := G.map g ≫ f
            fst.hf := by simpa only [← w] using S.1.downward_closed i.hf h
            snd := i
            r.g₁ := 𝟙 _
            r.g₂ := h
            r.w := by simpa using w.symm
            .. }
        simpa [r] using s.condition r )

lemma liftAux_map' {Y Y' : C} (f : G.obj Y ⟶ X) (f' : G.obj Y' ⟶ X) {W : C}
    (a : W ⟶ Y) (b : W ⟶ Y') (w : G.map a ≫ f = G.map b ≫ f') :
    liftAux hF α s f ≫ F.map a.op = liftAux hF α s f' ≫ F.map b.op := by
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable (G.map a ≫ f) S.2)⟩
  rintro ⟨T, g, hg⟩
  dsimp
  have eq₁ := liftAux_map hF α s f (g ≫ a) ⟨_, _, hg⟩ (𝟙 _) (by simp)
  have eq₂ := liftAux_map hF α s f' (g ≫ b) ⟨_, _, hg⟩ (𝟙 _) (by simp [w])
  dsimp at eq₁ eq₂
  simp only [Functor.map_comp, Functor.map_id, Category.id_comp] at eq₁ eq₂
  simp only [Category.assoc, eq₁, eq₂]

variable {α}

/-- Auxiliary definition for `isLimitMultifork` -/
def lift : s.pt ⟶ R.obj (op X) :=
  (hR (op X)).lift (Cone.mk _
    { app := fun j ↦ liftAux hF α s j.hom.unop
      naturality := fun j j' φ ↦ by
        simpa using liftAux_map' hF α s j'.hom.unop j.hom.unop (𝟙 _) φ.right.unop
          (Quiver.Hom.op_inj (by simpa using (StructuredArrow.w φ).symm)) })

lemma fac' (j : StructuredArrow (op X) G.op) :
    lift hF hR s ≫ R.map j.hom ≫ α.app j.right = liftAux hF α s j.hom.unop := by
  apply IsLimit.fac

@[reassoc (attr := simp)]
lemma fac (i : S.Arrow) : lift hF hR s ≫ R.map i.f.op = s.ι i := by
  apply (hR (op i.Y)).hom_ext
  intro j
  have eq := fac' hF hR s (StructuredArrow.mk (i.f.op ≫ j.hom))
  dsimp at eq ⊢
  simp only [Functor.map_comp, Category.assoc] at eq
  rw [Category.assoc, eq]
  simpa using liftAux_map hF α s (j.hom.unop ≫ i.f) (𝟙 _) i j.hom.unop (by simp)

include hR hF in
variable (K) in
lemma hom_ext {W : A} {f g : W ⟶ R.obj (op X)}
    (h : ∀ (i : S.Arrow), f ≫ R.map i.f.op = g ≫ R.map i.f.op) : f = g := by
  apply (hR (op X)).hom_ext
  intro j
  apply hF.hom_ext ⟨_, G.cover_lift J K (K.pullback_stable j.hom.unop S.2)⟩
  intro ⟨W, i, hi⟩
  have eq := h (GrothendieckTopology.Cover.Arrow.mk _ (G.map i ≫ j.hom.unop) hi)
  dsimp at eq ⊢
  simp only [Category.assoc, ← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    Functor.op_map, Quiver.Hom.unop_op]
  rw [reassoc_of% eq]

variable (S)

/-- Auxiliary definition for `ran_isSheaf_of_isCocontinuous` -/
def isLimitMultifork : IsLimit (S.multifork R) :=
  Multifork.IsLimit.mk _ (lift hF hR) (fac hF hR)
    (fun s _ hm ↦ hom_ext K hF hR (fun i ↦ (hm i).trans (fac hF hR s i).symm))

end RanIsSheafOfIsCocontinuous

variable (K)
variable [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]

/-- If `G` is cocontinuous, then `G.op.ran` pushes sheaves to sheaves.

This is SGA 4 III 2.2. -/
@[stacks 00XK "Alternative reference. There, results are obtained under the additional assumption
that `C` and `D` have pullbacks."]
theorem ran_isSheaf_of_isCocontinuous (ℱ : Sheaf J A) :
    Presheaf.IsSheaf K (G.op.ran.obj ℱ.val) := by
  rw [Presheaf.isSheaf_iff_multifork]
  intros X S
  exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork ℱ.2
    (G.op.isPointwiseRightKanExtensionRanCounit ℱ.val) S⟩

variable (A J)

/-- A cocontinuous functor induces a pushforward functor on categories of sheaves. -/
def Functor.sheafPushforwardCocontinuous : Sheaf J A ⥤ Sheaf K A where
  obj ℱ := ⟨G.op.ran.obj ℱ.val, ran_isSheaf_of_isCocontinuous _ K ℱ⟩
  map f := ⟨G.op.ran.map f.val⟩
  map_id ℱ := Sheaf.Hom.ext <| (ran G.op).map_id ℱ.val
  map_comp f g := Sheaf.Hom.ext <| (ran G.op).map_comp f.val g.val

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

variable [G.IsContinuous J K]

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
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm F).trans
      (by aesop_cat)

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

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting compatibility between pushforward and sheafification. -/
def pushforwardContinuousSheafificationCompatibility [G.IsContinuous J K] :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
    presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K :=
  ((G.op.ranAdjunction A).comp (sheafificationAdjunction J A)).leftAdjointUniq
    ((sheafificationAdjunction K A).comp (G.sheafAdjunctionCocontinuous A J K))

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
