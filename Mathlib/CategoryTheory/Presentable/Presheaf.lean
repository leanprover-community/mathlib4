/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.IsoCat
public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtCoyoneda
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Subfunctor.Colimits
public import Mathlib.CategoryTheory.Subfunctor.Image

import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Categories of presheaves are locally presentable

If `A` is a locally `κ`-presentable category and `C` is a small category,
we show that `Cᵒᵖ ⥤ A` is also locally `κ`-presentable, under the
additional assumption that `A` has pullbacks. This assumption about
pullbacks is automatically satisfied, as it is proven in the file
`CategoryTheory.Presentable.Representation`.

-/

public section

universe w v v' u u'

namespace CategoryTheory

open Opposite Limits

-- to be moved
lemma NatTrans.surjective_mapElements_obj_of_epi {C : Type*} [Category* C]
    {F G : C ⥤ Type w} (f : F ⟶ G) [Epi f] :
    Function.Surjective f.mapElements.obj := by
  rintro @⟨X, e⟩
  obtain ⟨e, rfl⟩ := surjective_of_epi (f.app X) e
  exact ⟨Functor.elementsMk _ _ e, rfl⟩

namespace Presheaf

attribute [local simp] freeYonedaHomEquiv_comp in
instance {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{w, w} A] [HasCoproducts.{v} A]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) (M : A)
    [IsCardinalPresentable M κ] :
    IsCardinalPresentable (freeYoneda X M) κ := by
  let e : coyoneda.obj (op (freeYoneda X M)) ≅
      (evaluation Cᵒᵖ A).obj (op X) ⋙ coyoneda.obj (op M) ⋙ uliftFunctor.{u} :=
    NatIso.ofComponents (fun P ↦ Equiv.toIso (freeYonedaHomEquiv.trans Equiv.ulift.symm))
  constructor
  intro J _ _
  have := preservesColimitsOfShape_of_isCardinalPresentable M κ J
  exact preservesColimitsOfShape_of_natIso e.symm

-- TODO: add variants of this result for `yoneda` and `shrinkYoneda`
instance {C : Type u} [SmallCategory C]
    [HasColimitsOfSize.{w, w} (Type (max u u'))]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) :
    IsCardinalPresentable (uliftYoneda.{u'}.obj X) κ where
  preservesColimitOfShape J _ _ := by
    let e : (coyoneda.obj (op (uliftYoneda.{u'}.obj X))) ≅
        (evaluation _ _).obj (op X) ⋙ uliftFunctor :=
      NatIso.ofComponents (fun P ↦ Equiv.toIso (uliftYonedaEquiv.trans Equiv.ulift.symm))
    exact preservesColimitsOfShape_of_natIso e.symm

lemma isStrongGenerator
    {A : Type u'} [Category.{v'} A] {P : ObjectProperty A} (hP : P.IsStrongGenerator)
    [HasCoproducts.{w} A] [HasPullbacks A] (C : Type w) [SmallCategory C] :
    (ObjectProperty.ofObj (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff] at hP ⊢
  obtain ⟨hP₁, hP₂⟩ := hP
  refine ⟨Presheaf.isSeparating (C := C) (ι := Subtype P) (S := Subtype.val)
    (by simpa using hP₁),
    fun P₁ P₂ i _ hi ↦ ?_⟩
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨X⟩
  refine hP₂ _ (fun G hG f ↦ ?_)
  obtain ⟨y, rfl⟩ := freeYonedaHomEquiv.surjective f
  obtain ⟨x, rfl⟩ := hi (freeYoneda X G)
    (ObjectProperty.ofObj_apply (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1) ⟨X, G, hG⟩) y
  exact ⟨freeYonedaHomEquiv x, by simp [freeYonedaHomEquiv_comp]⟩

instance {A : Type u'} [Category.{v'} A] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable A κ] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsCardinalLocallyPresentable (Cᵒᵖ ⥤ A) κ := by
  have hA := (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator A κ).1 inferInstance
  obtain ⟨P, _, hP₁, hP₂⟩ := hA
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨_, inferInstance, isStrongGenerator hP₁ C, ?_⟩
  rintro _ ⟨X, G, hG⟩
  have := hP₂ _ hG
  rw [isCardinalPresentable_iff] at this ⊢
  infer_instance

instance {A : Type u'} [Category.{v'} A] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable A κ] [HasPullbacks A]
    (C : Type*) [Category* C] [EssentiallySmall.{w} C] :
    IsCardinalLocallyPresentable (C ⥤ A) κ :=
  ((opOpEquivalence ..).trans
    (equivSmallModel.{w} C).symm).congrLeft.isCardinalLocallyPresentable κ

instance {A : Type u'} [Category.{v'} A] [IsLocallyPresentable.{w} A] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ A) where
  exists_cardinal := by
    obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} A
    exact ⟨κ, inferInstance, inferInstance⟩

instance {A : Type u'} [Category.{v'} A] [IsLocallyPresentable.{w} A] [HasPullbacks A]
    (C : Type*) [Category* C] [EssentiallySmall.{w} C] :
    IsLocallyPresentable.{w} (C ⥤ A) where
  exists_cardinal := by
    obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} A
    exact ⟨κ, inferInstance, inferInstance⟩

end Presheaf

lemma Functor.Elements.hasCardinalLT_arrow_elements_iff
    {A : Type*} [Category* A] {κ : Cardinal.{w}} (P : A ⥤ Type w)
    (hκ₀ : .aleph0 ≤ κ) (hκ : HasCardinalLT (Arrow A) κ) :
    HasCardinalLT (Arrow P.Elements) κ ↔ HasCardinalLT P.Elements κ :=
  ⟨hasCardinalLT_of_hasCardinalLT_arrow,
    fun h ↦ HasCardinalLT.of_injective
      (hasCardinalLT_prod hκ₀ h (hasCardinalLT_prod hκ₀ h hκ))
        (fun f ↦ (f.left, f.right, Arrow.mk f.hom.hom))
        (fun f₁ f₂ h ↦ by
          obtain ⟨X, Y, f₁, rfl⟩ := f₁.mk_surjective
          obtain ⟨X', Y', f₂, rfl⟩ := f₂.mk_surjective
          obtain rfl : X = X' := congr($(h).1)
          obtain rfl : Y = Y' := congr($(h).2.1)
          obtain rfl : f₁ = f₂ := by ext; exact congr($(h).2.2.hom)
          rfl)⟩

namespace Subfunctor

variable {A : Type*} [Category* A] {κ : Cardinal.{w}}
  {P : A ⥤ Type w}

lemma hasCardinalLT_elements_sup
    {S₁ S₂ : Subfunctor P} (h₁ : HasCardinalLT S₁.toFunctor.Elements κ)
    (h₂ : HasCardinalLT S₂.toFunctor.Elements κ) (hκ : .aleph0 ≤ κ) :
    HasCardinalLT (S₁ ⊔ S₂).toFunctor.Elements κ :=
  .of_surjective ((hasCardinalLT_sum_iff _ _ κ hκ).mpr ⟨h₁, h₂⟩)
    (fun e ↦ match e with
      | .inl e => (Subfunctor.homOfLe le_sup_left).mapElements.obj e
      | .inr e => (Subfunctor.homOfLe le_sup_right).mapElements.obj e)  (by
      intro ⟨e, he⟩
      simp only [max_obj, Set.mem_union] at he
      obtain he | he := he
      · exact ⟨Sum.inl (Functor.elementsMk _ _ ⟨e, he⟩), rfl⟩
      · exact ⟨Sum.inr (Functor.elementsMk _ _ ⟨e, he⟩), rfl⟩)

lemma hasCardinalLT_elements_iSup [Fact κ.IsRegular]
    {ι : Type*} {S : ι → Subfunctor P} (h : ∀ i, HasCardinalLT (S i).toFunctor.Elements κ)
    (hι : HasCardinalLT ι κ) :
    HasCardinalLT (⨆ i, S i).toFunctor.Elements κ :=
  (hasCardinalLT_sigma _ _ hι h).of_surjective
    (fun e ↦ (Subfunctor.homOfLe (le_iSup S e.1)).mapElements.obj e.2) (by
      intro ⟨e, he⟩
      simp only [iSup_obj, Set.mem_iUnion] at he
      obtain ⟨i, he⟩ := he
      exact ⟨⟨i, Functor.elementsMk _ _ ⟨e, he⟩⟩, rfl⟩)

end Subfunctor

namespace Presheaf

section

variable {A : Type w} [SmallCategory A] {κ : Cardinal.{w}} [Fact κ.IsRegular]
  {P : A ⥤ Type w}

lemma isCardinalPresentable_of_hasCardinalLT_arrow_elements
    (hP : HasCardinalLT (Arrow P.Elements) κ) :
    IsCardinalPresentable P κ := by
  apply +allowSynthFailures isCardinalPresentable_of_isColimit _
    (Functor.Elements.isColimitShrinkCoyonedaCocone P) κ
  · simpa
  · intro
    dsimp
    infer_instance

variable (κ P) in
abbrev hasCardinalLTSubfunctorToFunctorElements : Set (Subfunctor P) :=
  .ofPred (fun S ↦ HasCardinalLT (S.toFunctor.Elements) κ)

namespace hasCardinalLTSubfunctorToFunctorElements

instance :
    IsCardinalFiltered (hasCardinalLTSubfunctorToFunctorElements κ P) κ :=
  isCardinalFiltered_preorder _ _ (fun ι S hι ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hι
    let T : Subfunctor P := ⨆ (i : ι), S i
    have hT (i : ι) : S i ≤ T := le_trans (by rfl) (le_iSup _ i)
    refine ⟨⟨T, ?_⟩, fun i ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq]
      let p : (Σ (i : ι), (S i).val.toFunctor.Elements) → T.toFunctor.Elements :=
        fun ⟨i, x⟩ ↦ (NatTrans.mapElements (Subfunctor.homOfLe (hT i))).obj x
      have hp : Function.Surjective p := by
        rintro @⟨X, e, he⟩
        simp only [Set.mem_ofPred_eq, Subfunctor.iSup_obj, Set.mem_iUnion, T] at he
        obtain ⟨i, he⟩ := he
        exact ⟨⟨i, Functor.elementsMk _ X ⟨e, he⟩⟩, rfl⟩
      exact .of_surjective (hasCardinalLT_sigma _ _ hι (fun i ↦ (S i).prop)) _ hp
    · rw [Subtype.mk_le_mk]
      exact hT i)

instance : IsFiltered (hasCardinalLTSubfunctorToFunctorElements κ P) :=
  isFiltered_of_isCardinalFiltered _ κ

variable (κ P) in
@[expose, simps, implicit_reducible]
def cocone :
    Cocone ((Set.mono_coe (hasCardinalLTSubfunctorToFunctorElements κ P)).functor ⋙
      Subfunctor.toFunctorFunctor) where
  pt := P
  ι.app _ := Subfunctor.ι _

set_option backward.isDefEq.respectTransparency false in
variable (P) in
noncomputable def isColimitCocone (hκ : HasCardinalLT (Arrow A) κ) :
    IsColimit (cocone κ P) := by
  refine IsColimit.ofIsoColimit
    (isColimitOfPreserves Subfunctor.toFunctorFunctor
    ((Preorder.colimitCoconeOfIsLUB
    (hasCardinalLTSubfunctorToFunctorElements κ P).mono_coe.functor ?_).isColimit))
    (Cocone.ext (Subfunctor.topIso _))
  refine ⟨by tauto, fun Q hQ X x _ ↦
    hQ ⟨⟨Subfunctor.range (coyonedaEquiv.symm x), ?_⟩, rfl⟩ _ ⟨𝟙 X, by simp⟩⟩
  refine .of_surjective (hκ.of_injective (fun e ↦ Arrow.mk e.val) (fun _ _ h ↦ ?_)) _
    ((Subfunctor.toRange _).surjective_mapElements_obj_of_epi)
  rw [Arrow.mk_eq_mk_iff] at h
  obtain ⟨_, _, _⟩ := h
  exact Functor.Elements.ext _ _ (by assumption) (by aesop)

end hasCardinalLTSubfunctorToFunctorElements

open hasCardinalLTSubfunctorToFunctorElements in
lemma isCardinalPresentable_iff_hasCardinalLT_elements
    (hκ : HasCardinalLT (Arrow A) κ) :
    IsCardinalPresentable P κ ↔ HasCardinalLT P.Elements κ := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · have : IsCardinalPresentable (cocone κ P).pt κ := by assumption
    obtain ⟨⟨S, hS⟩, f, fac⟩ :=
      IsCardinalPresentable.exists_hom_of_isColimit κ (isColimitCocone P hκ) (𝟙 _)
    dsimp at f fac
    have : IsIso f := ⟨S.ι, fac, by simp [← cancel_mono S.ι, fac]⟩
    exact hS.of_injective  _
      (Functor.Elements.isoCatOfIso (asIso f)).objEquiv.injective
  · apply isCardinalPresentable_of_hasCardinalLT_arrow_elements
    rwa [Functor.Elements.hasCardinalLT_arrow_elements_iff P
      (Cardinal.IsRegular.aleph0_le Fact.out) hκ]

end

end Presheaf

end CategoryTheory
