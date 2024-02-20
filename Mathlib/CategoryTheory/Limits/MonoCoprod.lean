/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

#align_import category_theory.limits.mono_coprod from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `MonoCoprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `HasCoproduct A B`
is satisfied. If it is so, it is shown that right inclusions are
also monomorphisms.

More generally, we deduce that when suitable coproducts exists, then
if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.
It also follows that for any `i : I`, `Sigma.ι X i : X i ⟶ ∐ X` is
a monomorphism.

TODO: define distributive categories, and show that they satisfy `MonoCoprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace Limits

variable (C : Type*) [Category C]

/-- This condition expresses that inclusion morphisms into coproducts are monomorphisms. -/
class MonoCoprod : Prop where
  /-- the left inclusion of a colimit binary cofan is mono -/
  binaryCofan_inl : ∀ ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl
#align category_theory.limits.mono_coprod CategoryTheory.Limits.MonoCoprod

variable {C}

instance (priority := 100) monoCoprodOfHasZeroMorphisms [HasZeroMorphisms C] : MonoCoprod C :=
  ⟨fun A B c hc => by
    haveI : IsSplitMono c.inl :=
      IsSplitMono.mk' (SplitMono.mk (hc.desc (BinaryCofan.mk (𝟙 A) 0)) (IsColimit.fac _ _ _))
    infer_instance⟩
#align category_theory.limits.mono_coprod_of_has_zero_morphisms CategoryTheory.Limits.monoCoprodOfHasZeroMorphisms

namespace MonoCoprod

theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr := by
  haveI hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => hc.desc (BinaryCofan.mk f₂ f₁))
      (by aesop_cat) (by aesop_cat)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by aesop_cat) (by aesop_cat))
  exact binaryCofan_inl _ hc'
#align category_theory.limits.mono_coprod.binary_cofan_inr CategoryTheory.Limits.MonoCoprod.binaryCofan_inr

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inl : A ⟶ A ⨿ B) :=
  binaryCofan_inl _ (colimit.isColimit _)

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inr : B ⟶ A ⨿ B) :=
  binaryCofan_inr _ (colimit.isColimit _)

theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl := by
  suffices
    ∀ (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    by exact ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂
  intro
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using
    mono_comp c₁.inl (hc₁.coconePointUniqueUpToIso hc₂).hom
#align category_theory.limits.mono_coprod.mono_inl_iff CategoryTheory.Limits.MonoCoprod.mono_inl_iff

theorem mk' (h : ∀ A B : C, ∃ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C :=
  ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩
#align category_theory.limits.mono_coprod.mk' CategoryTheory.Limits.MonoCoprod.mk'

instance monoCoprodType : MonoCoprod (Type u) :=
  MonoCoprod.mk' fun A B => by
    refine' ⟨BinaryCofan.mk (Sum.inl : A ⟶ Sum A B) Sum.inr, _, _⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ m h₁ h₂ => by
          funext x
          rcases x with x | x
          · exact congr_fun h₁ x
          · exact congr_fun h₂ x)
    · rw [mono_iff_injective]
      intro a₁ a₂ h
      simpa using h
#align category_theory.limits.mono_coprod.mono_coprod_type CategoryTheory.Limits.MonoCoprod.monoCoprodType

section

variable {I₁ I₂ : Type*} {X : I₁ ⊕ I₂ → C} (c : Cofan X)
  (c₁ : Cofan (X ∘ Sum.inl)) (c₂ : Cofan (X ∘ Sum.inr))
  (hc : IsColimit c) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)

/-- Given a family of objects `X : I₁ ⊕ I₂ → C`, a cofan of `X`, and two colimit cofans
of `X ∘ Sum.inl` and `X ∘ Sum.inr`, this is a cofan for `c₁.pt` and `c₂.pt` whose
point is `c.pt`. -/
@[simp]
def binaryCofanSum : BinaryCofan c₁.pt c₂.pt :=
  BinaryCofan.mk (Cofan.IsColimit.desc hc₁ (fun i₁ => c.inj (Sum.inl i₁)))
    (Cofan.IsColimit.desc hc₂ (fun i₂ => c.inj (Sum.inr i₂)))

/-- The binary cofan `binaryCofanSum c c₁ c₂ hc₁ hc₂` is colimit. -/
def isColimitBinaryCofanSum : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂) :=
  BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => Cofan.IsColimit.desc hc (fun i => match i with
      | Sum.inl i₁ => c₁.inj i₁ ≫ f₁
      | Sum.inr i₂ => c₂.inj i₂ ≫ f₂))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₁ _ _ (by simp))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₂ _ _ (by simp))
    (fun f₁ f₂ m hm₁ hm₂ => by
      apply Cofan.IsColimit.hom_ext hc
      rintro (i₁|i₂) <;> aesop_cat)

lemma mono_binaryCofanSum_inl [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl :=
  MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

lemma mono_binaryCofanSum_inr [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr :=
  MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

lemma mono_binaryCofanSum_inl' [MonoCoprod C] (inl : c₁.pt ⟶ c.pt)
    (hinl : ∀ (i₁ : I₁), c₁.inj i₁ ≫ inl = c.inj (Sum.inl i₁)) :
    Mono inl := by
  suffices inl = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl by
    rw [this]
    exact MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₁ _ _ (by simpa using hinl)

lemma mono_binaryCofanSum_inr' [MonoCoprod C] (inr : c₂.pt ⟶ c.pt)
    (hinr : ∀ (i₂ : I₂), c₂.inj i₂ ≫ inr = c.inj (Sum.inr i₂)) :
    Mono inr := by
  suffices inr = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr by
    rw [this]
    exact MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₂ _ _ (by simpa using hinr)

end

section

variable [MonoCoprod C] {I J : Type*} (X : I → C) (ι : J → I) (hι : Function.Injective ι)

section

variable (c : Cofan X) (c₁ : Cofan (X ∘ ι)) (hc : IsColimit c) (hc₁ : IsColimit c₁)

lemma mono_of_injective_aux (c₂ : Cofan (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1))
    (hc₂ : IsColimit c₂) : Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) := by
  classical
  let e := ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  refine mono_binaryCofanSum_inl' (Cofan.mk c.pt (fun i' => c.inj (e i'))) _ _ ?_
    hc₁ hc₂ _ (by simp)
  exact IsColimit.ofIsoColimit ((IsColimit.ofCoconeEquiv (Cocones.equivalenceOfReindexing
    (Discrete.equivalence e) (Iso.refl _))).symm hc) (Cocones.ext (Iso.refl _))

lemma mono_of_injective [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) :=
  mono_of_injective_aux X ι hι c c₁ hc hc₁ _ (colimit.isColimit _)

end

lemma mono_of_injective' [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.desc (f := X ∘ ι) (fun j => Sigma.ι X (ι j))) :=
  mono_of_injective X ι hι _ _ (colimit.isColimit _) (colimit.isColimit _)

lemma mono_map'_of_injective [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.map' ι (fun j => 𝟙 ((X ∘ ι) j))) := by
  convert mono_of_injective' X ι hι
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_comp_map', id_comp, colimit.ι_desc]
  simp

end

section

variable [MonoCoprod C] {I : Type*} (X : I → C)

lemma mono_inj (c : Cofan X) (h : IsColimit c) (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit ↦ i))ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.inj c i) := by
  let ι : Unit → I := fun _ ↦ i
  have hι : Function.Injective ι := fun _ _ _ ↦ rfl
  exact mono_of_injective X ι hι c (Cofan.mk (X i) (fun _ ↦ 𝟙 _)) h
    (mkCofanColimit _ (fun s => s.inj ()))

instance mono_ι [HasCoproduct X] (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit ↦ i))ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.ι X i) :=
  mono_inj X _ (colimit.isColimit _) i

end

open Functor

section Preservation

variable {D : Type*} [Category D] (F : C ⥤ D)

theorem monoCoprod_of_preservesCoprod_of_reflectsMono [MonoCoprod D]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsMonomorphisms F] : MonoCoprod C where
  binaryCofan_inl {A B} c h := by
    let c' := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    apply mono_of_mono_map F
    show Mono c'.inl
    apply MonoCoprod.binaryCofan_inl
    apply mapIsColimitOfPreservesOfIsColimit F
    apply IsColimit.ofIsoColimit h
    refine Cocones.ext (φ := eqToIso rfl) ?_
    rintro ⟨(j₁|j₂)⟩ <;> simp only [const_obj_obj, eqToIso_refl, Iso.refl_hom,
      Category.comp_id, BinaryCofan.mk_inl, BinaryCofan.mk_inr]

end Preservation

section Concrete

instance [ConcreteCategory C] [PreservesColimitsOfShape (Discrete WalkingPair) (forget C)]
    [ReflectsMonomorphisms (forget C)] : MonoCoprod C :=
  monoCoprod_of_preservesCoprod_of_reflectsMono (forget C)

end Concrete

end MonoCoprod

end Limits

end CategoryTheory
