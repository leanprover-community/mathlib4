/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.IndObject

/-!
# Morphisms of ind-objects
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace CommaFacts

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (F : D ⥤ C) (G : E ⥤ C)

instance [IsFiltered D] [IsFiltered E] [G.Final] : IsFiltered (Comma F G) := sorry
instance [IsFiltered D] [IsFiltered E] [G.Final] : (Comma.fst F G).Final := sorry
instance [IsFiltered D] [IsFiltered E] [G.Final] : (Comma.snd F G).Final := sorry

end CommaFacts

open Limits

variable {C : Type u₁} [Category.{v₁} C]

section

structure MorphismPresentation {A B : Cᵒᵖ ⥤ Type v₁} (f : A ⟶ B) where
  I : Type v₁
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  F₁ : I ⥤ C
  F₂ : I ⥤ C
  ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
  isColimit₁ : IsColimit (Cocone.mk A ι₁)
  ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
  isColimit₂ : IsColimit (Cocone.mk B ι₂)
  φ : F₁ ⟶ F₂
  hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)

namespace Morphs

variable {A B : Cᵒᵖ ⥤ Type v₁} (f : A ⟶ B) (P₁ : IndObjectPresentation A)
  (P₂ : IndObjectPresentation B)

abbrev K : Type v₁ :=
  Comma (P₁.toCostructuredArrow ⋙ CostructuredArrow.map f) P₂.toCostructuredArrow

abbrev F₁ : K f P₁ P₂ ⥤ C := Comma.fst _ _ ⋙ P₁.F
abbrev F₂ : K f P₁ P₂ ⥤ C := Comma.snd _ _ ⋙ P₂.F

abbrev ι₁ : F₁ f P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f P₁ P₂)).obj A :=
  whiskerLeft (Comma.fst _ _) P₁.ι

noncomputable abbrev isColimit₁ : IsColimit (Cocone.mk A (ι₁ f P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

abbrev ι₂ : F₂ f P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f P₁ P₂)).obj B :=
  whiskerLeft (Comma.snd _ _) P₂.ι

noncomputable abbrev isColimit₂ : IsColimit (Cocone.mk B (ι₂ f P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

def ϕ : F₁ f P₁ P₂ ⟶ F₂ f P₁ P₂ where
  app g := g.hom.left
  naturality _ _ h := by simpa using h.w

theorem hf : f = IsColimit.map (isColimit₁ f P₁ P₂)
    (Cocone.mk B (ι₂ f P₁ P₂)) (whiskerRight (ϕ f P₁ P₂) yoneda) := by
  refine (isColimit₁ f P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa [ϕ] using i.hom.w.symm

end Morphs

structure ParallelPairPresentation {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) where
  I : Type v₁
  [ℐ : SmallCategory I]
  [hI : IsFiltered I]
  F₁ : I ⥤ C
  F₂ : I ⥤ C
  ι₁ : F₁ ⋙ yoneda ⟶ (Functor.const I).obj A
  isColimit₁ : IsColimit (Cocone.mk A ι₁)
  ι₂ : F₂ ⋙ yoneda ⟶ (Functor.const I).obj B
  isColimit₂ : IsColimit (Cocone.mk B ι₂)
  φ : F₁ ⟶ F₂
  ψ : F₁ ⟶ F₂
  hf : f = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight φ yoneda)
  hg : g = IsColimit.map isColimit₁ (Cocone.mk B ι₂) (whiskerRight ψ yoneda)

instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : ParallelPairPresentation f g) :
    SmallCategory P.I := P.ℐ
instance {A B : Cᵒᵖ ⥤ Type v₁} {f g : A ⟶ B} (P : ParallelPairPresentation f g) :
    IsFiltered P.I := P.hI

namespace DoubleMorphs

variable {A B : Cᵒᵖ ⥤ Type v₁} (f g : A ⟶ B) (P₁ : IndObjectPresentation A)
  (P₂ : IndObjectPresentation B)

abbrev K : Type v₁ :=
  Comma ((P₁.toCostructuredArrow ⋙ CostructuredArrow.map f).prod'
    (P₁.toCostructuredArrow ⋙ CostructuredArrow.map g))
    (P₂.toCostructuredArrow.prod' P₂.toCostructuredArrow)

abbrev F₁ : K f g P₁ P₂ ⥤ C := Comma.fst _ _ ⋙ P₁.F
abbrev F₂ : K f g P₁ P₂ ⥤ C := Comma.snd _ _ ⋙ P₂.F

abbrev ι₁ : F₁ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj A :=
  whiskerLeft (Comma.fst _ _) P₁.ι

noncomputable abbrev isColimit₁ : IsColimit (Cocone.mk A (ι₁ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₁.isColimit

abbrev ι₂ : F₂ f g P₁ P₂ ⋙ yoneda ⟶ (Functor.const (K f g P₁ P₂)).obj B :=
  whiskerLeft (Comma.snd _ _) P₂.ι

noncomputable abbrev isColimit₂ : IsColimit (Cocone.mk B (ι₂ f g P₁ P₂)) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm P₂.isColimit

def ϕ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.1.left
  naturality _ _ h := by
    have := h.w
    simp only [Functor.prod'_obj, Functor.comp_obj, prod_Hom, Functor.prod'_map, Functor.comp_map,
      prod_comp, Prod.mk.injEq, CostructuredArrow.hom_eq_iff, CostructuredArrow.map_obj_left,
      IndObjectPresentation.toCostructuredArrow_obj_left, CostructuredArrow.comp_left,
      CostructuredArrow.map_map_left, IndObjectPresentation.toCostructuredArrow_map_left] at this
    exact this.1

theorem hf : f = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ϕ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using i.hom.1.w.symm

def ψ : F₁ f g P₁ P₂ ⟶ F₂ f g P₁ P₂ where
  app h := h.hom.2.left
  naturality _ _ h := by
    have := h.w
    simp only [Functor.prod'_obj, Functor.comp_obj, prod_Hom, Functor.prod'_map, Functor.comp_map,
      prod_comp, Prod.mk.injEq, CostructuredArrow.hom_eq_iff, CostructuredArrow.map_obj_left,
      IndObjectPresentation.toCostructuredArrow_obj_left, CostructuredArrow.comp_left,
      CostructuredArrow.map_map_left, IndObjectPresentation.toCostructuredArrow_map_left] at this
    exact this.2

theorem hg : g = IsColimit.map (isColimit₁ f g P₁ P₂)
    (Cocone.mk B (ι₂ f g P₁ P₂)) (whiskerRight (ψ f g P₁ P₂) yoneda) := by
  refine (isColimit₁ f g P₁ P₂).hom_ext (fun i => ?_)
  rw [IsColimit.ι_map]
  simpa using i.hom.2.w.symm

noncomputable def presentation : ParallelPairPresentation f g where
  I := K f g P₁ P₂
  F₁ := F₁ f g P₁ P₂
  F₂ := F₂ f g P₁ P₂
  ι₁ := ι₁ f g P₁ P₂
  isColimit₁ := isColimit₁ f g P₁ P₂
  ι₂ := ι₂ f g P₁ P₂
  isColimit₂ := isColimit₂ f g P₁ P₂
  φ := ϕ f g P₁ P₂
  ψ := ψ f g P₁ P₂
  hf := hf f g P₁ P₂
  hg := hg f g P₁ P₂

end DoubleMorphs

open DoubleMorphs in
theorem aboutParallelPairs {A B : Cᵒᵖ ⥤ Type v₁} (hA : IsIndObject A) (hB : IsIndObject B)
    (f g : A ⟶ B) : Nonempty (ParallelPairPresentation f g) :=
  ⟨DoubleMorphs.presentation f g hA.presentation hB.presentation⟩

end

end CategoryTheory
