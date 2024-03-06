/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

theorem equalizerCondition_w (P : Cᵒᵖ ⥤ D) {X B : C} (π : X ⟶ B) (c : PullbackCone π π) :
    P.map π.op ≫ P.map c.fst.op = P.map π.op ≫ P.map c.snd.op := by
  simp only [← Functor.map_comp, ← op_comp, c.condition]

def EqualizerCondition (P : Cᵒᵖ ⥤ D) : Prop :=
  ∀ ⦃X B : C⦄ (π : X ⟶ B) [EffectiveEpi π] (c : PullbackCone π π) (_ : IsLimit c),
    Nonempty (IsLimit (Fork.ofι (P.map π.op) (equalizerCondition_w P π c)))

def Fork.isLimitOfIsos {X S : C} {f₁ f₂ : X ⟶ S}
    (c : Fork f₁ f₂) (hc : IsLimit c) {X' S' : C}
    {f₁' f₂' : X' ⟶ S'} (c' : Fork f₁' f₂')
    (e₀ : S ≅ S') (e₁ : X ≅ X') (e : c.pt ≅ c'.pt)
    (comm₁ : e₁.hom ≫ f₁' = f₁ ≫ e₀.hom := by aesop_cat)
    (comm₂ : e₁.hom ≫ f₂' = f₂ ≫ e₀.hom := by aesop_cat)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₁.hom := by aesop_cat) : IsLimit c' := by
  let i : parallelPair f₁ f₂ ≅ parallelPair f₁' f₂' := parallelPair.ext e₁ e₀ comm₁.symm comm₂.symm
  refine (IsLimit.equivOfNatIsoOfIso i c c' (Cones.ext e ?_)) hc
  rintro ⟨j⟩
  · exact comm₃.symm
  · simp only [Cones.postcompose_obj_pt, Functor.const_obj_obj, parallelPair_obj_one,
      Cones.postcompose_obj_π, NatTrans.comp_app, Fork.app_one_eq_ι_comp_left, parallelPair_obj_zero,
      parallelPair.ext_hom_app, Category.assoc]
    rw [← comm₁, ← Category.assoc, ← comm₃, Category.assoc]

theorem equalizerCondition_of_natIso {P P' : Cᵒᵖ ⥤ D} (i : P ≅ P')
    (hP : EqualizerCondition P) : EqualizerCondition P' := fun {X B} π _ c hc =>
  ⟨Fork.isLimitOfIsos _ (hP π c hc).some _ (i.app _) (i.app _) (i.app _)⟩

def isLimit_equiv_of_eq {X Y : C} {f g : X ⟶ Y} {P : C} (ι ι' : P ⟶ X) (w : ι ≫ f = ι ≫ g)
  (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι') :
  IsLimit (Fork.ofι ι w) ≃ IsLimit (Fork.ofι ι' w') := sorry
  -- (by rwa [h] at w : ι' ≫ f = ι' ≫ g)

/-- Precomposing with a pullback-preserving functor preserves the equalizer condition. -/
theorem equalizerCondition_precomp_of_preservesPullback (P : Cᵒᵖ ⥤ Type*)
    (F : D ⥤ C) [∀ {X B} (π : X ⟶ B) [EffectiveEpi π], PreservesLimit (cospan π π) F]
    [F.PreservesEffectiveEpis] (hP : EqualizerCondition P) : EqualizerCondition (F.op ⋙ P) := by
  -- rw [equalizerCondition_iff]
  intro X B π _ c hc
  have hFc := isLimitOfPreserves F hc
  have := hP (F.map π) -- (F.mapCone c)
  have hh : (F.op ⋙ P).map π.op = P.map (F.map π).op := by simp
  refine ⟨(isLimit_equiv_of_eq _ _ ?_ _ hh.symm) ?_⟩
  · simp only [Functor.comp_obj, Functor.op_obj, Opposite.unop_op, Functor.comp_map,
      Functor.op_map, Quiver.Hom.unop_op]
    simp only [← Functor.map_comp, ← op_comp, c.condition]
  · refine (this (PullbackCone.mk (F.map c.fst) (F.map c.snd) ?_) ?_).some
    · simp only [← Functor.map_comp, c.condition]
    · sorry

open Opposite Presieve

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type*} (hF : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, hS, πsurj⟩ := Presieve.regular.single_epi (R := S)
  subst hS
  rw [isSheafFor_arrows_iff_pullbacks]
  intro y h
  have : (Presieve.singleton π).hasPullbacks := by rw [← ofArrows_pUnit]; infer_instance
  have : HasPullback π π := hasPullbacks.has_pullbacks Presieve.singleton.mk Presieve.singleton.mk
  let c : PullbackCone π π := (IsPullback.of_hasPullback π π).cone
  have hc : IsLimit c := IsPullback.isLimit _
  specialize hF π c hc
  rw [Types.type_equalizer_iff_unique] at hF
  obtain ⟨t, ht⟩ := hF (y ()) (h () ())
  exact ⟨t, fun _ ↦ ht.1, fun _ h ↦ ht.2 _ (h _)⟩
