/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Split exact categories

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type _} [Category C] [Preadditive C]

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace ExactCategory

variable (C)

def splitShortExact : (ShortComplex C) → Prop := fun S => Nonempty S.Splitting

variable {C}

lemma splitShortExact_op (S : ShortComplex C) (hX : splitShortExact C S) :
    splitShortExact Cᵒᵖ S.op := by
  obtain ⟨h⟩ := hX
  exact ⟨h.op⟩

lemma splitShortExact_unop (S : ShortComplex Cᵒᵖ) (hX : splitShortExact Cᵒᵖ S) :
    splitShortExact C S.unop:= by
  obtain ⟨h⟩ := hX
  exact ⟨h.unop⟩

variable (C)

def admissibleSplitMono := ShortComplex.fAdmissible (splitShortExact C)
def admissibleSplitEpi := ShortComplex.gAdmissible (splitShortExact C)

lemma admissibleSplitMono_op : (admissibleSplitMono _).op = admissibleSplitEpi Cᵒᵖ := by
  ext X Y f
  constructor
  · rintro ⟨_, _, _, h⟩
    exact ⟨_, _, _, splitShortExact_op _ h⟩
  · rintro ⟨_, _, _, h⟩
    exact ⟨_, _, _, splitShortExact_unop _ h⟩

lemma admissibleSplitEpi_op : (admissibleSplitEpi _).op = admissibleSplitMono Cᵒᵖ := by
  ext X Y f
  constructor
  · rintro ⟨_, _, _, h⟩
    exact ⟨_, _, _, splitShortExact_op _ h⟩
  · rintro ⟨_, _, _, h⟩
    exact ⟨_, _, _, splitShortExact_unop _ h⟩

lemma admissibleSplitMono_unop : (admissibleSplitMono Cᵒᵖ).unop = admissibleSplitEpi C := by
  rw [← (admissibleSplitEpi C).unop_op, admissibleSplitEpi_op]

lemma admissibleSplitEpi_unop : (admissibleSplitEpi Cᵒᵖ).unop = admissibleSplitMono C := by
  rw [← (admissibleSplitMono C).unop_op, admissibleSplitMono_op]

variable {C}

variable [HasBinaryBiproducts C]

noncomputable def splitShortExactPushoutCocone (S : ShortComplex C) (h : S.Splitting) {X₁' : C}
    (i : S.X₁ ⟶ X₁') : PushoutCocone S.f i :=
  PushoutCocone.mk (S.g ≫ biprod.inl + h.r ≫ i ≫ biprod.inr : _ ⟶ biprod S.X₃ X₁')
    biprod.inr (by simp)

noncomputable def isColimitSplitShortExactPushoutCocone (S : ShortComplex C) (h : S.Splitting)
    {X₁' : C} (i : S.X₁ ⟶ X₁') : IsColimit (splitShortExactPushoutCocone S h i) :=
  PushoutCocone.IsColimit.mk _ (fun s => biprod.desc (h.s ≫ s.inl) s.inr)
    (fun s => by simp [h.g_s_assoc, s.condition])
    (fun s => by simp)
    (fun s m h₁ h₂ => by
      ext
      · dsimp
        simp only [biprod.inl_desc, ← h₁, Preadditive.add_comp, assoc,
          Preadditive.comp_add, h.s_g_assoc, left_eq_add, h₂, h.s_r_assoc, zero_comp]
      · simp [h₂])

lemma admissibleSplitMono_coquarrable {X Y : C} (f : X ⟶ Y) (hf : (admissibleSplitMono C) f) :
    MorphismProperty.coquarrable C f := by
  intro X' i
  obtain ⟨Z, g, zero, ⟨h⟩⟩ := hf
  exact ⟨_, isColimitSplitShortExactPushoutCocone _ h i⟩

lemma admissibleSplitEpi_quarrable {X Y : C} (f : X ⟶ Y) (hf : (admissibleSplitEpi C) f) :
    MorphismProperty.quarrable C f := by
  apply MorphismProperty.coquarrable.unop
  apply admissibleSplitMono_coquarrable
  simpa only [← admissibleSplitEpi_op  C] using hf

variable (C)

lemma admissibleSplitMono_stableUnderComposition :
    (admissibleSplitMono C).IsStableUnderComposition := ⟨by
  rintro X Y Z f₁ f₂ ⟨A₁, g₁, zero₁, ⟨h₁⟩⟩ ⟨A₂, g₂, zero₂, ⟨h₂⟩⟩
  refine ⟨A₁ ⊞ A₂, biprod.lift (h₂.r ≫ g₁) g₂, ?_, ⟨?_⟩⟩
  · ext
    · simp only [assoc, biprod.lift_fst, zero_comp]
      rw [h₂.f_r_assoc, zero₁]
    · simp [zero₂]
  · exact
    { r := h₂.r ≫ h₁.r
      s := biprod.desc (h₁.s ≫ f₂) h₂.s
      s_g := by
        dsimp
        ext
        · dsimp
          simp only [assoc, biprod.lift_fst, biprod.inl_desc_assoc, id_comp, biprod.inl_fst]
          rw [h₂.f_r_assoc, h₁.s_g]
        · dsimp
          simp only [biprod.inl_desc_assoc, assoc, biprod.lift_snd, comp_id, biprod.inl_snd,
            zero₂, comp_zero]
        · dsimp
          simp only [assoc, biprod.lift_fst, biprod.inr_desc_assoc,
            h₂.s_r_assoc, zero_comp, id_comp, biprod.inr_fst]
        · dsimp
          simp only [assoc, biprod.lift_snd, biprod.inr_desc_assoc, id_comp, biprod.inr_snd]
          rw [h₂.s_g]
      f_r := by
        dsimp
        rw [assoc, h₂.f_r_assoc, h₁.f_r]
      id := by
        dsimp
        rw [biprod.lift_desc, assoc, h₁.r_f_assoc, ← h₂.id, Preadditive.sub_comp, id_comp,
          assoc, Preadditive.comp_sub, assoc]
        abel }⟩

lemma admissibleSplitEpi_stableUnderComposition :
    (admissibleSplitEpi C).IsStableUnderComposition := by
  simpa only [admissibleSplitMono_unop]
    using (admissibleSplitMono_stableUnderComposition Cᵒᵖ).unop

omit [HasBinaryBiproducts C] in
lemma admissibleSplitMono_stableUnderCobaseChange :
    (admissibleSplitMono C).IsStableUnderCobaseChange := ⟨by
  intro X₁ X₂ X₁' X₂' f i f' i' sq hf
  obtain ⟨X₃, g, zero, ⟨h⟩⟩ := hf
  obtain ⟨φ : X₂' ⟶ X₃, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' sq.isColimit 0 g (by simp [zero])
  obtain ⟨ψ : X₂' ⟶ X₁', hψ₁, hψ₂⟩ :=  PushoutCocone.IsColimit.desc' sq.isColimit
    (𝟙 X₁') (h.r ≫ i) (by rw [h.f_r_assoc, comp_id])
  dsimp at hφ₁ hφ₂ hψ₁ hψ₂
  refine ⟨X₃, φ, hφ₁, ⟨?_⟩⟩
  exact
  { r := ψ
    s := h.s ≫ i'
    f_r := hψ₁
    s_g := by
      dsimp
      rw [assoc, hφ₂, h.s_g]
    id := by
      apply PushoutCocone.IsColimit.hom_ext sq.isColimit
      · dsimp
        simp only [Preadditive.comp_add, reassoc_of% hψ₁, reassoc_of% hφ₁, zero_comp, add_zero]
        erw [comp_id]
      · dsimp
        erw [Preadditive.comp_add, reassoc_of% hψ₂, reassoc_of% hφ₂, comp_id, sq.w,
          h.g_s_assoc, Preadditive.sub_comp, id_comp, assoc, add_sub_cancel] }⟩

omit [HasBinaryBiproducts C] in
lemma admissibleSplitEpi_stableUnderBaseChange :
    (admissibleSplitEpi C).IsStableUnderBaseChange := by
  simpa only [admissibleSplitMono_unop]
    using (admissibleSplitMono_stableUnderCobaseChange Cᵒᵖ).unop

def splitExactSequences [HasZeroObject C] : ExactCategory C where
  shortExact' := splitShortExact C
  respectsIso_shortExact' := ⟨fun {S₁ S₂} e => by
    rintro ⟨h₁⟩
    exact ⟨h₁.ofIso e⟩⟩
  shortExact_kernel' := by
    rintro S ⟨hS⟩
    exact ⟨hS.fIsKernel⟩
  shortExact_cokernel' := by
    rintro S ⟨hS⟩
    exact ⟨hS.gIsCokernel⟩
  isMultiplicative_admissibleMono :=
    { id_mem X := ⟨0, 0, comp_zero, ⟨ShortComplex.Splitting.ofIsIsoOfIsZero _
        (by dsimp; infer_instance) (isZero_zero _)⟩⟩
      toIsStableUnderComposition := admissibleSplitMono_stableUnderComposition C }
  isMultiplicative_admissibleEpi :=
    { id_mem X := ⟨0, 0, zero_comp, ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _
        (isZero_zero _) (by dsimp; infer_instance)⟩⟩
      toIsStableUnderComposition := admissibleSplitEpi_stableUnderComposition C }
  admissibleMono_coquarrable := fun _ _ _ hf => admissibleSplitMono_coquarrable _ hf
  admissibleEpi_quarrable := fun _ _ _ hf => admissibleSplitEpi_quarrable _ hf
  admissibleMono_stableUnderCobaseChange := admissibleSplitMono_stableUnderCobaseChange C
  admissibleEpi_stableUnderBaseChange := admissibleSplitEpi_stableUnderBaseChange C

end ExactCategory

end CategoryTheory
