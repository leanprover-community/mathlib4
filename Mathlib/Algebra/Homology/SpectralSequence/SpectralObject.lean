import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.ArrowThree
import Mathlib.Tactic.Linarith

open CategoryTheory Category Limits

namespace CategoryTheory

namespace Limits

variable {C ι ι' J : Type _} [Category C] [Category ι] [Category ι'] [Category J]
  (F : ι' ⥤ ι)

-- this should be moved to `Limits.FunctorCategory`
noncomputable instance [HasFiniteLimits C] (i : ι) :
  PreservesFiniteLimits ((evaluation ι C).obj i) := ⟨fun _ => inferInstance⟩

noncomputable instance [HasFiniteColimits C] (i : ι) :
  PreservesFiniteColimits ((evaluation ι C).obj i) := ⟨fun _ => inferInstance⟩

instance [HasZeroMorphisms C] :
    ((whiskeringLeft ι' ι C).obj F).PreservesZeroMorphisms where

noncomputable instance [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J ((whiskeringLeft ι' ι C).obj F) :=
    ⟨fun {_} => ⟨fun hc => evaluationJointlyReflectsLimits _
      (fun i => isLimitOfPreserves ((evaluation ι C).obj (F.obj i)) hc)⟩⟩

noncomputable instance [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J ((whiskeringLeft ι' ι C).obj F) :=
    ⟨fun {_} => ⟨fun hc => evaluationJointlyReflectsColimits _
      (fun i => isColimitOfPreserves ((evaluation ι C).obj (F.obj i)) hc)⟩⟩

noncomputable instance [HasFiniteLimits C] :
    PreservesFiniteLimits ((whiskeringLeft ι' ι C).obj F) :=
  ⟨fun _ => by infer_instance⟩

noncomputable instance [HasFiniteColimits C] :
    PreservesFiniteColimits ((whiskeringLeft ι' ι C).obj F) :=
  ⟨fun _ => by infer_instance⟩

instance [HasFiniteColimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Epi τ] :
    Epi (whiskerLeft F τ) := ((whiskeringLeft ι' ι C).obj F).map_epi τ

instance [HasFiniteLimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Mono τ] :
  Mono (whiskerLeft F τ) := ((whiskeringLeft ι' ι C).obj F).map_mono τ

instance [HasFiniteColimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Epi τ] (i : ι) :
    Epi (τ.app i) :=
  ((evaluation ι C).obj i).map_epi τ

instance [HasFiniteLimits C] {X Y : ι ⥤ C} (τ : X ⟶ Y) [Mono τ] (i : ι) :
    Mono (τ.app i) :=
  ((evaluation ι C).obj i).map_mono τ

end Limits

end CategoryTheory


variable {C ι : Type _} [Category C] [Abelian C] [Category ι]

namespace CategoryTheory

namespace Abelian

lemma exact_iff_exact_evaluation (S : ShortComplex (ι ⥤ C)) :
    S.Exact ↔ ∀ (i : ι), (S.map ((evaluation ι C).obj i)).Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology,
    fun i => Iso.isZero_iff (S.mapHomologyIso ((evaluation ι C).obj i)),
    evaluation_obj_obj, Functor.isZero_iff]

variable (C ι)

structure SpectralObject where
  H (n : ℤ) : Arrow ι ⥤ C
  δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : Arrow₂.δ₀ ⋙ H n₀ ⟶ Arrow₂.δ₂ ⋙ H n₁
  zero₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (δ n₀ n₁ h).app D ≫ (H n₁).map (Arrow₂.δ₂Toδ₁.app D) = 0
  zero₂ (n : ℤ) (D : Arrow₂ ι) :
    (H n).map (Arrow₂.δ₂Toδ₁.app D) ≫ (H n).map (Arrow₂.δ₁Toδ₀.app D) = 0
  zero₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (H n₀).map (Arrow₂.δ₁Toδ₀.app D) ≫ (δ n₀ n₁ h).app D = 0
  exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₁ n₀ n₁ h D)).Exact
  exact₂ (n : ℤ) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₂ n D)).Exact
  exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₃ n₀ n₁ h D)).Exact

namespace SpectralObject

pp_extended_field_notation H
pp_extended_field_notation δ

attribute [reassoc (attr := simp)] zero₁ zero₂ zero₃

variable {C ι}
variable (X : SpectralObject C ι)

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

@[reassoc]
lemma zero₃' {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)
    (hfg : f ≫ g = fg) (φ : Arrow.mk fg ⟶ Arrow.mk g) (hφ₁ : φ.left = f) (hφ₂ : φ.right = 𝟙 k) :
      (X.H n₀).map φ ≫ (X.δ n₀ n₁ h).app (Arrow₂.mk f g) = 0 := by
  subst hfg
  obtain rfl : φ = (Arrow₂.δ₁Toδ₀.app (Arrow₂.mk f g)) := by
    ext
    . exact hφ₁
    . exact hφ₂
  refine' X.zero₃ n₀ n₁ hn₁ _

def shortComplex₁ : ShortComplex (Arrow₂ ι ⥤ C):=
  ShortComplex.mk (X.δ n₀ n₁ hn₁) (whiskerRight Arrow₂.δ₂Toδ₁ (X.H n₁))
     (by
      ext D
      exact X.zero₁ n₀ n₁ hn₁ D)

pp_extended_field_notation shortComplex₁

def shortComplex₂ : ShortComplex (Arrow₂ ι ⥤ C):=
  ShortComplex.mk (whiskerRight Arrow₂.δ₂Toδ₁ (X.H n₀))
    (whiskerRight Arrow₂.δ₁Toδ₀ (X.H n₀)) (by
      ext D
      exact X.zero₂ n₀ D)

pp_extended_field_notation shortComplex₂

def shortComplex₃ : ShortComplex (Arrow₂ ι ⥤ C) :=
  ShortComplex.mk  (whiskerRight Arrow₂.δ₁Toδ₀ (X.H n₀)) (X.δ n₀ n₁ hn₁)
     (by
      ext D
      exact X.zero₃ n₀ n₁ hn₁ D)

pp_extended_field_notation shortComplex₃

lemma shortComplex₁_exact : (X.shortComplex₁ n₀ n₁ hn₁).Exact := by
  rw [exact_iff_exact_evaluation]
  intro i
  apply X.exact₁

lemma shortComplex₂_exact : (X.shortComplex₂ n₀).Exact := by
  rw [exact_iff_exact_evaluation]
  intro i
  apply X.exact₂

lemma shortComplex₃_exact : (X.shortComplex₃ n₀ n₁ hn₁).Exact := by
  rw [exact_iff_exact_evaluation]
  intro i
  apply X.exact₃

def shortComplex₄ : ShortComplex₄ (Arrow₂ ι ⥤ C) :=
  ShortComplex₄.mk
    (whiskerRight Arrow₂.δ₂Toδ₁ (X.H n₀))
    (whiskerRight Arrow₂.δ₁Toδ₀ (X.H n₀))
    (X.δ n₀ n₁ hn₁)
    (X.shortComplex₂ n₀).zero
    (X.shortComplex₃ n₀ n₁ hn₁).zero

pp_extended_field_notation shortComplex₄

lemma shortComplex₄_exact : (X.shortComplex₄ n₀ n₁ hn₁).Exact where
  exact₁ := X.shortComplex₂_exact n₀
  exact₂ := X.shortComplex₃_exact n₀ n₁ hn₁

-- the homology of this short complex gives the terms in all the pages of the spectral sequence
def shortComplexE' : ShortComplex (Arrow₃ ι ⥤ C) where
  X₁ := Arrow₃.hMor ⋙ X.H n₀
  X₂ := Arrow₃.gMor ⋙ X.H n₁
  X₃ := Arrow₃.fMor ⋙ X.H n₂
  f := whiskerLeft (Arrow₃.δ₀) (X.δ n₀ n₁ hn₁)
  g := whiskerLeft (Arrow₃.δ₃) (X.δ n₁ n₂ hn₂)
  zero := by
    ext D
    have eq := (X.δ n₁ n₂ hn₂).naturality (Arrow₃.δ₃Toδ₂.app D)
    dsimp at eq ⊢
    simp only [Arrow₃.δ₂_map_δ₃Toδ₂_app, Arrow₂.δ₂_obj, Arrow₃.δ₃_obj_f,
      Functor.map_id, comp_id] at eq
    rw [← eq, Arrow₃.δ₀_map_δ₃Toδ₂_app_eq_δ₂Toδ₁_app_δ₀_obj,
      reassoc_of% (X.zero₁ n₀ n₁ hn₁ (Arrow₃.δ₀.obj D)), zero_comp]

pp_extended_field_notation shortComplexE'

noncomputable def cycles : Arrow₂ ι ⥤ C := kernel (X.δ n₀ n₁ hn₁)
noncomputable def cyclesCo : Arrow₂ ι ⥤ C := cokernel (X.δ n₀ n₁ hn₁)

pp_extended_field_notation cycles
pp_extended_field_notation cyclesCo

noncomputable def iCycles : X.cycles n₀ n₁ hn₁ ⟶ Arrow₂.δ₀ ⋙ X.H n₀ := kernel.ι _
noncomputable def pCyclesCo : Arrow₂.δ₂ ⋙ X.H n₁ ⟶ X.cyclesCo n₀ n₁ hn₁ := cokernel.π _

@[reassoc (attr := simp)]
lemma iCycles_comp_δ : X.iCycles n₀ n₁ hn₁ ≫ X.δ n₀ n₁ hn₁ = 0 :=
  kernel.condition _

@[reassoc (attr := simp)]
lemma iCycles_comp_δ_app (D : Arrow₂ ι) :
    (X.iCycles n₀ n₁ hn₁).app D ≫ (X.δ n₀ n₁ hn₁).app D = 0 :=
  congr_app (X.iCycles_comp_δ n₀ n₁ hn₁) D

@[reassoc (attr := simp)]
lemma δ_comp_pCyclesCo : X.δ n₀ n₁ hn₁ ≫ X.pCyclesCo n₀ n₁ hn₁ = 0 :=
  cokernel.condition _

@[reassoc (attr := simp)]
lemma δ_comp_pCyclesCo_app (D : Arrow₂ ι) :
    (X.δ n₀ n₁ hn₁).app D ≫ (X.pCyclesCo n₀ n₁ hn₁).app D = 0 :=
  congr_app (X.δ_comp_pCyclesCo n₀ n₁ hn₁) D

pp_extended_field_notation iCycles
pp_extended_field_notation pCyclesCo

instance : Mono (X.iCycles n₀ n₁ hn₁) := by
  dsimp only [iCycles]
  infer_instance

instance : Epi (X.pCyclesCo n₀ n₁ hn₁) := by
  dsimp only [pCyclesCo]
  infer_instance

noncomputable def cokernelIsoCycles :
    cokernel (whiskerRight Arrow₂.δ₂Toδ₁ (X.H n₀)) ≅ X.cycles n₀ n₁ hn₁ :=
  (X.shortComplex₄_exact n₀ n₁ hn₁).cokerIsoKer

pp_extended_field_notation cokernelIsoCycles

noncomputable def Hδ₁ToCycles : Arrow₂.δ₁ ⋙ X.H n₀ ⟶ X.cycles n₀ n₁ hn₁ :=
  cokernel.π _ ≫ (X.cokernelIsoCycles n₀ n₁ hn₁).hom

pp_extended_field_notation Hδ₁ToCycles

instance : Epi (X.Hδ₁ToCycles n₀ n₁ hn₁) := by
  dsimp [Hδ₁ToCycles]
  apply epi_comp

@[reassoc (attr := simp)]
lemma Hδ₁ToCycles_iCycles :
    X.Hδ₁ToCycles n₀ n₁ hn₁ ≫ X.iCycles n₀ n₁ hn₁ = whiskerRight Arrow₂.δ₁Toδ₀ (X.H n₀) := by
  dsimp only [Hδ₁ToCycles]
  rw [assoc]
  exact (X.shortComplex₄ n₀ n₁ hn₁).cokerToKer_fac

@[reassoc (attr := simp)]
lemma Hδ₂Toδ₁_Hδ₁ToCycles :
    whiskerRight Arrow₂.δ₂Toδ₁ (X.H n₀) ≫ X.Hδ₁ToCycles n₀ n₁ hn₁ = 0 := by
  rw [← cancel_mono (X.iCycles n₀ n₁ hn₁), assoc, Hδ₁ToCycles_iCycles, zero_comp]
  exact (X.shortComplex₂ n₀).zero

@[simps]
noncomputable def cokernelSequenceCycles : ShortComplex (Arrow₂ ι ⥤ C) :=
  ShortComplex.mk _ _ (X.Hδ₂Toδ₁_Hδ₁ToCycles n₀ n₁ hn₁)

pp_extended_field_notation cokernelSequenceCycles

instance : Epi (X.cokernelSequenceCycles n₀ n₁ hn₁).g := by
  dsimp only [cokernelSequenceCycles]
  infer_instance

lemma cokernelSequenceCycles_exact : (X.cokernelSequenceCycles n₀ n₁ hn₁).Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  exact IsColimit.ofIsoColimit (cokernelIsCokernel _)
    (Cofork.ext (X.cokernelIsoCycles n₀ n₁ hn₁) (by simp [Hδ₁ToCycles]))

@[simps!]
noncomputable def δ₀PullbackCokernelSequenceCycles :
    ShortComplex (Arrow₃ ι ⥤ C) :=
  (X.cokernelSequenceCycles n₀ n₁ hn₁).map (((whiskeringLeft _ _ C).obj (Arrow₃.δ₀)))

pp_extended_field_notation δ₀PullbackCokernelSequenceCycles

instance : Epi (X.δ₀PullbackCokernelSequenceCycles n₀ n₁ hn₁).g := by
  dsimp [δ₀PullbackCokernelSequenceCycles]
  infer_instance

lemma δ₀PullbackCokernelSequenceCycles_exact :
    (X.δ₀PullbackCokernelSequenceCycles n₀ n₁ hn₁).Exact :=
  (X.cokernelSequenceCycles_exact n₀ n₁ hn₁).map (((whiskeringLeft _ _ C).obj (Arrow₃.δ₀)))

noncomputable def Ψ : Arrow₃.δ₀ ⋙ X.cycles n₀ n₁ hn₁ ⟶ Arrow₃.δ₃ ⋙ X.cyclesCo n₀ n₁ hn₁ :=
  (X.δ₀PullbackCokernelSequenceCycles_exact n₀ n₁ hn₁).desc
    (whiskerLeft Arrow₃.δ₂ (X.δ n₀ n₁ hn₁) ≫ whiskerLeft Arrow₃.δ₃ (X.pCyclesCo n₀ n₁ hn₁)) (by
      ext A
      dsimp
      erw [reassoc_of% ((X.δ n₀ n₁ hn₁).naturality (Arrow₃.δ₃Toδ₂.app A)), Functor.map_id]
      rw [id_comp, ← NatTrans.comp_app, δ_comp_pCyclesCo, zero_app])

pp_extended_field_notation Ψ

lemma comp_Ψ : (X.δ₀PullbackCokernelSequenceCycles n₀ n₁ hn₁).g ≫ X.Ψ n₀ n₁ hn₁ =
    (whiskerLeft Arrow₃.δ₂ (X.δ n₀ n₁ hn₁) ≫ whiskerLeft Arrow₃.δ₃ (X.pCyclesCo n₀ n₁ hn₁)) :=
  (X.δ₀PullbackCokernelSequenceCycles_exact n₀ n₁ hn₁).g_desc _ _

@[reassoc (attr := simp)]
lemma comp_ψ_app (D : Arrow₃ ι) :
  (X.Hδ₁ToCycles n₀ n₁ hn₁).app (Arrow₃.δ₀.obj D) ≫ (X.Ψ n₀ n₁ hn₁).app D =
    (X.δ n₀ n₁ hn₁).app (Arrow₃.δ₂.obj D) ≫ (X.pCyclesCo n₀ n₁ hn₁).app (Arrow₃.δ₃.obj D) :=
  congr_app (X.comp_Ψ n₀ n₁ hn₁) D

@[simps]
noncomputable def shortComplex₄Ψ : ShortComplex₄ (Arrow₃ ι ⥤ C) where
  X₁ := Arrow₃.δ₁ ⋙ X.cycles n₀ n₁ hn₁
  X₂ := Arrow₃.δ₀ ⋙ X.cycles n₀ n₁ hn₁
  X₃ := Arrow₃.δ₃ ⋙ X.cyclesCo n₀ n₁ hn₁
  X₄ := Arrow₃.δ₂ ⋙ X.cyclesCo n₀ n₁ hn₁
  f := whiskerRight Arrow₃.δ₁Toδ₀ (X.cycles n₀ n₁ hn₁)
  g := X.Ψ n₀ n₁ hn₁
  h := whiskerRight Arrow₃.δ₃Toδ₂ (X.cyclesCo n₀ n₁ hn₁)
  zero₁ := by
    ext D
    simp only [Functor.comp_obj, NatTrans.comp_app, whiskerRight_app, zero_app,
      ← cancel_epi ((X.Hδ₁ToCycles n₀ n₁ hn₁).app _), comp_zero, ← NatTrans.naturality_assoc,
      comp_ψ_app, Functor.comp_map]
    erw [X.zero₃'_assoc n₀ n₁ hn₁ _ _ _ _ _ rfl (by rfl), zero_comp]
    dsimp
    rw [assoc]
  zero₂ := by
    ext D
    rw [← cancel_epi ((X.Hδ₁ToCycles n₀ n₁ hn₁).app (Arrow₃.δ₀.obj D))]
    simp only [zero_app, comp_zero, NatTrans.comp_app, comp_ψ_app_assoc, whiskerRight_app,
      ← NatTrans.naturality, Functor.comp_map, Arrow₃.δ₂_map_δ₃Toδ₂_app, Functor.map_id,
      Functor.comp_obj, id_comp, δ_comp_pCyclesCo_app]

pp_extended_field_notation shortComplex₄Ψ

/-lemma shortComplex₄Ψ_exact : (X.shortComplex₄Ψ n₀ n₁ hn₁).Exact where
  exact₁ := by
    rw [exact_iff_exact_evaluation]
    rintro ⟨f₁, f₂, f₃⟩
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    dsimp
    intro A₀ x₀ hx₀
    dsimp [Arrow₃.δ₀] at x₀ hx₀
    obtain ⟨A₁, π₁, hπ₁, x₁, fac⟩ := surjective_up_to_refinements_of_epi
      ((X.Hδ₁ToCycles n₀ n₁ hn₁).app (Arrow₂.mk f₂ f₃)) x₀
    sorry
  exact₂ := sorry

noncomputable def Φ : cokernel (whiskerRight Arrow₃.δ₁Toδ₀ (X.cycles n₀ n₁ hn₁)) ≅
    kernel (whiskerRight Arrow₃.δ₃Toδ₂ (X.cyclesCo n₀ n₁ hn₁)) :=
  (X.shortComplex₄Ψ_exact n₀ n₁ hn₁).cokerIsoKer

pp_extended_field_notation Φ-/

end SpectralObject

end Abelian

end CategoryTheory
