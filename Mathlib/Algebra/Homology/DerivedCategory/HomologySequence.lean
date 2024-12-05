/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The homology sequence

In this file, we construct `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ`,
show that they are homological functors which form a shift sequence, and construct
the long exact homology sequences associated to distinguished triangles in the
derived category.

-/

universe w v u

open CategoryTheory Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace DerivedCategory

/-- The homology functor `DerivedCategory C ⥤ C` in degree `n : ℤ`. -/
noncomputable def homologyFunctor (n : ℤ) : DerivedCategory C ⥤ C :=
  HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up ℤ) n

/-- The homology functor on the derived category is induced by the homology
functor on the category of cochain complexes. -/
noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up ℤ) n

/-- The homology functor on the derived category is induced by the homology
functor on the homotopy category of cochain complexes. -/
noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up ℤ) n

noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostcompQIso C)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      HomologicalComplex.homologyFunctorSingleIso _ _ _

variable {C} in
lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _

lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro hf n
    infer_instance
  · intro hf
    let g := (Functor.mapArrow Qh).objPreimage (Arrow.mk f)
    refine ((MorphismProperty.isomorphisms (DerivedCategory C)).arrow_iso_iff
      ((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f))).1 ?_
    change IsIso (Qh.map g.hom)
    rw [isIso_Qh_map_iff, HomotopyCategory.mem_quasiIso_iff]
    intro n
    have e : Arrow.mk ((homologyFunctor C n).map f) ≅
        Arrow.mk ((HomotopyCategory.homologyFunctor _ _ n).map g.hom) :=
      ((homologyFunctor C n).mapArrow.mapIso
        (((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
        ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
    exact ((MorphismProperty.isomorphisms C).arrow_iso_iff e).1 (hf n)

instance (n : ℤ) : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

/-- The functors `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ` are part
of a "shift sequence", i.e. they satisfy compatibilities with shifts. -/
noncomputable instance : (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) ℤ
    (homologyFunctor C) (homologyFunctorFactorsh C)

variable {C}

namespace HomologySequence

/-- The connecting homomorphism on the homology sequence attached to a distinguished
triangle in the derived category. -/
noncomputable def δ (T : Triangle (DerivedCategory C))
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C n₀).obj T.obj₃ ⟶ (homologyFunctor C n₁).obj T.obj₁ :=
  (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
include hT

@[reassoc (attr := simp)]
lemma comp_δ : (homologyFunctor C n₀).map T.mor₂ ≫ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

@[reassoc (attr := simp)]
lemma δ_comp : δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h

lemma exact₂ :
    (ShortComplex.mk ((homologyFunctor C n₀).map T.mor₁) ((homologyFunctor C n₀).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero])).Exact :=
  (homologyFunctor C 0).homologySequence_exact₂ _ hT _

lemma exact₃ : (ShortComplex.mk _ _ (comp_δ T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h

lemma exact₁ : (ShortComplex.mk _ _ (δ_comp T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h

lemma epi_homologyMap_mor₁_iff :
    Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

lemma mono_homologyMap_mor₁_iff :
    Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

lemma epi_homologyMap_mor₂_iff :
    Epi ((homologyFunctor C n₀).map T.mor₂) ↔ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT _ _ h

lemma mono_homologyMap_mor₂_iff :
    Mono ((homologyFunctor C n₀).map T.mor₂) ↔ (homologyFunctor C n₀).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n₀

lemma isIso_homologyMap_mor₁_iff :
    IsIso ((homologyFunctor C n₁).map T.mor₁) ↔
      δ T n₀ n₁ h  = 0 ∧ (homologyFunctor C n₁).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_isIso_shift_map_mor₁_iff _ hT _ _ h

lemma isIso_homologyMap_mor₂_iff :
    IsIso ((homologyFunctor C n₀).map T.mor₂) ↔
      δ T n₀ n₁ h  = 0 ∧ (homologyFunctor C n₀).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequence_isIso_shift_map_mor₂_iff _ hT _ _ h

end HomologySequence

end DerivedCategory
