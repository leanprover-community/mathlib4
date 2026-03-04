/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# The homology sequence

In this file, we construct `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ`,
show that they are homological functors which form a shift sequence, and construct
the long exact homology sequences associated to distinguished triangles in the
derived category.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

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

variable {C} in
@[reassoc (attr := simp)]
lemma homologyFunctorFactors_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (homologyFunctor C n).map (Q.map f) ≫ (homologyFunctorFactors C n).hom.app L =
    (homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f n :=
  (homologyFunctorFactors C n).hom.naturality f

/-- The homology functor on the derived category is induced by the homology
functor on the homotopy category of cochain complexes. -/
noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up ℤ) n

@[reassoc]
lemma homologyFunctorFactorsh_hom_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (homologyFunctor C n).map ((quotientCompQhIso C).hom.app K) ≫
      (homologyFunctorFactors C n).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).inv.app _ :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

@[reassoc]
lemma homologyFunctorFactorsh_inv_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.app _ ≫
      (homologyFunctorFactors C n).inv.app K ≫
        (homologyFunctor C n).map ((quotientCompQhIso C).inv.app K) :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

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

instance (n : ℤ) : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

/-- The functors `homologyFunctor C n : DerivedCategory C ⥤ C` for all `n : ℤ` are part
of a "shift sequence", i.e. they satisfy compatibilities with shifts. -/
noncomputable instance : (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) ℤ
    (homologyFunctor C) (homologyFunctorFactorsh C)

lemma shift_homologyFunctor (n : ℤ) :
    (homologyFunctor C 0).shift n = homologyFunctor C n := rfl

variable {C}

@[reassoc]
lemma shiftMap_homologyFunctor_map_Qh
    {K L : HomotopyCategory C (.up ℤ)} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a') :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Qh) a a' h =
    (homologyFunctorFactorsh C a).hom.app _ ≫
      (HomotopyCategory.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (homologyFunctorFactorsh C a').inv.app _ :=
  Functor.ShiftSequence.induced_shiftMap ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shiftMap_homologyFunctor_map_Q
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧)
    (a a' : ℤ) (h : n + a = a') :
    (homologyFunctor C 0).shiftMap (ShiftedHom.map f Q) a a' h =
    (homologyFunctorFactors C a).hom.app _ ≫
      (HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftMap f a a' h ≫
        (homologyFunctorFactors C a').inv.app _ := by
  rw [← ShiftedHom.map_naturality_1 f (quotientCompQhIso C),
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.shiftMap_comp', Functor.shiftMap_comp,
    ShiftedHom.comp_map, shiftMap_homologyFunctor_map_Qh,
    homologyFunctorFactorsh_hom_app_quotient_obj,
    homologyFunctorFactorsh_inv_app_quotient_obj,
    HomotopyCategory.homologyFunctor_shiftMap]
  simp [shift_homologyFunctor, ← Functor.map_comp, ← Functor.map_comp_assoc]

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

end HomologySequence

end DerivedCategory
