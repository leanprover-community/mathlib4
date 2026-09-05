/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# ...


-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

-- to be moved
section

variable {C : Type*} [Category* C]

variable [Abelian C] [HasDerivedCategory C]

variable (C) in
@[simps! hom_app inv_app]
noncomputable def DerivedCategory.Plus.singleFunctorIso (n : ℤ) :
    CochainComplex.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Q ≅ singleFunctor C n :=
  Iso.refl _

namespace CategoryTheory.ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The (distinguished) triangle in the bounded below derived category of `C` given by a
short exact short complex in `C`. -/
noncomputable abbrev singleTrianglePlus : Triangle (DerivedCategory.Plus C) :=
  ObjectProperty.liftTriangle _ hS.singleTriangle ⟨0, by dsimp; infer_instance⟩
    ⟨0, by dsimp; infer_instance⟩ ⟨0, by dsimp; infer_instance⟩

lemma singleTrianglePlus_distinguished :
    hS.singleTrianglePlus ∈ distTriang (DerivedCategory.Plus C) :=
  ObjectProperty.liftTriangle_distinguished _ _ _ _ _ hS.singleTriangle_distinguished

end CategoryTheory.ShortComplex.ShortExact

end


namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

namespace Functor

variable (F : C ⥤ D) [F.Additive]

/-- If `F : C ⥤ D` is an additive functor between abelian categories,
with enough injectives in `C`, and `n : ℕ`, this is `n`th right derived
functors of `F`. It is defined using the (total) right derived
functor `F.rightDerivedFunctorPlus` on the bounded below derived categories. -/
@[implicit_reducible, simps! -isSimp obj map]
noncomputable def rightDerived (n : ℕ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n

instance (n : ℕ) : (F.rightDerived n).Additive := by
  dsimp [rightDerived]
  infer_instance

instance (X : C) (n : ℤ) [Injective X] :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ((CochainComplex.Plus.singleFunctor C n).obj X)) :=
  isIso_rightDerivedFunctorPlusUnit_app_of_injective _ _ n (by dsimp;infer_instance)
    (by dsimp; infer_instance)

noncomputable def toRightDerived₀ : F ⟶ F.rightDerived 0 :=
  F.rightUnitor.inv ≫
  whiskerLeft _ ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso D 0).inv ≫
    whiskerRight (DerivedCategory.Plus.singleFunctorIso D 0).inv _ ≫ (associator _ _ _).hom) ≫
  (associator _ _ _).inv ≫ whiskerRight (F.singleMapCochainComplexPlus 0).inv _ ≫
  (associator _ _ _).inv ≫ whiskerRight (associator _ _ _).hom _ ≫
  (associator _ _ _).hom ≫ whiskerLeft (CochainComplex.Plus.singleFunctor C 0)
  (whiskerRight F.rightDerivedFunctorPlusUnit (DerivedCategory.Plus.homologyFunctor D 0)) ≫
  whiskerLeft _ (associator _ _ _).hom ≫ (associator _ _ _).inv ≫
  whiskerRight (DerivedCategory.Plus.singleFunctorIso C 0).hom _

instance (X : C) [Injective X] : IsIso (F.toRightDerived₀.app X) := by
  dsimp [toRightDerived₀]
  infer_instance

variable {S : ShortComplex C} (hS : S.ShortExact)

noncomputable def rightDerivedδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia) :
    (F.rightDerived n₀).obj S.X₃ ⟶ (F.rightDerived n₁).obj S.X₁ :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
    (F.rightDerivedFunctorPlus.mapTriangle.obj (hS.singleTrianglePlus)) n₀ n₁ (by lia)

include hS in
lemma mono_rightDerived_map_f :
    Mono ((F.rightDerived 0).map S.f) :=
  ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₁ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) (-1) 0 (by simp)).mono_g
        ((DerivedCategory.Plus.isZero_homology_of_isGE
          (F.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₃)) 0 (-1) (by lia)).eq_of_src _ _)

include hS in
lemma rightDerived_exact₂ (n : ℕ) :
    (ShortComplex.mk ((F.rightDerived n).map S.f) ((F.rightDerived n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₂ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) _

@[reassoc (attr := simp)]
lemma rightDerivedδ_comp (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia) :
    F.rightDerivedδ hS n₀ n₁ h ≫ (F.rightDerived n₁).map S.f = 0 :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ_comp
    _ (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) _ _ _

@[reassoc (attr := simp)]
lemma comp_rightDerivedδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia) :
    (F.rightDerived n₀).map S.g ≫ F.rightDerivedδ hS n₀ n₁ h = 0 :=
  (DerivedCategory.Plus.homologyFunctor D 0).comp_homologySequenceδ
    _ (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) _ _ _

lemma rightDerived_exact₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk (F.rightDerivedδ hS n₀ n₁ h) ((F.rightDerived n₁).map S.f)
      (by simp)).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₁ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) _ _ _

lemma rightDerived_exact₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk ((F.rightDerived n₀).map S.g) (F.rightDerivedδ hS n₀ n₁ h)
      (by simp)).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₃ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      hS.singleTrianglePlus_distinguished) _ _ _

instance : (F.rightDerived 0).PreservesMonomorphisms where
  preserves f _ := by
    have : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    simpa using F.mono_rightDerived_map_f this

variable [PreservesFiniteLimits F]

instance (X : C) : Mono (F.toRightDerived₀.app X) :=
  mono_of_mono_fac (F.toRightDerived₀.naturality (Injective.ι X)).symm

instance (X : C) : IsIso (F.toRightDerived₀.app X) := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι X))
  have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  let φ := S.mapNatTrans F.toRightDerived₀
  have : Mono φ.τ₁ := by
    simp only [φ, S, ShortComplex.mapNatTrans_τ₁]
    infer_instance
  have : Epi φ.τ₁ :=
    ShortComplex.epi_of_mono_of_epi_of_mono φ
      (F.preservesFiniteLimits_iff_forall_exact_map_and_mono.mp inferInstance _ hS).1
      (by dsimp; infer_instance)
      (by simp only [ShortComplex.mapNatTrans_τ₂, φ]; infer_instance)
      (by simp only [ShortComplex.mapNatTrans_τ₃, φ]; infer_instance)
  exact isIso_of_mono_of_epi φ.τ₁

instance : IsIso F.toRightDerived₀ := NatIso.isIso_of_isIso_app _

@[simps! hom]
noncomputable def isoRightDerived₀ : F ≅ F.rightDerived 0 :=
  asIso F.toRightDerived₀

@[reassoc (attr := simp)]
lemma isoRightDerived₀_hom_inv_id :
    F.toRightDerived₀ ≫ F.isoRightDerived₀.inv = 𝟙 _ :=
  F.isoRightDerived₀.hom_inv_id

@[reassoc (attr := simp)]
lemma isoRightDerived₀_inv_hom_id :
    F.isoRightDerived₀.inv ≫ F.toRightDerived₀ = 𝟙 _ :=
  F.isoRightDerived₀.inv_hom_id

@[reassoc (attr := simp)]
lemma isoRightDerived₀_hom_inv_id_app (X : C) :
    F.toRightDerived₀.app X ≫ F.isoRightDerived₀.inv.app X = 𝟙 _ :=
  F.isoRightDerived₀.hom_inv_id_app X

@[reassoc (attr := simp)]
lemma isoRightDerived₀_inv_hom_id_app (X : C) :
    F.isoRightDerived₀.inv.app X ≫ F.toRightDerived₀.app X = 𝟙 _ :=
  F.isoRightDerived₀.inv_hom_id_app X

end Functor

end CategoryTheory
