/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# ...


-/

@[expose] public section

open CategoryTheory Limits

-- to be moved
section

variable {C : Type*} [Category* C]

namespace CochainComplex.Plus

variable [HasZeroMorphisms C] [HasZeroObject C]

variable (C) in
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (.up ℤ) n) (fun _ ↦ ⟨n, inferInstance⟩)

end CochainComplex.Plus

variable [Abelian C] [HasDerivedCategory C]

variable (C) in
@[simps! hom_app inv_app]
noncomputable def DerivedCategory.Plus.singleFunctorIso (n : ℤ) :
    CochainComplex.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Q ≅ singleFunctor C n :=
  Iso.refl _

end

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C]

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
  isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective _ _ (by
    dsimp [CochainComplex.Plus.singleFunctor, ObjectProperty.lift]
    infer_instance)

noncomputable def toRightDerived₀ : F ⟶ F.rightDerived 0 :=
  sorry ≫ whiskerLeft (CochainComplex.Plus.singleFunctor C 0)
    (whiskerRight F.rightDerivedFunctorPlusUnit (DerivedCategory.Plus.homologyFunctor D 0)) ≫
    whiskerLeft _ (associator _ _ _).hom ≫ (associator _ _ _).inv ≫
    whiskerRight (DerivedCategory.Plus.singleFunctorIso C 0).hom _

instance (X : C) [Injective X] : IsIso (F.toRightDerived₀.app X) := sorry

end Functor

namespace ShortComplex.ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (F : C ⥤ D) [F.Additive]

include hS in
lemma mono_rightDerived_map_f :
    Mono ((F.rightDerived 0).map S.f) := by
  have := hS
  sorry

end ShortComplex.ShortExact

namespace Functor

variable (F : C ⥤ D) [F.Additive]

instance : (F.rightDerived 0).PreservesMonomorphisms where
  preserves f _ := by
    have : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    exact this.mono_rightDerived_map_f F

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
