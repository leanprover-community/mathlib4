/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization
/-!

# Ext Commute with Flat Base Change

The `Ext` functor over `R`-module commute with flat base change if `R` is Noethrian and two modules
are finitely generated.

-/

universe v v' u u'

variable (R : Type u) [CommRing R]

section basechange

open CategoryTheory

variable {R} (S : Type u') [CommRing S] [Algebra R S]

lemma isBaseChange_comp_equiv {M1 M2 N : Type*} [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup N]
    [Module R M1] [Module R M2] [Module R N] [Module S N] [IsScalarTower R S N] (e : M1 ≃ₗ[R] M2)
    (f : M2 →ₗ[R] N) (isb : IsBaseChange S f) : IsBaseChange S (f.comp e.toLinearMap) := by
  sorry

section extendscalars'

namespace ModuleCat

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Small.{v'} M] [Small.{v'} N] : Small.{v'} (TensorProduct R M N) :=
  let _ : Small.{v'} (FreeAddMonoid (M × N)) :=
    small_of_surjective (FreeAddMonoid.freeAddMonoidCongr (equivShrink (M × N)).symm).surjective
  small_of_surjective Quotient.mk''_surjective

noncomputable def ExtendScalars'.obj' [UnivLE.{v, v'}] [Small.{v'} S]
    (M : ModuleCat.{v} R) : ModuleCat.{v'} S :=
  ModuleCat.of S (Shrink.{v'} (TensorProduct R S M))

noncomputable def ExtendScalars'.map' [UnivLE.{v, v'}] [Small.{v'} S]
    {M1 M2 : ModuleCat.{v} R} (g : M1 ⟶ M2) : obj' S M1 ⟶ obj' S M2 :=
  ModuleCat.ofHom (((Shrink.linearEquiv.{v'} S (TensorProduct R S M2)).symm.toLinearMap.comp
    (g.hom.baseChange S)).comp (Shrink.linearEquiv.{v'} S (TensorProduct R S M1)).toLinearMap)

lemma ExtendScalars'.map'_id [UnivLE.{v, v'}] [Small.{v'} S]
    (M : ModuleCat.{v} R) : map' S (𝟙 M) = 𝟙 (obj' S M) := by
  simp [map', obj']

lemma ExtendScalars'.map'_comp [UnivLE.{v, v'}] [Small.{v'} S]
    {M1 M2 M3 : ModuleCat.{v} R} (g : M1 ⟶ M2) (h : M2 ⟶ M3) :
    map' S (g ≫ h) = (map' S g) ≫ (map' S h) := by
  ext x
  change (Shrink.linearEquiv S (TensorProduct R S M3)).symm
      (((h.hom ∘ₗ g.hom).baseChange S) ((Shrink.linearEquiv S (TensorProduct R S M1)) x)) =
      (Shrink.linearEquiv S (TensorProduct R S M3)).symm ((h.hom.baseChange S)
      ((Shrink.linearEquiv S (TensorProduct R S M2))
      ((Shrink.linearEquiv S (TensorProduct R S M2)).symm ((g.hom.baseChange S)
      ((Shrink.linearEquiv S (TensorProduct R S M1)) x)))))
  rw [LinearEquiv.apply_symm_apply]
  simp [LinearMap.baseChange_comp]

variable (R) in
noncomputable def extendScalars' [UnivLE.{v, v'}] [Small.{v'} S] :
    (ModuleCat.{v} R) ⥤ (ModuleCat.{v'} S) where
  obj := ExtendScalars'.obj' S
  map := ExtendScalars'.map' S
  map_id := ExtendScalars'.map'_id S
  map_comp := ExtendScalars'.map'_comp S

variable [UnivLE.{v, v'}] [Small.{v'} S]

instance : (extendScalars' R S).Additive where
  map_add {X Y} f g := by
    simp only [extendScalars', ExtendScalars'.map', hom_add, LinearMap.baseChange_add]
    ext x
    simp

lemma extendScalars'_map_shortExact [Module.Flat R S]
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.ShortExact) :
    (T.map (extendScalars' R S)).ShortExact where
  exact := by
    have exac : Function.Exact (T.f.hom.baseChange S) (T.g.hom.baseChange S) :=
      lTensor_exact S ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp h.exact)
        h.moduleCat_surjective_g
    have : Function.Exact (ExtendScalars'.map' S T.f) (ExtendScalars'.map' S T.g) := by
      simp only [ExtendScalars'.map', hom_ofHom, LinearMap.exact_iff, LinearEquiv.range_comp]
      rw [LinearMap.comp_assoc, LinearEquiv.ker_comp]
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
      convert exac ((Shrink.linearEquiv S (TensorProduct R S T.X₂)) x)
      rw [LinearMap.range_comp, ← Submodule.comap_equiv_eq_map_symm, Submodule.mem_comap]
      rfl
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr this
  mono_f := by
    have inj : Function.Injective (T.f.hom.baseChange S) :=
      Module.Flat.lTensor_preserves_injective_linearMap T.f.hom h.moduleCat_injective_f
    have : Function.Injective (ExtendScalars'.map' S T.f) := by
      simp only [ExtendScalars'.map', hom_ofHom, ← LinearMap.ker_eq_bot]
      rw [LinearMap.comp_assoc, LinearEquiv.ker_comp, LinearMap.ker_eq_bot]
      exact inj.comp (LinearEquiv.injective _)
    exact (mono_iff_injective (T.map (extendScalars' R S)).f).mpr this
  epi_g := by
    have surj : Function.Surjective (T.g.hom.baseChange S) :=
      LinearMap.lTensor_surjective S h.moduleCat_surjective_g
    have : Function.Surjective (ExtendScalars'.map' S T.g) := by
      simp only [ExtendScalars'.map', hom_ofHom, ← LinearMap.range_eq_top]
      rw [LinearEquiv.range_comp, LinearMap.range_eq_top]
      exact (Shrink.linearEquiv S (TensorProduct R S T.X₃)).symm.surjective.comp surj
    exact (epi_iff_surjective (T.map (extendScalars' R S)).g).mpr this

instance [Module.Flat R S] : Limits.PreservesFiniteLimits (extendScalars' R S) := by
  have := (((extendScalars' R S).exact_tfae.out 0 3).mp (extendScalars'_map_shortExact S))
  exact this.1

instance [Module.Flat R S] : Limits.PreservesFiniteColimits (extendScalars' R S) := by
  have := (((extendScalars' R S).exact_tfae.out 0 3).mp (extendScalars'_map_shortExact S))
  exact this.2

namespace Algebra'

variable (R) in
scoped instance extendScalars'_linear :
    letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
    Functor.Linear R (ModuleCat.extendScalars' R S) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  {
  map_smul {X Y} g r := by
    simp only [extendScalars', ExtendScalars'.map', hom_smul, LinearMap.baseChange_smul]
    let _ : IsScalarTower R S (ExtendScalars'.obj' S X ⟶ ExtendScalars'.obj' S Y) := {
      smul_assoc r s z := by
        rw [Algebra.smul_def, ← smul_smul]
        rfl }
    rw [← algebraMap_smul S r, ← algebraMap_smul S r, LinearMap.comp_smul, LinearMap.smul_comp]
    rfl }

end Algebra'

end ModuleCat

end extendscalars'

section

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}
  (comm1 : h₂.comp f = (f'.restrictScalars R).comp h₁)
  (comm2 : h₃.comp g = (g'.restrictScalars R).comp h₂)

include comm1 comm2 in
lemma IsBaseChange.of_right_exact (isb1 : IsBaseChange S h₁) (isb2 : IsBaseChange S h₂)
    (exac1 : Function.Exact f g) (surj1 : Function.Surjective g)
    (exac2 : Function.Exact f' g') (surj2 : Function.Surjective g') : IsBaseChange S h₃ := by
  change Function.Bijective _ at isb1 isb2 ⊢
  refine LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exac2 isb1.2 isb2 ?_ surj2
  · ext s m
    simpa using congr(s • ($comm1 m)).symm
  · ext s m
    simpa using congr(s • ($comm2 m)).symm
  · simp only [LinearMap.coe_restrictScalars, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact S exac1 surj1
  · simp only [LinearMap.coe_restrictScalars, LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S surj1

include comm1 comm2 in
lemma IsBaseChange.of_left_exact [Module.Flat R S] (isb2 : IsBaseChange S h₂)
    (isb3 : IsBaseChange S h₃) (exac1 : Function.Exact f g) (inj1 : Function.Injective f)
    (exac2 : Function.Exact f' g') (inj2 : Function.Injective f') : IsBaseChange S h₁ := by
  change Function.Bijective _ at isb2 isb3 ⊢
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exac2 isb2 isb3.1 ?_ inj2
  · ext s m
    simpa using congr(s • ($comm1 m)).symm
  · ext s m
    simpa using congr(s • ($comm2 m)).symm
  · simp only [LinearMap.coe_restrictScalars, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact S exac1
  · simp only [LinearMap.coe_restrictScalars, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f inj1

lemma IsBaseChange.of_equiv_left (f : M₁ ≃ₗ[R] M₂) (f' : N₁ ≃ₗ[S] N₂)
    (comm1 : h₂.comp f.toLinearMap = (f'.restrictScalars R).comp h₁)
    (isb1 : IsBaseChange S h₁) : IsBaseChange S h₂ :=
  IsBaseChange.of_right_exact S (f := (0 : Unit →ₗ[R] M₁)) (f' := (0 : Unit →ₗ[S] N₁))
    (g := f) (g' := f') 0 h₁ h₂ (by simp) comm1 (show Function.Bijective _ from by simp) isb1
      (fun y ↦ (by simpa using eq_comm)) f.bijective.2 (fun y ↦ (by simpa using eq_comm))
        f'.bijective.2

lemma IsBaseChange.of_equiv_right (f : M₁ ≃ₗ[R] M₂) (f' : N₁ ≃ₗ[S] N₂)
    (comm1 : h₂.comp f.toLinearMap = (f'.restrictScalars R).comp h₁)
    (isb2 : IsBaseChange S h₂) : IsBaseChange S h₁ := by
  refine IsBaseChange.of_equiv_left S h₂ h₁ f.symm f'.symm (LinearMap.ext fun y ↦ ?_) isb2
  obtain ⟨y, rfl⟩ := f.surjective y
  exact f'.injective (by simpa using congr($comm1 y).symm)

end

section

variable (R) (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open TensorProduct in
theorem Module.FinitePresentation.isBaseChange_map [Module.Flat R S]
    [Module.FinitePresentation R M] : IsBaseChange S (LinearMap.baseChangeHom R S M N) := by
  have h_free (n : ℕ) : IsBaseChange S (LinearMap.baseChangeHom R S (Fin n → R) N) := by
    let e₁ := TensorProduct.piRight R S S (fun _ : Fin n ↦ R)
    let e₂ := LinearEquiv.congrLeft (S ⊗[R] N) S e₁.symm
    let e₃ := (LinearEquiv.piCongrRight (fun _ ↦ (LinearMap.ringLmapEquivSelf ..).symm ≪≫ₗ
      (LinearEquiv.congrLeft (S ⊗[R] N) S (AlgebraTensorModule.rid R S S).symm))) ≪≫ₗ
      (LinearMap.lsum S (fun _ : Fin n ↦ _) S) ≪≫ₗ e₂
    let e₄ : ((Fin n → R) →ₗ[R] N) ≃ₗ[R] (Fin n → N) :=
      (LinearMap.lsum R (fun _ : Fin n ↦ R) R).symm ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ ↦ LinearMap.ringLmapEquivSelf ..)
    refine IsBaseChange.of_equiv
      ((e₄.baseChange R S) ≪≫ₗ (TensorProduct.piRight R S S (fun _ : Fin n ↦ N)) ≪≫ₗ e₃)
        (fun f ↦ TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext fun s ↦ ?_))
    ext i
    simpa [e₄, e₃, e₂, e₁, LinearEquiv.congrLeft, LinearEquiv.baseChange] using
      (tmul_eq_smul_one_tmul s (f (Pi.single i 1))).symm
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  refine IsBaseChange.of_left_exact S (f := f.lcomp R N) (g := g.lcomp R N)
    (f' := (f.baseChange S).lcomp S (S ⊗[R] N)) (g' := (g.baseChange S).lcomp S (S ⊗[R] N))
    _ _ _ ?_ ?_ (h_free n) (h_free m) ?_ ?_ ?_ ?_
  · exact LinearMap.ext fun φ ↦ TensorProduct.AlgebraTensorModule.curry_injective
      (LinearMap.ext fun s ↦ (LinearMap.ext fun m ↦ (by simp)))
  · exact LinearMap.ext fun φ ↦ TensorProduct.AlgebraTensorModule.curry_injective
      (LinearMap.ext fun s ↦ (LinearMap.ext fun m ↦ (by simp)))

  -- Waiting for the left exactness of hom
  all_goals sorry

end

section

open Abelian

variable [UnivLE.{v, v'}] [Small.{v', u'} S]

universe w w'

variable [UnivLE.{v, w}] [UnivLE.{v', w'}]

instance hasExt_of_small1 [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

instance hasExt_of_small2 [Small.{v'} S] : CategoryTheory.HasExt.{w'} (ModuleCat.{v'} S) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w'} (ModuleCat.{v'} S)

variable [Small.{v} R]

noncomputable instance (n : ℕ) (M N : ModuleCat.{v'} S) : Module R (Ext M N n) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  inferInstance

instance (n : ℕ) (M N : ModuleCat.{v'} S) : IsScalarTower R S (Ext M N n) where
  smul_assoc r s z := by
    simp only [Ext.smul_eq_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Linear.comp_smul, Category.comp_id]
    rw [Algebra.smul_def, ← smul_smul]
    rfl

instance (M N : ModuleCat.{v'} S) : Module R (M ⟶ N) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  inferInstance

instance (M N : ModuleCat.{v'} S) : IsScalarTower R S (M ⟶ N) where
  smul_assoc r s x := by
    rw [Algebra.smul_def, ← smul_smul]
    rfl

noncomputable def ModuleCat.extendScalars'_map_LinearMap (M N : ModuleCat.{v} R) :
  (M ⟶ N) →ₗ[R] ((ModuleCat.extendScalars'.{v, v'} R S).obj M ⟶
    (ModuleCat.extendScalars'.{v, v'} R S).obj N) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  letI := ModuleCat.Algebra'.extendScalars'_linear.{v, v'} R S
  (ModuleCat.extendScalars'.{v, v'} R S).mapLinearMap R (X := M) (Y := N)

omit [UnivLE.{v, w}] [UnivLE.{v', w'}] [Small.{v, u} R] in
lemma ModuleCat.extendScalars'_map_LinearMap_eq_mapAddHom (M N : ModuleCat.{v} R) :
  extendScalars'_map_LinearMap.{v, v'} S M N =
  (ModuleCat.extendScalars'.{v, v'} R S).mapAddHom (X := M) (Y := N) := rfl

omit [UnivLE.{v, w}] [UnivLE.{v', w'}] [Small.{v, u} R] in
lemma CategoryTheory.isBaseChange_hom [IsNoetherianRing R] [Module.Flat R S]
    (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N] :
    IsBaseChange S (ModuleCat.extendScalars'_map_LinearMap.{v, v'} S M N) := by
  let _ : SMulCommClass S R (Shrink.{v', max v u'} (TensorProduct R S N)) :=
    Equiv.smulCommClass S R (equivShrink (TensorProduct R S ↑N)).symm
  let hmod : Module R (Shrink.{v'} (TensorProduct R S M) →ₗ[S] Shrink.{v'} (TensorProduct R S N)) :=
    LinearMap.module
  let _ :  Module R (((ModuleCat.extendScalars'.{v, v'} R S).obj M) →ₗ[S]
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N)) := hmod
  let hsca : IsScalarTower R S
    (Shrink.{v'} (TensorProduct R S M) →ₗ[S] Shrink.{v'} (TensorProduct R S N)) := {
    smul_assoc r s x := by
      ext
      simp }
  let _ :  IsScalarTower R S (((ModuleCat.extendScalars'.{v, v'} R S).obj M) →ₗ[S]
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N)) := hsca
  have : ModuleCat.extendScalars'_map_LinearMap.{v, v'} S M N =
    ((ModuleCat.homLinearEquiv (S := S)).symm.restrictScalars R).toLinearMap.comp
    (((((Shrink.linearEquiv.{v'} S (TensorProduct R S N)).symm.congrRight).trans
    ((Shrink.linearEquiv.{v'} S (TensorProduct R S M)).symm.congrLeft (Shrink.{v'}
    (TensorProduct R S N)) S)).restrictScalars R).toLinearMap.comp
    ((LinearMap.baseChangeHom R S M N).comp ModuleCat.homLinearEquiv.toLinearMap)) := by
    apply LinearMap.ext
    intro f
    rfl
  rw [this]
  apply IsBaseChange.comp
  · apply IsBaseChange.comp
    · apply isBaseChange_comp_equiv _ _
      let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      exact Module.FinitePresentation.isBaseChange_map R S M N
    · exact IsBaseChange.ofEquiv _
  · exact IsBaseChange.ofEquiv _

noncomputable def ModuleCat.extendScalars'.mapExtLinearMap [Module.Flat R S]
  (M N : ModuleCat.{v} R) (n : ℕ) :
  Ext M N n →ₗ[R] Ext ((ModuleCat.extendScalars'.{v, v'} R S).obj M)
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N) n :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  letI := ModuleCat.Algebra'.extendScalars'_linear.{v, v'} R S
  ((ModuleCat.extendScalars'.{v, v'} R S).mapExtLinearMap R M N n)

lemma ModuleCat.extendScalars'.mapExtLinearMap_eq_mapExt [Module.Flat R S]
  (M N : ModuleCat.{v} R) (n : ℕ) : extendScalars'.mapExtLinearMap.{v, v'} S M N n =
    (ModuleCat.extendScalars'.{v, v'} R S).mapExt M N n := rfl

open ModuleCat

set_option maxHeartbeats 350000 in
-- The dimension shifting is just too complicated
theorem CategoryTheory.Abelian.Ext.isBaseChange_aux [IsNoetherianRing R] [Module.Flat R S]
    (M N : ModuleCat.{v} R) [Module.Finite R M] [Module.Finite R N] (n : ℕ) :
    IsBaseChange S (extendScalars'.mapExtLinearMap.{v, v'} S M N n) := by
  induction n generalizing M N
  · have isb : IsBaseChange S (extendScalars'_map_LinearMap.{v, v'} S M N) :=
      CategoryTheory.isBaseChange_hom.{v, v'} S M N
    convert ((IsBaseChange.ofEquiv linearEquiv₀).comp isb).comp
      (IsBaseChange.ofEquiv linearEquiv₀.symm)
    ext x
    rcases (Ext.mk₀_bijective M N).2 x with ⟨y, hy⟩
    simp only [← hy, extendScalars'.mapExtLinearMap_eq_mapExt, mapExt_mk₀_eq_mk₀_map, linearEquiv₀,
      addEquiv₀, homEquiv₀, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      AddEquiv.coe_mk, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.symm_mk,
      Equiv.symm_symm, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.coe_symm_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]
    congr 1
  · rename_i n ih _ _
    rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
    let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
    have surjf : Function.Surjective f := by simpa [f] using hf'
    let T : ShortComplex (ModuleCat.{v} R) := {
      f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
      g := ModuleCat.ofHom.{v} f
      zero := by
        ext x
        simp }
    have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) := by
      intro x
      simp [T]
    have T_exact : T.ShortExact := {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr T_exact'
      mono_f := (ModuleCat.mono_iff_injective T.f).mpr (LinearMap.ker f).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective T.g).mpr surjf}
    let _ : Module.Finite R T.X₂ := by
      simp [T, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
    have _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
    have _ : Module.Free R T.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
    have proj := ModuleCat.projective_of_categoryTheory_projective T.X₂
    let TS := (T.map (ModuleCat.extendScalars'.{v, v'} R S))
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.extendScalars'.{v, v'} R S)
    have _ : Module.Free S TS.X₂ := by
      simp only [ModuleCat.extendScalars', ShortComplex.map_X₂, ModuleCat.ExtendScalars'.obj', TS]
      exact Module.Free.of_equiv (Shrink.linearEquiv S (TensorProduct R S T.X₂)).symm
    have proj' := ModuleCat.projective_of_categoryTheory_projective TS.X₂
    let NS := ((ModuleCat.extendScalars'.{v, v'} R S).obj N)
    let f : Ext T.X₂ N n →ₗ[R] Ext T.X₁ N n := {
      __ := (mk₀ T.f).precomp N (zero_add n)
      map_smul' r x := by simp }
    let g : Ext T.X₁ N n →ₗ[R] Ext T.X₃ N (n + 1) := {
      __ := T_exact.extClass.precomp N (add_comm 1 n)
      map_smul' r x := by simp }
    have exac1 : Function.Exact f g := (ShortComplex.ab_exact_iff_function_exact  _).mp
        (Ext.contravariant_sequence_exact₁' T_exact N n (n + 1) (add_comm 1 n))
    have isz1 : Limits.IsZero (AddCommGrpCat.of (Ext T.X₂ N (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective)
    have surj1 : Function.Surjective g := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.contravariant_sequence_exact₃' T_exact N n (n + 1) (add_comm 1 n)).epi_f
      (isz1.eq_zero_of_tgt _))
    let f' : Ext TS.X₂ NS n →ₗ[S] Ext TS.X₁ NS n := {
      __ := (mk₀ TS.f).precomp NS (zero_add n)
      map_smul' s x := by simp }
    let g' : Ext TS.X₁ NS n →ₗ[S] Ext TS.X₃ NS (n + 1) := {
      __ := TS_exact.extClass.precomp NS (add_comm 1 n)
      map_smul' s x := by simp }
    have exac2 : Function.Exact f' g' := (ShortComplex.ab_exact_iff_function_exact  _).mp
        (Ext.contravariant_sequence_exact₁' TS_exact NS n (n + 1) (add_comm 1 n))
    have isz2 : Limits.IsZero (AddCommGrpCat.of (Ext TS.X₂ NS (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective)
    have surj2 : Function.Surjective g' := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.contravariant_sequence_exact₃' TS_exact NS n (n + 1) (add_comm 1 n)).epi_f
      (isz2.eq_zero_of_tgt _))
    let h₁ : Ext T.X₂ N n →ₗ[R] Ext TS.X₂ NS n := extendScalars'.mapExtLinearMap.{v, v'} S T.X₂ N n
    let h₂ : Ext T.X₁ N n →ₗ[R] Ext TS.X₁ NS n := extendScalars'.mapExtLinearMap.{v, v'} S T.X₁ N n
    let h₃ : Ext T.X₃ N (n + 1) →ₗ[R] Ext TS.X₃ NS (n + 1) :=
      extendScalars'.mapExtLinearMap.{v, v'} S T.X₃ N (n + 1)
    apply IsBaseChange.of_right_exact S h₁ h₂ h₃ _ _ (ih T.X₂ N) (ih T.X₁ N) exac1 surj1 exac2 surj2
    · ext x
      simp only [ShortComplex.map_X₁, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, bilinearComp_apply_apply, ShortComplex.map_X₂, ShortComplex.map_f,
        ← mapExt_mk₀_eq_mk₀_map, LinearMap.coe_restrictScalars, TS, h₂, f, f', h₁]
      rw [extendScalars'.mapExtLinearMap_eq_mapExt, extendScalars'.mapExtLinearMap_eq_mapExt,
        Ext.mapExt_comp_eq_comp_mapExt]
    · ext x
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        bilinearComp_apply_apply, LinearMap.coe_restrictScalars, h₃, g, g', h₂]
      have : (ModuleCat.extendScalars'.{v, v'} R S).mapExt T.X₃ T.X₁ 1 T_exact.extClass =
        TS_exact.extClass :=
        Ext.mapExt_extClass_eq_extClass_map (ModuleCat.extendScalars'.{v, v'} R S) T_exact
      erw [extendScalars'.mapExtLinearMap_eq_mapExt, extendScalars'.mapExtLinearMap_eq_mapExt]
      rw [Ext.mapExt_comp_eq_comp_mapExt, this]

noncomputable def ModuleCat.iso_extendScalars'_of_isBaseChange {M : ModuleCat.{v} R}
    {MS : ModuleCat.{v'} S} (f : M →ₗ[R] (RestrictScalars R S MS))
    (isb1 : letI := RestrictScalars.moduleOrig R S MS; IsBaseChange S f) :
    MS ≅ (ModuleCat.extendScalars'.{v, v'} R S).obj M :=
  letI := RestrictScalars.moduleOrig R S MS
  (isb1.equiv.symm.trans (Shrink.linearEquiv S (TensorProduct R S M)).symm).toModuleIso

noncomputable def ModuleCat.iso_extendScalars'_of_isBaseChange' {M : ModuleCat.{v} R}
    {MS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS] (f : M →ₗ[R] MS)
    (isb1 : IsBaseChange S f) : MS ≅ (ModuleCat.extendScalars'.{v, v'} R S).obj M :=
  letI := RestrictScalars.moduleOrig R S MS
  (isb1.equiv.symm.trans (Shrink.linearEquiv S (TensorProduct R S M)).symm).toModuleIso

namespace CategoryTheory.Abelian

noncomputable def Ext.isBaseChangeMap_aux {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} (f : M →ₗ[R] (RestrictScalars R S MS))
    (isb1 : letI := RestrictScalars.moduleOrig R S MS; IsBaseChange S f)
    (g : N →ₗ[R] (RestrictScalars R S NS))
    (isb2 : letI := RestrictScalars.moduleOrig R S NS; IsBaseChange S g)
    (n : ℕ) : Ext ((ModuleCat.extendScalars'.{v, v'} R S).obj M)
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N) n ≃ₗ[S] Ext MS NS n := {
  __ := (((extFunctorObj.{w'} ((ModuleCat.extendScalars'.{v, v'} R S).obj M) n).mapIso
  (iso_extendScalars'_of_isBaseChange S g isb2).symm).trans (((extFunctor.{w'} n).mapIso
  (iso_extendScalars'_of_isBaseChange S f isb1).op).app NS)).addCommGroupIsoToAddEquiv
  map_smul' s x := by simp [Iso.addCommGroupIsoToAddEquiv] }

noncomputable def Ext.isBaseChangeMap_aux' {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS]
    [Module R NS] [IsScalarTower R S NS] (f : M →ₗ[R] MS) (isb1 : IsBaseChange S f)
    (g : N →ₗ[R] NS) (isb2 : IsBaseChange S g) (n : ℕ) :
    Ext ((ModuleCat.extendScalars'.{v, v'} R S).obj M)
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N) n ≃ₗ[S] Ext MS NS n := {
  __ := (((extFunctorObj.{w'} ((ModuleCat.extendScalars'.{v, v'} R S).obj M) n).mapIso
  (iso_extendScalars'_of_isBaseChange' S g isb2).symm).trans (((extFunctor.{w'} n).mapIso
  (iso_extendScalars'_of_isBaseChange' S f isb1).op).app NS)).addCommGroupIsoToAddEquiv
  map_smul' s x := by simp [Iso.addCommGroupIsoToAddEquiv] }

noncomputable def Ext.isBaseChangeMap [Module.Flat R S] {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} (f : M →ₗ[R] (RestrictScalars R S MS))
    (isb1 : letI := RestrictScalars.moduleOrig R S MS; IsBaseChange S f)
    (g : N →ₗ[R] (RestrictScalars R S NS))
    (isb2 : letI := RestrictScalars.moduleOrig R S NS; IsBaseChange S g)
    (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
  ((Ext.isBaseChangeMap_aux S f isb1 g isb2 n).restrictScalars R).toLinearMap.comp
    (extendScalars'.mapExtLinearMap.{v, v'} S M N n)

noncomputable def Ext.isBaseChangeMap' [Module.Flat R S] {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS]
    [Module R NS] [IsScalarTower R S NS] (f : M →ₗ[R] MS) (isb1 : IsBaseChange S f)
    (g : N →ₗ[R] NS) (isb2 : IsBaseChange S g) (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
  ((Ext.isBaseChangeMap_aux' S f isb1 g isb2 n).restrictScalars R).toLinearMap.comp
    (extendScalars'.mapExtLinearMap.{v, v'} S M N n)

--This is false alarm
set_option linter.unusedSectionVars false in
@[nolint unusedArguments]
theorem Ext.isBaseChange [IsNoetherianRing R] [Module.Flat R S] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N] {MS NS : ModuleCat.{v'} S}
    (f : M →ₗ[R] (RestrictScalars R S MS))
    (isb1 : letI := RestrictScalars.moduleOrig R S MS; IsBaseChange S f)
    (g : N →ₗ[R] (RestrictScalars R S NS))
    (isb2 : letI := RestrictScalars.moduleOrig R S NS; IsBaseChange S g)
    (n : ℕ) : IsBaseChange S (Ext.isBaseChangeMap.{v, v'} S f isb1 g isb2 n) :=
  (Ext.isBaseChange_aux.{v, v'} S M N n).comp
  (IsBaseChange.ofEquiv (isBaseChangeMap_aux S f isb1 g isb2 n))

--This is false alarm
set_option linter.unusedSectionVars false in
@[nolint unusedArguments]
theorem Ext.isBaseChange' [IsNoetherianRing R] [Module.Flat R S] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Module.Finite R N] {MS NS : ModuleCat.{v'} S}
    [Module R MS] [IsScalarTower R S MS] [Module R NS] [IsScalarTower R S NS]
    (f : M →ₗ[R] MS) (isb1 : IsBaseChange S f)
    (g : N →ₗ[R] NS) (isb2 : IsBaseChange S g)
    (n : ℕ) : IsBaseChange S (Ext.isBaseChangeMap'.{v, v'} S f isb1 g isb2 n) :=
  (Ext.isBaseChange_aux.{v, v'} S M N n).comp
  (IsBaseChange.ofEquiv (isBaseChangeMap_aux' S f isb1 g isb2 n))

end CategoryTheory.Abelian

end

end basechange

section Localization

namespace CategoryTheory.Abelian

open ModuleCat

universe w w'

variable (S : Submonoid R) (A : Type u') [CommRing A] [Algebra R A] [IsLocalization S A]

variable [UnivLE.{v, v'}] [Small.{v', u'} A] [UnivLE.{v, w}] [UnivLE.{v', w'}] [Small.{v, u} R]
  [Small.{v', u'} A]

variable {R}

noncomputable def Ext.isLocalizedModuleMap {M N : ModuleCat.{v} R} {MS NS : ModuleCat.{v'} A}
    (f : M →ₗ[R] (RestrictScalars R A MS))
    (isl1 : letI := RestrictScalars.moduleOrig R A MS; IsLocalizedModule S f)
    (g : N →ₗ[R] (RestrictScalars R A NS))
    (isl2 : letI := RestrictScalars.moduleOrig R A NS; IsLocalizedModule S g)
    (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
    letI := IsLocalization.flat A S
    letI := RestrictScalars.moduleOrig R A MS
    letI := RestrictScalars.moduleOrig R A NS
    (Ext.isBaseChangeMap.{v, v'} A f (IsLocalizedModule.isBaseChange S A f) g
      (IsLocalizedModule.isBaseChange S A g) n)

noncomputable def Ext.isLocalizedModuleMap' {M N : ModuleCat.{v} R} {MS NS : ModuleCat.{v'} A}
    [Module R MS] [IsScalarTower R A MS] [Module R NS] [IsScalarTower R A NS]
    (f : M →ₗ[R] MS) (isl1 : IsLocalizedModule S f) (g : N →ₗ[R] NS) (isl2 : IsLocalizedModule S g)
    (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
    letI := IsLocalization.flat A S
    (Ext.isBaseChangeMap'.{v, v'} A f (IsLocalizedModule.isBaseChange S A f) g
      (IsLocalizedModule.isBaseChange S A g) n)

--This is false alarm
set_option linter.unusedSectionVars false in
@[nolint unusedArguments]
theorem Ext.isLocalizedModule [IsNoetherianRing R] {M N : ModuleCat.{v} R}
    [Module.Finite R M] [Module.Finite R N] {MS NS : ModuleCat.{v'} A}
    (f : M →ₗ[R] (RestrictScalars R A MS))
    (isl1 : letI := RestrictScalars.moduleOrig R A MS; IsLocalizedModule S f)
    (g : N →ₗ[R] (RestrictScalars R A NS))
    (isl2 : letI := RestrictScalars.moduleOrig R A NS; IsLocalizedModule S g) (n : ℕ) :
    IsLocalizedModule S (Ext.isLocalizedModuleMap.{v, v'} S A f isl1 g isl2 n) :=
  letI := IsLocalization.flat A S
  letI := RestrictScalars.moduleOrig R A MS
  letI := RestrictScalars.moduleOrig R A NS
  (isLocalizedModule_iff_isBaseChange S A _).mpr (Ext.isBaseChange.{v, v'} A M N
    f (IsLocalizedModule.isBaseChange S A f) g (IsLocalizedModule.isBaseChange S A g) n)

--This is false alarm
set_option linter.unusedSectionVars false in
@[nolint unusedArguments]
theorem Ext.isLocalizedModule' [IsNoetherianRing R] {M N : ModuleCat.{v} R}
    [Module.Finite R M] [Module.Finite R N] {MS NS : ModuleCat.{v'} A}
    [Module R MS] [IsScalarTower R A MS] [Module R NS] [IsScalarTower R A NS]
    (f : M →ₗ[R] MS) (isl1 : IsLocalizedModule S f) (g : N →ₗ[R] NS) (isl2 : IsLocalizedModule S g)
    (n : ℕ) : IsLocalizedModule S (Ext.isLocalizedModuleMap'.{v, v'} S A f isl1 g isl2 n) :=
  letI := IsLocalization.flat A S
  (isLocalizedModule_iff_isBaseChange S A _).mpr (Ext.isBaseChange'.{v, v'} A M N
    f (IsLocalizedModule.isBaseChange S A f) g (IsLocalizedModule.isBaseChange S A g) n)

end CategoryTheory.Abelian

end Localization
