/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!

# Ext Commute with Flat Base Change

The `Ext` functor over `R`-module commute with flat base change if `R` is Noethrian and two modules
are finitely generated.

-/

@[expose] public section

universe v v' u u'

variable (R : Type u) [CommRing R]

section basechange

open CategoryTheory

variable {R} (S : Type u') [CommRing S] [Algebra R S]

section extendscalars'

namespace ModuleCat

instance (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Small.{v'} M] [Small.{v'} N] : Small.{v'} (TensorProduct R M N) :=
  let _ : Small.{v'} (FreeAddMonoid (M × N)) :=
    small_of_surjective (FreeAddMonoid.freeAddMonoidCongr (equivShrink (M × N)).symm).surjective
  small_of_surjective Quotient.mk''_surjective

/-- Auxiliary construction for `ModuleCat.ExtendScalars'.obj`,
turning an `R`-module into an `S`-module by `M` ↦ `Shrink S ⨂ M`. -/
noncomputable def ExtendScalars'.obj' [UnivLE.{v, v'}] [Small.{v'} S]
    (M : ModuleCat.{v} R) : ModuleCat.{v'} S :=
  ModuleCat.of S (Shrink.{v'} (TensorProduct R S M))

/-- Auxiliary construction for `ModuleCat.ExtendScalars'.map`,
sending `l : M1 ⟶ M2` to `s ⊗ m ↦ s ⊗ l m` with compostion of `Shrink.linearEquiv`. -/
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
/-- A version of `ModuleCat.extendScalars` with more general universe level,
turning an `R`-module into an `S`-module by `M` ↦ `Shrink S ⨂ M`,
sending `l : M1 ⟶ M2` to `s ⊗ m ↦ s ⊗ l m` with compostion of `Shrink.linearEquiv`. -/
noncomputable def extendScalars' [UnivLE.{v, v'}] [Small.{v'} S] :
    (ModuleCat.{v} R) ⥤ (ModuleCat.{v'} S) where
  obj := ExtendScalars'.obj' S
  map := ExtendScalars'.map' S
  map_id := ExtendScalars'.map'_id S
  map_comp := ExtendScalars'.map'_comp S

variable [UnivLE.{v, v'}] [Small.{v'} S]

set_option backward.isDefEq.respectTransparency false in
instance : (extendScalars' R S).Additive where
  map_add {X Y} f g := by
    simp only [extendScalars', ExtendScalars'.map', hom_add, LinearMap.baseChange_add]
    ext x
    simp

set_option backward.isDefEq.respectTransparency false in
lemma extendScalars'_map_exact [Module.Flat R S]
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.Exact) :
    (T.map (extendScalars' R S)).Exact := by
  have exac : Function.Exact (T.f.hom.baseChange S) (T.g.hom.baseChange S) :=
    Module.Flat.lTensor_exact S
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp h)
  have : Function.Exact (ExtendScalars'.map' S T.f) (ExtendScalars'.map' S T.g) := by
    simp only [ExtendScalars'.map', hom_ofHom, LinearMap.exact_iff, LinearEquiv.range_comp]
    rw [LinearMap.comp_assoc, LinearEquiv.ker_comp]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    convert exac ((Shrink.linearEquiv S (TensorProduct R S T.X₂)) x)
    rw [LinearMap.range_comp, ← Submodule.comap_equiv_eq_map_symm, Submodule.mem_comap]
    rfl
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr this

instance [Module.Flat R S] : Limits.PreservesFiniteLimits (extendScalars' R S) := by
  have := (((extendScalars' R S).exact_tfae.out 1 3).mp (extendScalars'_map_exact S))
  exact this.1

instance [Module.Flat R S] : Limits.PreservesFiniteColimits (extendScalars' R S) := by
  have := (((extendScalars' R S).exact_tfae.out 1 3).mp (extendScalars'_map_exact S))
  exact this.2

namespace Algebra'

set_option backward.isDefEq.respectTransparency false in
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

open Abelian

variable [UnivLE.{v, v'}] [Small.{v} R] [Small.{v'} S]

noncomputable instance (n : ℕ) (M N : ModuleCat.{v'} S) : Module R (Ext M N n) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance (n : ℕ) (M N : ModuleCat.{v'} S) : IsScalarTower R S (Ext M N n) where
  smul_assoc r s z := by
    simp only [Ext.smul_eq_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Linear.comp_smul, Category.comp_id]
    rw [Algebra.smul_def, ← smul_smul]
    rfl

instance (M N : ModuleCat.{v'} S) : Module R (M ⟶ N) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance (M N : ModuleCat.{v'} S) : IsScalarTower R S (M ⟶ N) where
  smul_assoc r s x := by
    rw [Algebra.smul_def, ← smul_smul]
    rfl

/-- The separate definition of `(ModuleCat.extendScalars' R S).mapLinearMap`
to avoid some instance in namespace `ModuleCat.Algebra`. -/
noncomputable def ModuleCat.extendScalars'_map_LinearMap (M N : ModuleCat.{v} R) :
  (M ⟶ N) →ₗ[R] ((ModuleCat.extendScalars'.{v, v'} R S).obj M ⟶
    (ModuleCat.extendScalars'.{v, v'} R S).obj N) :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  letI := ModuleCat.Algebra'.extendScalars'_linear.{v, v'} R S
  (ModuleCat.extendScalars'.{v, v'} R S).mapLinearMap R (X := M) (Y := N)

omit [Small.{v} R] in
lemma ModuleCat.extendScalars'_map_LinearMap_eq_mapAddHom (M N : ModuleCat.{v} R) :
  extendScalars'_map_LinearMap.{v, v'} S M N =
  (ModuleCat.extendScalars'.{v, v'} R S).mapAddHom (X := M) (Y := N) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [Small.{v} R] in
lemma ModuleCat.isBaseChange_hom [Module.Flat R S]
    (M N : ModuleCat.{v} R) [Module.FinitePresentation R M] :
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
    ((LinearMap.baseChangeHom R S M N).comp ModuleCat.homLinearEquiv.toLinearMap)) := rfl
  rw [this]
  apply (IsBaseChange.comp _ (IsBaseChange.ofEquiv _)).comp (IsBaseChange.ofEquiv _)
  exact (Module.FinitePresentation.isBaseChange_map R M N S).comp_equiv _ _

/-- The map between `Ext` induced by `ModuleCat.extendScalars' R S`,
separated out to avoid some instance in namespace `ModuleCat.Algebra`. -/
noncomputable def ModuleCat.extendScalars'.mapExtLinearMap [Module.Flat R S]
  (M N : ModuleCat.{v} R) (n : ℕ) :
  Ext M N n →ₗ[R] Ext ((ModuleCat.extendScalars'.{v, v'} R S).obj M)
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N) n :=
  letI : Linear R (ModuleCat.{v'} S) := ModuleCat.Algebra.instLinear
  letI := ModuleCat.Algebra'.extendScalars'_linear.{v, v'} R S
  ((ModuleCat.extendScalars'.{v, v'} R S).mapExtLinearMap R M N n)

lemma ModuleCat.extendScalars'.mapExtLinearMap_eq_mapExt [Module.Flat R S]
  (M N : ModuleCat.{v} R) (n : ℕ) : ⇑(extendScalars'.mapExtLinearMap.{v, v'} S M N n) =
    Ext.mapExactFunctor (ModuleCat.extendScalars'.{v, v'} R S) := rfl

open ModuleCat

set_option backward.isDefEq.respectTransparency false in
theorem CategoryTheory.Abelian.Ext.isBaseChange_aux [IsNoetherianRing R] [Module.Flat R S]
    (M N : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ) :
    IsBaseChange S (extendScalars'.mapExtLinearMap.{v, v'} S M N n) := by
  induction n generalizing M N
  · have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
    have isb : IsBaseChange S (extendScalars'_map_LinearMap.{v, v'} S M N) :=
      ModuleCat.isBaseChange_hom.{v, v'} S M N
    convert ((IsBaseChange.ofEquiv linearEquiv₀).comp isb).comp
      (IsBaseChange.ofEquiv linearEquiv₀.symm)
    ext x
    rcases (Ext.mk₀_bijective M N).2 x with ⟨y, hy⟩
    simp only [← hy, extendScalars'.mapExtLinearMap_eq_mapExt, mapExactFunctor_mk₀, linearEquiv₀,
      addEquiv₀, homEquiv₀, AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      AddEquiv.coe_mk, Equiv.invFun_as_coe, AddEquiv.coe_toEquiv_symm, AddEquiv.symm_mk,
      Equiv.symm_symm, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      LinearEquiv.coe_symm_mk', LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]
    congr 1
  · rename_i n ih _
    rcases Module.exists_finite_presentation R M with ⟨L, _, _, _, _, f, surjf⟩
    let T : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
    have T_exact : T.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    let TS := (T.map (ModuleCat.extendScalars'.{v, v'} R S))
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.extendScalars'.{v, v'} R S)
    have _ : Module.Free S TS.X₂ := by
      simp only [ModuleCat.extendScalars', ShortComplex.map_X₂, ModuleCat.ExtendScalars'.obj', TS]
      exact Module.Free.of_equiv (Shrink.linearEquiv S (TensorProduct R S T.X₂)).symm
    let NS := ((ModuleCat.extendScalars'.{v, v'} R S).obj N)
    let f : Ext T.X₂ N n →ₗ[R] Ext T.X₁ N n := {
      __ := (mk₀ T.f).precomp N (zero_add n)
      map_smul' r x := by simp }
    let g : Ext T.X₁ N n →ₗ[R] Ext T.X₃ N (n + 1) := {
      __ := T_exact.extClass.precomp N (add_comm 1 n)
      map_smul' r x := by simp }
    have exac1 : Function.Exact f g := (ShortComplex.ab_exact_iff_function_exact  _).mp
        (Ext.contravariant_sequence_exact₁' T_exact N n (n + 1) (add_comm 1 n))
    have surj1 : Function.Surjective g :=
      precomp_extClass_surjective_of_projective_X₂ N T_exact n
    let f' : Ext TS.X₂ NS n →ₗ[S] Ext TS.X₁ NS n := {
      __ := (mk₀ TS.f).precomp NS (zero_add n)
      map_smul' s x := by simp }
    let g' : Ext TS.X₁ NS n →ₗ[S] Ext TS.X₃ NS (n + 1) := {
      __ := TS_exact.extClass.precomp NS (add_comm 1 n)
      map_smul' s x := by simp }
    have exac2 : Function.Exact f' g' := (ShortComplex.ab_exact_iff_function_exact  _).mp
        (Ext.contravariant_sequence_exact₁' TS_exact NS n (n + 1) (add_comm 1 n))
    have surj2 : Function.Surjective g' :=
      precomp_extClass_surjective_of_projective_X₂ NS TS_exact n
    let h₁ : Ext T.X₂ N n →ₗ[R] Ext TS.X₂ NS n := extendScalars'.mapExtLinearMap.{v, v'} S T.X₂ N n
    let h₂ : Ext T.X₁ N n →ₗ[R] Ext TS.X₁ NS n := extendScalars'.mapExtLinearMap.{v, v'} S T.X₁ N n
    let h₃ : Ext T.X₃ N (n + 1) →ₗ[R] Ext TS.X₃ NS (n + 1) :=
      extendScalars'.mapExtLinearMap.{v, v'} S T.X₃ N (n + 1)
    apply IsBaseChange.of_right_exact S h₁ h₂ h₃ _ _ (ih T.X₂ N) (ih T.X₁ N) exac1 surj1 exac2 surj2
    · ext x
      simp only [ShortComplex.map_X₁, ZeroHom.toFun_eq_coe,
        AddMonoidHom.toZeroHom_coe, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk,
        Function.comp_apply, bilinearComp_apply_apply, ShortComplex.map_X₂, ShortComplex.map_f,
        ← mapExactFunctor_mk₀, LinearMap.coe_restrictScalars, TS, h₂, f, f', h₁]
      rw [extendScalars'.mapExtLinearMap_eq_mapExt, extendScalars'.mapExtLinearMap_eq_mapExt,
        Ext.mapExactFunctor_comp]
    · ext x
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
        LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        bilinearComp_apply_apply, LinearMap.coe_restrictScalars, h₃, g, g', h₂]
      rw [← Ext.mapExactFunctor_extClass (ModuleCat.extendScalars'.{v, v'} R S) T_exact]
      exact Ext.mapExactFunctor_comp (ModuleCat.extendScalars'.{v, v'} R S) _ x (add_comm 1 n)

/-- If `MS` in `ModuleCat S` is base change of an `R`-module `M`,
then it is isomporhic to `(ModuleCat.extendScalars' R S).obj M`. -/
noncomputable def ModuleCat.iso_extendScalars'_of_isBaseChange' {M : ModuleCat.{v} R}
    {MS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS] (f : M →ₗ[R] MS)
    (isb1 : IsBaseChange S f) : MS ≅ (ModuleCat.extendScalars'.{v, v'} R S).obj M :=
  (isb1.equiv.symm.trans (Shrink.linearEquiv S (TensorProduct R S M)).symm).toModuleIso

namespace CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false in
/-- The isomprohism on `Ext` induced by `ModuleCat.iso_extendScalars'_of_isBaseChange'`. -/
noncomputable def Ext.isBaseChangeMap_aux' {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS]
    [Module R NS] [IsScalarTower R S NS] (f : M →ₗ[R] MS) (isb1 : IsBaseChange S f)
    (g : N →ₗ[R] NS) (isb2 : IsBaseChange S g) (n : ℕ) :
    Ext ((ModuleCat.extendScalars'.{v, v'} R S).obj M)
    ((ModuleCat.extendScalars'.{v, v'} R S).obj N) n ≃ₗ[S] Ext MS NS n := {
  __ := (((extFunctorObj ((ModuleCat.extendScalars'.{v, v'} R S).obj M) n).mapIso
  (iso_extendScalars'_of_isBaseChange' S g isb2).symm).trans (((extFunctor n).mapIso
  (iso_extendScalars'_of_isBaseChange' S f isb1).op).app NS)).addCommGroupIsoToAddEquiv
  map_smul' s x := by simp [Iso.addCommGroupIsoToAddEquiv] }

/-- Compostion of `Ext.isBaseChangeMap_aux'` and `ModuleCat.extendScalars'.mapExtLinearMap`. -/
noncomputable def Ext.isBaseChangeMap' [Module.Flat R S] {M N : ModuleCat.{v} R}
    {MS NS : ModuleCat.{v'} S} [Module R MS] [IsScalarTower R S MS]
    [Module R NS] [IsScalarTower R S NS] (f : M →ₗ[R] MS) (isb1 : IsBaseChange S f)
    (g : N →ₗ[R] NS) (isb2 : IsBaseChange S g) (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
  ((Ext.isBaseChangeMap_aux' S f isb1 g isb2 n).restrictScalars R).toLinearMap.comp
    (extendScalars'.mapExtLinearMap.{v, v'} S M N n)

theorem Ext.isBaseChange' [IsNoetherianRing R] [Module.Flat R S] (M N : ModuleCat.{v} R)
    [Module.Finite R M] {MS NS : ModuleCat.{v'} S}
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

variable (S : Submonoid R) (A : Type u') [CommRing A] [Algebra R A] [IsLocalization S A]

variable [UnivLE.{v, v'}] [Small.{v} R] [Small.{v'} A]

variable {R}

/-- `Ext.isBaseChangeMap'` specifying to localization. -/
noncomputable def Ext.isLocalizedModuleMap' {M N : ModuleCat.{v} R} {MS NS : ModuleCat.{v'} A}
    [Module R MS] [IsScalarTower R A MS] [Module R NS] [IsScalarTower R A NS]
    (f : M →ₗ[R] MS) (isl1 : IsLocalizedModule S f) (g : N →ₗ[R] NS) (isl2 : IsLocalizedModule S g)
    (n : ℕ) : Ext M N n →ₗ[R] Ext MS NS n :=
  haveI := IsLocalization.flat A S
  (Ext.isBaseChangeMap'.{v, v'} A f (IsLocalizedModule.isBaseChange S A f) g
    (IsLocalizedModule.isBaseChange S A g) n)

theorem Ext.isLocalizedModule' [IsNoetherianRing R] {M N : ModuleCat.{v} R}
    [Module.Finite R M] {MS NS : ModuleCat.{v'} A}
    [Module R MS] [IsScalarTower R A MS] [Module R NS] [IsScalarTower R A NS]
    (f : M →ₗ[R] MS) (isl1 : IsLocalizedModule S f) (g : N →ₗ[R] NS) (isl2 : IsLocalizedModule S g)
    (n : ℕ) : IsLocalizedModule S (Ext.isLocalizedModuleMap'.{v, v'} S A f isl1 g isl2 n) :=
  haveI := IsLocalization.flat A S
  (isLocalizedModule_iff_isBaseChange S A _).mpr (Ext.isBaseChange'.{v, v'} A M N
    f (IsLocalizedModule.isBaseChange S A f) g (IsLocalizedModule.isBaseChange S A g) n)

end CategoryTheory.Abelian

end Localization
