/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

#align_import category_theory.preadditive.injective_resolution from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a cochain map `I.ι` from cochain complex consisting just of `Z` in degree zero to `C`,
so that the augmented cochain complex is exact.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Injective

variable [HasZeroObject C] [HasZeroMorphisms C]
/--
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

Except in situations where you want to provide a particular injective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `injectiveResolution Z`: the `ℕ`-indexed cochain complex
  (equipped with `injective` and `exact` instances)
* `InjectiveResolution.ι Z`: the cochain map from `(single C _ 0).obj Z` to
  `InjectiveResolution Z` (all the components are equipped with `Mono` instances,
  and when the category is `Abelian` we will show `ι` is a quasi-iso).
-/
-- @[nolint has_nonempty_instance]
structure InjectiveResolution (Z : C) where
  cocomplex : CochainComplex C ℕ
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  hι : QuasiIso ι := by infer_instance
  --exact₀ : Exact (ι.f 0) (cocomplex.d 0 1) := by infer_instance
  --exact : ∀ n, Exact (cocomplex.d n (n + 1)) (cocomplex.d (n + 1) (n + 2)) := by infer_instance
  --mono : Mono (ι.f 0) := by infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution CategoryTheory.InjectiveResolution

open InjectiveResolution in
attribute [inherit_doc InjectiveResolution]
  cocomplex InjectiveResolution.ι injective

attribute [instance] InjectiveResolution.injective InjectiveResolution.hasHomology
  InjectiveResolution.hι

/-- An object admits an injective resolution. -/
class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)
#align category_theory.has_injective_resolution CategoryTheory.HasInjectiveResolution

attribute [inherit_doc HasInjectiveResolution] HasInjectiveResolution.out

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughInjectives C]` and `[Abelian C]`. -/
class HasInjectiveResolutions : Prop where
  out : ∀ Z : C, HasInjectiveResolution Z
#align category_theory.has_injective_resolutions CategoryTheory.HasInjectiveResolutions

attribute [instance 100] HasInjectiveResolutions.out

end

namespace InjectiveResolution

lemma cocomplex_exactAt_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
    I.cocomplex.ExactAt n.succ := by
  rw [← quasiIsoAt_iff_exactAt I.ι n.succ (CochainComplex.single₀_exactAt _ _)]
  · infer_instance

@[simp]
theorem ι_f_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ) : I.ι.f (n + 1) = 0 := by
  apply zero_of_source_iso_zero
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.ι_f_succ CategoryTheory.InjectiveResolution.ι_f_succ

-- Porting note: removed @[simp] simp can prove this
theorem ι_f_zero_comp_complex_d {Z : C} (I : InjectiveResolution Z) :
    I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.ι_f_zero_comp_complex_d CategoryTheory.InjectiveResolution.ι_f_zero_comp_complex_d

-- Porting note: removed @[simp] simp can prove this
theorem complex_d_comp {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.complex_d_comp CategoryTheory.InjectiveResolution.complex_d_comp

@[simps!]
def fork {Z : C} (I : InjectiveResolution Z) : KernelFork (I.cocomplex.d 0 1) :=
  KernelFork.ofι _ I.ι_f_zero_comp_complex_d

def isLimitFork {Z : C} (I : InjectiveResolution Z) : IsLimit I.fork := by
  refine' IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) _
  apply Iso.symm
  refine' Fork.ext ((CochainComplex.single₀Homology₀Iso Z).symm ≪≫ isoOfQuasiIsoAt I.ι 0 ≪≫
    I.cocomplex.isoHomologyπ₀.symm) _
  dsimp [fork]
  -- this may not be optimal...
  simp only [Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality_assoc,
    HomologicalComplex.cyclesMap_i, CochainComplex.single₀_obj_X_0,
    ← cancel_epi (CochainComplex.single₀Homology₀Iso Z).hom,
    ← cancel_epi  (CochainComplex.isoHomologyπ₀ ((CochainComplex.single₀ C).obj Z)).hom,
    Iso.hom_inv_id_assoc, CochainComplex.isoHomologyπ₀_hom,
    CochainComplex.isoHomologyπ₀_hom_inv_id_assoc,
    ← cancel_epi (CochainComplex.single₀Cycles₀Iso Z).inv,
    CochainComplex.single₀Cycles₀Iso_inv_comp_iCycles_assoc Z,
    CochainComplex.single₀_homologyπ_comp_single₀Homology₀Iso_hom_assoc]

instance {Z : C} (I : InjectiveResolution Z) (n : ℕ) : CategoryTheory.Mono (I.ι.f n) := by
  cases n
  · exact mono_of_isLimit_fork I.isLimitFork
  · rw [ι_f_succ]; infer_instance

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
def self (Z : C) [CategoryTheory.Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n <;>
      · dsimp
        infer_instance
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.self CategoryTheory.InjectiveResolution.self

end InjectiveResolution

end CategoryTheory
