/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

#align_import category_theory.preadditive.injective_resolution from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a quasi-isomorphism `I.ι` from the cochain complex consisting just of `Z`
in degree zero to `I.cocomplex`.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/


noncomputable section

universe v u

namespace CategoryTheory

open Limits HomologicalComplex CochainComplex

<<<<<<< HEAD
open Injective

variable [HasZeroObject C] [HasZeroMorphisms C]
=======
variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
>>>>>>> origin/homology-sequence-computation
/--
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism from the complex consisting of just `Z` supported in degree `0`.
-/
-- @[nolint has_nonempty_instance]
structure InjectiveResolution (Z : C) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C ℕ
<<<<<<< HEAD
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  hι : QuasiIso ι := by infer_instance
  --exact₀ : Exact (ι.f 0) (cocomplex.d 0 1) := by infer_instance
  --exact : ∀ n, Exact (cocomplex.d n (n + 1)) (cocomplex.d (n + 1) (n + 2)) := by infer_instance
  --mono : Mono (ι.f 0) := by infer_instance
=======
  /-- the cochain complex must be degreewise injective -/
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  /-- the cochain complex must have homology -/
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  /-- the morphism from the single cochain complex with `Z` in degree `0` -/
  ι : (single₀ C).obj Z ⟶ cocomplex
  /-- the morphism from the single cochain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance
>>>>>>> origin/homology-sequence-computation
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution CategoryTheory.InjectiveResolution

open InjectiveResolution in
<<<<<<< HEAD
attribute [inherit_doc InjectiveResolution]
  cocomplex InjectiveResolution.ι injective

attribute [instance] InjectiveResolution.injective InjectiveResolution.hasHomology
  InjectiveResolution.hι
=======
attribute [instance] injective quasiIso hasHomology
>>>>>>> origin/homology-sequence-computation

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

<<<<<<< HEAD
lemma cocomplex_exactAt_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
    I.cocomplex.ExactAt n.succ := by
  rw [← quasiIsoAt_iff_exactAt I.ι n.succ (CochainComplex.single₀_exactAt _ _)]
  · infer_instance

=======
variable {Z : C} (I : InjectiveResolution Z)

lemma cocomplex_exactAt_succ (n : ℕ) :
    I.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  · infer_instance

lemma exact_succ (n : ℕ):
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

>>>>>>> origin/homology-sequence-computation
@[simp]
theorem ι_f_succ (n : ℕ) : I.ι.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.ι_f_succ CategoryTheory.InjectiveResolution.ι_f_succ

-- Porting note: removed @[simp] simp can prove this
<<<<<<< HEAD
theorem ι_f_zero_comp_complex_d {Z : C} (I : InjectiveResolution Z) :
=======
@[reassoc]
theorem ι_f_zero_comp_complex_d :
>>>>>>> origin/homology-sequence-computation
    I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.ι_f_zero_comp_complex_d CategoryTheory.InjectiveResolution.ι_f_zero_comp_complex_d

-- Porting note: removed @[simp] simp can prove this
<<<<<<< HEAD
theorem complex_d_comp {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
=======
theorem complex_d_comp (n : ℕ) :
>>>>>>> origin/homology-sequence-computation
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
  simp
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.complex_d_comp CategoryTheory.InjectiveResolution.complex_d_comp

<<<<<<< HEAD
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
=======
/-- The (limit) kernel fork given by the composition
`Z ⟶ I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
@[simp]
def kernelFork : KernelFork (I.cocomplex.d 0 1) :=
  KernelFork.ofι _ I.ι_f_zero_comp_complex_d

/-- `Z` is the kernel of `I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
def isLimitKernelFork : IsLimit (I.kernelFork) := by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

instance (n : ℕ) : Mono (I.ι.f n) := by
  cases n
  · exact mono_of_isLimit_fork I.isLimitKernelFork
>>>>>>> origin/homology-sequence-computation
  · rw [ι_f_succ]; infer_instance

variable (Z)

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
@[simps]
def self [Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
<<<<<<< HEAD
    cases n <;>
      · dsimp
        infer_instance
=======
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp
>>>>>>> origin/homology-sequence-computation
set_option linter.uppercaseLean3 false in
#align category_theory.InjectiveResolution.self CategoryTheory.InjectiveResolution.self

end InjectiveResolution

end CategoryTheory
