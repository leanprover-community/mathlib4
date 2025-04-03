/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

#align_import category_theory.preadditive.basic from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/


universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    aesop_cat
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    aesop_cat
#align category_theory.preadditive CategoryTheory.Preadditive
#align category_theory.preadditive.add_comp' CategoryTheory.Preadditive.add_comp
#align category_theory.preadditive.comp_add' CategoryTheory.Preadditive.comp_add

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance] Preadditive.homGroup

-- Porting note: simp can prove reassoc version
attribute [reassoc, simp] Preadditive.add_comp

attribute [reassoc] Preadditive.comp_add

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] Preadditive.comp_add

end CategoryTheory

open CategoryTheory

namespace CategoryTheory

namespace Preadditive

section Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

instance inducedCategory : Preadditive.{v} (InducedCategory C F) where
  homGroup P Q := @Preadditive.homGroup C _ _ (F P) (F Q)
  add_comp _ _ _ _ _ _ := add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := comp_add _ _ _ _ _ _
#align category_theory.preadditive.induced_category CategoryTheory.Preadditive.inducedCategory

end InducedCategory

instance fullSubcategory (Z : C → Prop) : Preadditive.{v} (FullSubcategory Z) where
  homGroup P Q := @Preadditive.homGroup C _ _ P.obj Q.obj
  add_comp _ _ _ _ _ _ := add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := comp_add _ _ _ _ _ _
#align category_theory.preadditive.full_subcategory CategoryTheory.Preadditive.fullSubcategory

instance (X : C) : AddCommGroup (End X) := by
  dsimp [End]
  infer_instance

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp
#align category_theory.preadditive.left_comp CategoryTheory.Preadditive.leftComp

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp
#align category_theory.preadditive.right_comp CategoryTheory.Preadditive.rightComp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def compHom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
  AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂
#align category_theory.preadditive.comp_hom CategoryTheory.Preadditive.compHom

-- Porting note: simp can prove the reassoc version
@[reassoc, simp]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'
#align category_theory.preadditive.sub_comp CategoryTheory.Preadditive.sub_comp

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'
#align category_theory.preadditive.comp_sub CategoryTheory.Preadditive.comp_sub

-- Porting note: simp can prove the reassoc version
@[reassoc, simp]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f
#align category_theory.preadditive.neg_comp CategoryTheory.Preadditive.neg_comp

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp]
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g
#align category_theory.preadditive.comp_neg CategoryTheory.Preadditive.comp_neg

@[reassoc]
theorem neg_comp_neg : (-f) ≫ (-g) = f ≫ g := by simp
#align category_theory.preadditive.neg_comp_neg CategoryTheory.Preadditive.neg_comp_neg

theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) n f
#align category_theory.preadditive.nsmul_comp CategoryTheory.Preadditive.nsmul_comp

theorem comp_nsmul (n : ℕ) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (leftComp R f) n g
#align category_theory.preadditive.comp_nsmul CategoryTheory.Preadditive.comp_nsmul

theorem zsmul_comp (n : ℤ) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (rightComp P g) n f
#align category_theory.preadditive.zsmul_comp CategoryTheory.Preadditive.zsmul_comp

theorem comp_zsmul (n : ℤ) : f ≫ (n • g) = n • f ≫ g :=
  map_zsmul (leftComp R f) n g
#align category_theory.preadditive.comp_zsmul CategoryTheory.Preadditive.comp_zsmul

@[reassoc]
theorem comp_sum {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    (f ≫ ∑ j ∈ s, g j) = ∑ j ∈ s, f ≫ g j :=
  map_sum (leftComp R f) _ _
#align category_theory.preadditive.comp_sum CategoryTheory.Preadditive.comp_sum

@[reassoc]
theorem sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j ∈ s, f j) ≫ g = ∑ j ∈ s, f j ≫ g :=
  map_sum (rightComp P g) _ _
#align category_theory.preadditive.sum_comp CategoryTheory.Preadditive.sum_comp

instance {P Q : C} {f : P ⟶ Q} [Epi f] : Epi (-f) :=
  ⟨fun g g' H => by rwa [neg_comp, neg_comp, ← comp_neg, ← comp_neg, cancel_epi, neg_inj] at H⟩

instance {P Q : C} {f : P ⟶ Q} [Mono f] : Mono (-f) :=
  ⟨fun g g' H => by rwa [comp_neg, comp_neg, ← neg_comp, ← neg_comp, cancel_mono, neg_inj] at H⟩

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _
#align category_theory.preadditive.preadditive_has_zero_morphisms CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

/-- Porting note: adding this before the ring instance allowed moduleEndRight to find
the correct Monoid structure on End. Moved both down after preadditiveHasZeroMorphisms
to make use of them -/
instance {X : C} : Semiring (End X) :=
  { End.monoid with
    zero_mul := fun f => by dsimp [mul]; exact HasZeroMorphisms.comp_zero f _
    mul_zero := fun f => by dsimp [mul]; exact HasZeroMorphisms.zero_comp _ f
    left_distrib := fun f g h => Preadditive.add_comp X X X g h f
    right_distrib := fun f g h => Preadditive.comp_add X X X h f g }

/-- Porting note: It looks like Ring's parent classes changed in
Lean 4 so the previous instance needed modification. Was following my nose here. -/
instance {X : C} : Ring (End X) :=
  { (inferInstance : Semiring (End X)),
    (inferInstance : AddCommGroup (End X)) with
    add_left_neg := add_left_neg }

instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add _ _ _ := add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero
#align category_theory.preadditive.module_End_right CategoryTheory.Preadditive.moduleEndRight

theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
    Mono f where
  right_cancellation := fun {Z} g₁ g₂ hg =>
    sub_eq_zero.1 <| h _ <| (map_sub (rightComp Z f) g₁ g₂).trans <| sub_eq_zero.2 hg
#align category_theory.preadditive.mono_of_cancel_zero CategoryTheory.Preadditive.mono_of_cancel_zero

theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
    Mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
  ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩
#align category_theory.preadditive.mono_iff_cancel_zero CategoryTheory.Preadditive.mono_iff_cancel_zero

theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel.ι f = 0) : Mono f :=
  mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]
#align category_theory.preadditive.mono_of_kernel_zero CategoryTheory.Preadditive.mono_of_kernel_zero

lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha, h.eq_of_tgt a 0, Limits.zero_comp])

lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h

theorem epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) :
    Epi f :=
  ⟨fun {Z} g g' hg =>
    sub_eq_zero.1 <| h _ <| (map_sub (leftComp Z f) g g').trans <| sub_eq_zero.2 hg⟩
#align category_theory.preadditive.epi_of_cancel_zero CategoryTheory.Preadditive.epi_of_cancel_zero

theorem epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
    Epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
  ⟨fun _ _ _ => zero_of_epi_comp _, epi_of_cancel_zero f⟩
#align category_theory.preadditive.epi_iff_cancel_zero CategoryTheory.Preadditive.epi_iff_cancel_zero

theorem epi_of_cokernel_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
    (w : cokernel.π f = 0) : Epi f :=
  epi_of_cancel_zero f fun g h => by rw [← cokernel.π_desc f g h, w, Limits.zero_comp]
#align category_theory.preadditive.epi_of_cokernel_zero CategoryTheory.Preadditive.epi_of_cokernel_zero

lemma epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
    (h : IsZero c.pt) : Epi f := epi_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ hg
  rw [← ha, h.eq_of_src a 0, Limits.comp_zero])

lemma epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f)) :
    Epi f :=
  epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

namespace IsIso

@[simp]
theorem comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0 := by
  rw [← IsIso.eq_inv_comp, Limits.comp_zero]
#align category_theory.preadditive.is_iso.comp_left_eq_zero CategoryTheory.Preadditive.IsIso.comp_left_eq_zero

@[simp]
theorem comp_right_eq_zero [IsIso g] : f ≫ g = 0 ↔ f = 0 := by
  rw [← IsIso.eq_comp_inv, Limits.zero_comp]
#align category_theory.preadditive.is_iso.comp_right_eq_zero CategoryTheory.Preadditive.IsIso.comp_right_eq_zero

end IsIso

open ZeroObject

variable [HasZeroObject C]

theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel f ≅ 0) : Mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)
#align category_theory.preadditive.mono_of_kernel_iso_zero CategoryTheory.Preadditive.mono_of_kernel_iso_zero

theorem epi_of_cokernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasColimit (parallelPair f 0)]
    (w : cokernel f ≅ 0) : Epi f :=
  epi_of_cokernel_zero (zero_of_target_iso_zero _ w)
#align category_theory.preadditive.epi_of_cokernel_iso_zero CategoryTheory.Preadditive.epi_of_cokernel_iso_zero

end Preadditive

section Equalizers

variable {C : Type u} [Category.{v} C] [Preadditive C]

section

variable {X Y : C} {f : X ⟶ Y} {g : X ⟶ Y}

/-- Map a kernel cone on the difference of two morphisms to the equalizer fork. -/
@[simps! pt]
def forkOfKernelFork (c : KernelFork (f - g)) : Fork f g :=
  Fork.ofι c.ι <| by rw [← sub_eq_zero, ← comp_sub, c.condition]
#align category_theory.preadditive.fork_of_kernel_fork CategoryTheory.Preadditive.forkOfKernelFork

@[simp]
theorem forkOfKernelFork_ι (c : KernelFork (f - g)) : (forkOfKernelFork c).ι = c.ι :=
  rfl
#align category_theory.preadditive.fork_of_kernel_fork_ι CategoryTheory.Preadditive.forkOfKernelFork_ι

/-- Map any equalizer fork to a cone on the difference of the two morphisms. -/
def kernelForkOfFork (c : Fork f g) : KernelFork (f - g) :=
  Fork.ofι c.ι <| by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]
#align category_theory.preadditive.kernel_fork_of_fork CategoryTheory.Preadditive.kernelForkOfFork

@[simp]
theorem kernelForkOfFork_ι (c : Fork f g) : (kernelForkOfFork c).ι = c.ι :=
  rfl
#align category_theory.preadditive.kernel_fork_of_fork_ι CategoryTheory.Preadditive.kernelForkOfFork_ι

@[simp]
theorem kernelForkOfFork_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
    kernelForkOfFork (Fork.ofι ι w) = KernelFork.ofι ι (by simp [w]) :=
  rfl
#align category_theory.preadditive.kernel_fork_of_fork_of_ι CategoryTheory.Preadditive.kernelForkOfFork_ofι

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
def isLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsLimit c) :
    IsLimit (forkOfKernelFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; aesop_cat⟩
#align category_theory.preadditive.is_limit_fork_of_kernel_fork CategoryTheory.Preadditive.isLimitForkOfKernelFork

@[simp]
theorem isLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsLimit c) (s : Fork f g) :
    (isLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl
#align category_theory.preadditive.is_limit_fork_of_kernel_fork_lift CategoryTheory.Preadditive.isLimitForkOfKernelFork_lift

/-- An equalizer of `f` and `g` is a kernel of `f - g`. -/
def isLimitKernelForkOfFork {c : Fork f g} (i : IsLimit c) : IsLimit (kernelForkOfFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; aesop_cat⟩
#align category_theory.preadditive.is_limit_kernel_fork_of_fork CategoryTheory.Preadditive.isLimitKernelForkOfFork

variable (f g)

/-- A preadditive category has an equalizer for `f` and `g` if it has a kernel for `f - g`. -/
theorem hasEqualizer_of_hasKernel [HasKernel (f - g)] : HasEqualizer f g :=
  HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }
#align category_theory.preadditive.has_equalizer_of_has_kernel CategoryTheory.Preadditive.hasEqualizer_of_hasKernel

/-- A preadditive category has a kernel for `f - g` if it has an equalizer for `f` and `g`. -/
theorem hasKernel_of_hasEqualizer [HasEqualizer f g] : HasKernel (f - g) :=
  HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }
#align category_theory.preadditive.has_kernel_of_has_equalizer CategoryTheory.Preadditive.hasKernel_of_hasEqualizer

variable {f g}

/-- Map a cokernel cocone on the difference of two morphisms to the coequalizer cofork. -/
@[simps! pt]
def coforkOfCokernelCofork (c : CokernelCofork (f - g)) : Cofork f g :=
  Cofork.ofπ c.π <| by rw [← sub_eq_zero, ← sub_comp, c.condition]
#align category_theory.preadditive.cofork_of_cokernel_cofork CategoryTheory.Preadditive.coforkOfCokernelCofork

@[simp]
theorem coforkOfCokernelCofork_π (c : CokernelCofork (f - g)) :
    (coforkOfCokernelCofork c).π = c.π :=
  rfl
#align category_theory.preadditive.cofork_of_cokernel_cofork_π CategoryTheory.Preadditive.coforkOfCokernelCofork_π

/-- Map any coequalizer cofork to a cocone on the difference of the two morphisms. -/
def cokernelCoforkOfCofork (c : Cofork f g) : CokernelCofork (f - g) :=
  Cofork.ofπ c.π <| by rw [sub_comp, zero_comp, sub_eq_zero, c.condition]
#align category_theory.preadditive.cokernel_cofork_of_cofork CategoryTheory.Preadditive.cokernelCoforkOfCofork

@[simp]
theorem cokernelCoforkOfCofork_π (c : Cofork f g) : (cokernelCoforkOfCofork c).π = c.π :=
  rfl
#align category_theory.preadditive.cokernel_cofork_of_cofork_π CategoryTheory.Preadditive.cokernelCoforkOfCofork_π

@[simp]
theorem cokernelCoforkOfCofork_ofπ {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
    cokernelCoforkOfCofork (Cofork.ofπ π w) = CokernelCofork.ofπ π (by simp [w]) :=
  rfl
#align category_theory.preadditive.cokernel_cofork_of_cofork_of_π CategoryTheory.Preadditive.cokernelCoforkOfCofork_ofπ

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
def isColimitCoforkOfCokernelCofork {c : CokernelCofork (f - g)} (i : IsColimit c) :
    IsColimit (coforkOfCokernelCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (cokernelCoforkOfCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; aesop_cat⟩
#align category_theory.preadditive.is_colimit_cofork_of_cokernel_cofork CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork

@[simp]
theorem isColimitCoforkOfCokernelCofork_desc {c : CokernelCofork (f - g)} (i : IsColimit c)
    (s : Cofork f g) :
    (isColimitCoforkOfCokernelCofork i).desc s = i.desc (cokernelCoforkOfCofork s) :=
  rfl
#align category_theory.preadditive.is_colimit_cofork_of_cokernel_cofork_desc CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork_desc

/-- A coequalizer of `f` and `g` is a cokernel of `f - g`. -/
def isColimitCokernelCoforkOfCofork {c : Cofork f g} (i : IsColimit c) :
    IsColimit (cokernelCoforkOfCofork c) :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨i.desc (coforkOfCokernelCofork s), i.fac _ _, fun h => by
      apply Cofork.IsColimit.hom_ext i; aesop_cat⟩
#align category_theory.preadditive.is_colimit_cokernel_cofork_of_cofork CategoryTheory.Preadditive.isColimitCokernelCoforkOfCofork

variable (f g)

/-- A preadditive category has a coequalizer for `f` and `g` if it has a cokernel for `f - g`. -/
theorem hasCoequalizer_of_hasCokernel [HasCokernel (f - g)] : HasCoequalizer f g :=
  HasColimit.mk
    { cocone := coforkOfCokernelCofork _
      isColimit := isColimitCoforkOfCokernelCofork (coequalizerIsCoequalizer (f - g) 0) }
#align category_theory.preadditive.has_coequalizer_of_has_cokernel CategoryTheory.Preadditive.hasCoequalizer_of_hasCokernel

/-- A preadditive category has a cokernel for `f - g` if it has a coequalizer for `f` and `g`. -/
theorem hasCokernel_of_hasCoequalizer [HasCoequalizer f g] : HasCokernel (f - g) :=
  HasColimit.mk
    { cocone := cokernelCoforkOfCofork (coequalizer.cofork f g)
      isColimit := isColimitCokernelCoforkOfCofork (colimit.isColimit (parallelPair f g)) }
#align category_theory.preadditive.has_cokernel_of_has_coequalizer CategoryTheory.Preadditive.hasCokernel_of_hasCoequalizer

end

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
theorem hasEqualizers_of_hasKernels [HasKernels C] : HasEqualizers C :=
  @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g
#align category_theory.preadditive.has_equalizers_of_has_kernels CategoryTheory.Preadditive.hasEqualizers_of_hasKernels

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
theorem hasCoequalizers_of_hasCokernels [HasCokernels C] : HasCoequalizers C :=
  @hasCoequalizers_of_hasColimit_parallelPair _ _ fun {_} {_} f g =>
    hasCoequalizer_of_hasCokernel f g
#align category_theory.preadditive.has_coequalizers_of_has_cokernels CategoryTheory.Preadditive.hasCoequalizers_of_hasCokernels

end Equalizers

section

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

instance : SMul (Units ℤ) (X ≅ Y) where
  smul a e :=
    { hom := (a : ℤ) • e.hom
      inv := ((a⁻¹ : Units ℤ) : ℤ) • e.inv
      hom_inv_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.inv_mul, one_smul, e.hom_inv_id]
      inv_hom_id := by
        simp only [comp_zsmul, zsmul_comp, smul_smul, Units.mul_inv, one_smul, e.inv_hom_id] }

@[simp]
lemma smul_iso_hom (a : Units ℤ) (e : X ≅ Y) : (a • e).hom = a • e.hom := rfl

@[simp]
lemma smul_iso_inv (a : Units ℤ) (e : X ≅ Y) : (a • e).inv = a⁻¹ • e.inv := rfl

instance : Neg (X ≅ Y) where
  neg e :=
    { hom := -e.hom
      inv := -e.inv }

@[simp]
lemma neg_iso_hom (e : X ≅ Y) : (-e).hom = -e.hom := rfl

@[simp]
lemma neg_iso_inv (e : X ≅ Y) : (-e).inv = -e.inv := rfl

end

end Preadditive

end CategoryTheory
