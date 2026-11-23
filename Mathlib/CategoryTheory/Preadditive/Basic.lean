/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

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

@[expose] public section


universe w v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
linear in both variables. -/
@[stacks 00ZY]
class Preadditive (C : Type u) [Category.{v} C] where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    cat_disch
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    cat_disch

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance_reducible, instance] Preadditive.homGroup

-- simp can already prove reassoc version
attribute [reassoc, simp] Preadditive.add_comp Preadditive.comp_add

attribute [to_dual self] Preadditive.homGroup
attribute [to_dual existing comp_add] Preadditive.add_comp
attribute [to_dual self (reorder :=
  homGroup (P Q), add_comp comp_add, add_comp (P R, f f' g), comp_add (P R, f g' g))] Preadditive.mk

variable {C : Type u} [Category.{v} C] [Preadditive C]
namespace End

@[simps!]
instance (X : C) : AddCommGroup (End X) := (End.homEquiv (X := X)).addCommGroup

/-- The additive bijection `End X ≃+ (X ⟶ X)`
when `X` is an object in a preadditive category. -/
@[implicit_reducible, simps!]
def addEquiv {X : C} : End X ≃+ (X ⟶ X) where
  toEquiv := homEquiv
  map_add' := by cat_disch

@[simp]
lemma sum_asHom {X : C} {ι : Type*} (s : Finset ι) (f : ι → End X) :
    (∑ i ∈ s, f i).asHom = ∑ i ∈ s, (f i).asHom :=
  map_sum addEquiv _ _

end End

namespace Preadditive

section Preadditive

open AddMonoidHom

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

instance inducedCategory : Preadditive.{v} (InducedCategory C F) where
  homGroup P Q := InducedCategory.homEquiv.addCommGroup
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

variable {F} in
/-- The additive equivalence `(X ⟶ Y) ≃+ (F X ⟶ F Y)` when `F : D → C` and
`C` is a preadditive category. -/
@[simps!, to_dual self]
def _root_.CategoryTheory.InducedCategory.homAddEquiv
    {X Y : InducedCategory C F} :
    (X ⟶ Y) ≃+ (F X ⟶ F Y) where
  toEquiv := InducedCategory.homEquiv
  map_add' := by aesop_cat

end InducedCategory

instance fullSubcategory (Z : ObjectProperty C) : Preadditive Z.FullSubcategory where
  homGroup P Q := {
      -- Note: Add zero field explicitly for a better transparency of definitional properties
      zero := Z.homMk 0
      __ := InducedCategory.homEquiv.addCommGroup }
  add_comp _ _ _ _ _ _ := by ext; apply add_comp
  comp_add _ _ _ _ _ _ := by ext; apply comp_add

/-- Composition by a fixed left argument as a group homomorphism -/
@[to_dual rightComp /-- Composition by a fixed right argument as a group homomorphism -/]
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def compHom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) :=
  AddMonoidHom.mk' (fun f => leftComp _ f) fun f₁ f₂ =>
    AddMonoidHom.ext fun g => (rightComp _ g).map_add f₁ f₂

-- simp can prove the reassoc version
@[to_dual (attr := reassoc, simp) (reorder := f f' g) comp_sub]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

-- simp can prove the reassoc version
@[to_dual (attr := reassoc, simp) (reorder := f g) comp_neg]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

@[to_dual self, reassoc]
theorem neg_comp_neg : (-f) ≫ (-g) = f ≫ g := by simp

@[to_dual (reorder := f g) comp_nsmul]
theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) n f

@[to_dual (reorder := f g) comp_zsmul]
theorem zsmul_comp (n : ℤ) : (n • f) ≫ g = n • f ≫ g :=
  map_zsmul (rightComp P g) n f

@[to_dual (attr := reassoc) (reorder := f g) comp_sum]
theorem sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j ∈ s, f j) ≫ g = ∑ j ∈ s, f j ≫ g :=
  map_sum (rightComp P g) _ _

@[reassoc]
theorem sum_comp' {P Q R S : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : J → (Q ⟶ R))
    (h : R ⟶ S) : (∑ j ∈ s, f j ≫ g j) ≫ h = ∑ j ∈ s, f j ≫ g j ≫ h := by
  simp only [← Category.assoc]
  apply sum_comp

@[to_dual]
instance {P Q : C} {f : P ⟶ Q} [Epi f] : Epi (-f) :=
  ⟨fun g g' H => by rwa [neg_comp, neg_comp, ← comp_neg, ← comp_neg, cancel_epi, neg_inj] at H⟩

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

variable (C) in
lemma hasZeroObject_of_hasCoproduct [HasCoproduct (PEmpty.elim : PEmpty.{w + 1} → C)] :
    HasZeroObject C :=
  ⟨∐ (PEmpty.elim : PEmpty.{w + 1} → C), by
    rw [IsZero.iff_id_eq_zero]
    cat_disch⟩

attribute [local simp] End.mul_asHom in
/-- This instance is split off from the `Ring (End X)` instance to speed up instance search. -/
instance {X : C} : Semiring (End X) :=
  { End.monoid with
    zero_mul := by cat_disch
    mul_zero := by cat_disch
    left_distrib := by cat_disch
    right_distrib := by cat_disch }

instance {X : C} : Ring (End X) :=
  { (inferInstance : Semiring (End X)),
    (inferInstance : AddCommGroup (End X)) with
    neg_add_cancel := neg_add_cancel }

instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add _ _ _ := add_comp _ _ _ _ _ _
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add _ _ _ _ _ _
  zero_smul _ := comp_zero

to_dual_name_hint Mono Epi, ι π, Lift Desc

@[to_dual]
theorem mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
    Mono f where
  right_cancellation := fun {Z} g₁ g₂ hg =>
    sub_eq_zero.1 <| h _ <| (map_sub (rightComp Z f) g₁ g₂).trans <| sub_eq_zero.2 hg

@[to_dual]
theorem mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
    Mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
  ⟨fun _ _ _ => zero_of_comp_mono _, mono_of_cancel_zero f⟩

@[to_dual]
theorem mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel.ι f = 0) : Mono f :=
  mono_of_cancel_zero f fun g h => by rw [← kernel.lift_ι f g h, w, Limits.comp_zero]

@[to_dual]
lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := mono_of_cancel_zero _ (fun g hg => by
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ hg
  rw [← ha, h.eq_of_tgt a 0, Limits.zero_comp])

@[to_dual]
lemma mono_iff_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c) :
    Mono f ↔ IsZero c.pt :=
  ⟨fun _ ↦ KernelFork.IsLimit.isZero_of_mono hc, mono_of_isZero_kernel' c hc⟩

@[to_dual]
lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h

@[to_dual]
lemma mono_iff_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    Mono f ↔ IsZero (kernel f) :=
  mono_iff_isZero_kernel' _ (limit.isLimit _)

namespace IsIso

@[to_dual (attr := simp) (reorder := f g) comp_right_eq_zero]
theorem comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0 := by
  rw [← IsIso.eq_inv_comp, Limits.comp_zero]

end IsIso

open ZeroObject

variable [HasZeroObject C]

@[to_dual]
theorem mono_of_kernel_iso_zero {X Y : C} {f : X ⟶ Y} [HasLimit (parallelPair f 0)]
    (w : kernel f ≅ 0) : Mono f :=
  mono_of_kernel_zero (zero_of_source_iso_zero _ w)

end Preadditive

section Equalizers

section

variable {X Y : C} {f : X ⟶ Y} {g : X ⟶ Y}

/-- Map a kernel cone on the difference of two morphisms to the equalizer fork. -/
@[to_dual (attr := simps! pt)
/-- Map a cokernel cocone on the difference of two morphisms to the coequalizer cofork. -/]
def forkOfKernelFork (c : KernelFork (f - g)) : Fork f g :=
  Fork.ofι c.ι <| by rw [← sub_eq_zero, ← comp_sub, c.condition]

@[to_dual (attr := simp)]
theorem forkOfKernelFork_ι (c : KernelFork (f - g)) : (forkOfKernelFork c).ι = c.ι :=
  rfl

/-- Map any equalizer fork to a cone on the difference of the two morphisms. -/
@[to_dual /-- Map any coequalizer cofork to a cocone on the difference of the two morphisms. -/]
def kernelForkOfFork (c : Fork f g) : KernelFork (f - g) :=
  Fork.ofι c.ι <| by rw [comp_sub, comp_zero, sub_eq_zero, c.condition]

@[to_dual (attr := simp)]
theorem kernelForkOfFork_ι (c : Fork f g) : (kernelForkOfFork c).ι = c.ι :=
  rfl

@[to_dual (attr := simp)]
theorem kernelForkOfFork_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
    kernelForkOfFork (Fork.ofι ι w) = KernelFork.ofι ι (by simp [w]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
@[to_dual /-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/]
def isLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsLimit c) :
    IsLimit (forkOfKernelFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (kernelForkOfFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

@[to_dual (attr := simp)]
theorem isLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsLimit c) (s : Fork f g) :
    (isLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An equalizer of `f` and `g` is a kernel of `f - g`. -/
@[to_dual /-- A coequalizer of `f` and `g` is a cokernel of `f - g`. -/]
def isLimitKernelForkOfFork {c : Fork f g} (i : IsLimit c) : IsLimit (kernelForkOfFork c) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨i.lift (forkOfKernelFork s), i.fac _ _, fun h => by apply Fork.IsLimit.hom_ext i; cat_disch⟩

variable (f g)

/-- A preadditive category has an equalizer for `f` and `g` if it has a kernel for `f - g`. -/
@[to_dual
/-- A preadditive category has a coequalizer for `f` and `g` if it has a cokernel for `f - g`. -/]
theorem hasEqualizer_of_hasKernel [HasKernel (f - g)] : HasEqualizer f g :=
  HasLimit.mk
    { cone := forkOfKernelFork _
      isLimit := isLimitForkOfKernelFork (equalizerIsEqualizer (f - g) 0) }

/-- A preadditive category has a kernel for `f - g` if it has an equalizer for `f` and `g`. -/
@[to_dual
/-- A preadditive category has a cokernel for `f - g` if it has a coequalizer for `f` and `g`. -/]
theorem hasKernel_of_hasEqualizer [HasEqualizer f g] : HasKernel (f - g) :=
  HasLimit.mk
    { cone := kernelForkOfFork (equalizer.fork f g)
      isLimit := isLimitKernelForkOfFork (limit.isLimit (parallelPair f g)) }

end

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
@[to_dual /-- If a preadditive category has all cokernels, then it also has all coequalizers. -/]
theorem hasEqualizers_of_hasKernels [HasKernels C] : HasEqualizers C :=
  @hasEqualizers_of_hasLimit_parallelPair _ _ fun {_} {_} f g => hasEqualizer_of_hasKernel f g

end Equalizers

section

variable {X Y : C}

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

@[to_dual (attr := simp) neg_iso_inv]
lemma neg_iso_hom (e : X ≅ Y) : (-e).hom = -e.hom := rfl

end

end Preadditive

end CategoryTheory
