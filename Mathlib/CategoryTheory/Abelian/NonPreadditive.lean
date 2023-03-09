/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.abelian.non_preadditive
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Shapes.NormalMono.Equalizers
import Mathbin.CategoryTheory.Abelian.Images
import Mathbin.CategoryTheory.Preadditive.Basic

/-!
# Every non_preadditive_abelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with a zero object,
kernels and cokernels, products and coproducts and in which every monomorphism and epimorphis is
normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. Even more remarkably,
since abelian categories admit exactly one preadditive structure (see
`subsingleton_preadditive_of_has_binary_biproducts`), the construction manages to exactly
reconstruct any natural preadditive structure the category may have.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

section

universe v u

variable (C : Type u) [Category.{v} C]

/-- We call a category `non_preadditive_abelian` if it has a zero object, kernels, cokernels, binary
    products and coproducts, and every monomorphism and every epimorphism is normal. -/
class NonPreadditiveAbelian extends HasZeroMorphisms C, NormalMonoCategory C,
  NormalEpiCategory C where
  [HasZeroObject : HasZeroObject C]
  [HasKernels : HasKernels C]
  [HasCokernels : HasCokernels C]
  [HasFiniteProducts : HasFiniteProducts C]
  [HasFiniteCoproducts : HasFiniteCoproducts C]
#align category_theory.non_preadditive_abelian CategoryTheory.NonPreadditiveAbelian

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
set_option default_priority 100

attribute [instance] non_preadditive_abelian.has_zero_object

attribute [instance] non_preadditive_abelian.has_kernels

attribute [instance] non_preadditive_abelian.has_cokernels

attribute [instance] non_preadditive_abelian.has_finite_products

attribute [instance] non_preadditive_abelian.has_finite_coproducts

end

end CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [NonPreadditiveAbelian C]

namespace CategoryTheory.NonPreadditiveAbelian

section Factor

variable {P Q : C} (f : P ⟶ Q)

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : Epi (Abelian.factorThruImage f) :=
  let I := Abelian.image f
  let p := Abelian.factorThruImage f
  let i := kernel.ι (cokernel.π f)
  -- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
    NormalMonoCategory.epi_of_zero_cancel
    _ fun R (g : I ⟶ R) (hpg : p ≫ g = 0) =>
    by
    -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
    let u := kernel.ι g ≫ i
    haveI : mono u := mono_comp _ _
    haveI hu := normal_mono_of_mono u
    let h := hu.g
    -- By hypothesis, p factors through the kernel of g via some t.
    obtain ⟨t, ht⟩ := kernel.lift' g p hpg
    have fh : f ≫ h = 0
    calc
      f ≫ h = (p ≫ i) ≫ h := (abelian.image.fac f).symm ▸ rfl
      _ = ((t ≫ kernel.ι g) ≫ i) ≫ h := (ht ▸ rfl)
      _ = t ≫ u ≫ h := by
        simp only [category.assoc] <;>
          conv_lhs =>
            congr
            skip
            rw [← category.assoc]
      _ = t ≫ 0 := (hu.w ▸ rfl)
      _ = 0 := has_zero_morphisms.comp_zero _ _
      
    -- h factors through the cokernel of f via some l.
    obtain ⟨l, hl⟩ := cokernel.desc' f h fh
    have hih : i ≫ h = 0
    calc
      i ≫ h = i ≫ cokernel.π f ≫ l := hl ▸ rfl
      _ = 0 ≫ l := by rw [← category.assoc, kernel.condition]
      _ = 0 := zero_comp
      
    -- i factors through u = ker h via some s.
    obtain ⟨s, hs⟩ := normal_mono.lift' u i hih
    have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i := by rw [category.assoc, hs, category.id_comp]
    haveI : epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs')
    -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
    exact zero_of_epi_comp _ (kernel.condition g)

instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) :=
  isIso_of_mono_of_epi _
#align category_theory.non_preadditive_abelian.is_iso_factor_thru_image CategoryTheory.NonPreadditiveAbelian.isIso_factorThruImage

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : Mono (Abelian.factorThruCoimage f) :=
  let I := Abelian.coimage f
  let i := Abelian.factorThruCoimage f
  let p := cokernel.π (kernel.ι f)
  NormalEpiCategory.mono_of_cancel_zero _ fun R (g : R ⟶ I) (hgi : g ≫ i = 0) =>
    by
    -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
    let u := p ≫ cokernel.π g
    haveI : epi u := epi_comp _ _
    haveI hu := normal_epi_of_epi u
    let h := hu.g
    -- By hypothesis, i factors through the cokernel of g via some t.
    obtain ⟨t, ht⟩ := cokernel.desc' g i hgi
    have hf : h ≫ f = 0
    calc
      h ≫ f = h ≫ p ≫ i := (abelian.coimage.fac f).symm ▸ rfl
      _ = h ≫ p ≫ cokernel.π g ≫ t := (ht ▸ rfl)
      _ = h ≫ u ≫ t := by
        simp only [category.assoc] <;>
          conv_lhs =>
            congr
            skip
            rw [← category.assoc]
      _ = 0 ≫ t := by rw [← category.assoc, hu.w]
      _ = 0 := zero_comp
      
    -- h factors through the kernel of f via some l.
    obtain ⟨l, hl⟩ := kernel.lift' f h hf
    have hhp : h ≫ p = 0
    calc
      h ≫ p = (l ≫ kernel.ι f) ≫ p := hl ▸ rfl
      _ = l ≫ 0 := by rw [category.assoc, cokernel.condition]
      _ = 0 := comp_zero
      
    -- p factors through u = coker h via some s.
    obtain ⟨s, hs⟩ := normal_epi.desc' u p hhp
    have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I := by rw [← category.assoc, hs, category.comp_id]
    haveI : mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs')
    -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
    exact zero_of_comp_mono _ (cokernel.condition g)

instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) :=
  isIso_of_mono_of_epi _
#align category_theory.non_preadditive_abelian.is_iso_factor_thru_coimage CategoryTheory.NonPreadditiveAbelian.isIso_factorThruCoimage

end Factor

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

/-- In a `non_preadditive_abelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  IsCokernel.cokernelIso _ _
    (cokernel.ofIsoComp _ _ (Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit _) h)
      (ConeMorphism.w (Limits.IsLimit.uniqueUpToIso (limit.isLimit _) h).hom _))
    (asIso <| Abelian.factorThruCoimage f) (Abelian.coimage.fac f)
#align category_theory.non_preadditive_abelian.epi_is_cokernel_of_kernel CategoryTheory.NonPreadditiveAbelian.epiIsCokernelOfKernel

/-- In a `non_preadditive_abelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  IsKernel.isoKernel _ _
    (kernel.ofCompIso _ _ (Limits.IsColimit.coconePointUniqueUpToIso h (colimit.isColimit _))
      (CoconeMorphism.w (Limits.IsColimit.uniqueUpToIso h <| colimit.isColimit _).hom _))
    (asIso <| Abelian.factorThruImage f) (Abelian.image.fac f)
#align category_theory.non_preadditive_abelian.mono_is_kernel_of_cokernel CategoryTheory.NonPreadditiveAbelian.monoIsKernelOfCokernel

end CokernelOfKernel

section

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
abbrev r (A : C) : A ⟶ cokernel (diag A) :=
  prod.lift (𝟙 A) 0 ≫ cokernel.π (diag A)
#align category_theory.non_preadditive_abelian.r CategoryTheory.NonPreadditiveAbelian.r

instance mono_Δ {A : C} : Mono (diag A) :=
  mono_of_mono_fac <| prod.lift_fst _ _
#align category_theory.non_preadditive_abelian.mono_Δ CategoryTheory.NonPreadditiveAbelian.mono_Δ

instance mono_r {A : C} : Mono (r A) :=
  by
  let hl : is_limit (kernel_fork.of_ι (diag A) (cokernel.condition (diag A))) :=
    mono_is_kernel_of_cokernel _ (colimit.is_colimit _)
  apply normal_epi_category.mono_of_cancel_zero
  intro Z x hx
  have hxx : (x ≫ prod.lift (𝟙 A) (0 : A ⟶ A)) ≫ cokernel.π (diag A) = 0 := by
    rw [category.assoc, hx]
  obtain ⟨y, hy⟩ := kernel_fork.is_limit.lift' hl _ hxx
  rw [kernel_fork.ι_of_ι] at hy
  have hyy : y = 0 := by
    erw [← category.comp_id y, ← limits.prod.lift_snd (𝟙 A) (𝟙 A), ← category.assoc, hy,
      category.assoc, prod.lift_snd, has_zero_morphisms.comp_zero]
  haveI : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
  apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
  rw [← hy, hyy, zero_comp, zero_comp]
#align category_theory.non_preadditive_abelian.mono_r CategoryTheory.NonPreadditiveAbelian.mono_r

instance epi_r {A : C} : Epi (r A) :=
  by
  have hlp : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ limits.prod.snd = 0 := prod.lift_snd _ _
  let hp1 : is_limit (kernel_fork.of_ι (prod.lift (𝟙 A) (0 : A ⟶ A)) hlp) :=
    by
    refine' fork.is_limit.mk _ (fun s => fork.ι s ≫ limits.prod.fst) _ _
    · intro s
      ext <;> simp
      erw [category.comp_id]
    · intro s m h
      haveI : mono (prod.lift (𝟙 A) (0 : A ⟶ A)) := mono_of_mono_fac (prod.lift_fst _ _)
      apply (cancel_mono (prod.lift (𝟙 A) (0 : A ⟶ A))).1
      convert h
      ext <;> simp
  let hp2 : is_colimit (cokernel_cofork.of_π (limits.prod.snd : A ⨯ A ⟶ A) hlp) :=
    epi_is_cokernel_of_kernel _ hp1
  apply normal_mono_category.epi_of_zero_cancel
  intro Z z hz
  have h : prod.lift (𝟙 A) (0 : A ⟶ A) ≫ cokernel.π (diag A) ≫ z = 0 := by rw [← category.assoc, hz]
  obtain ⟨t, ht⟩ := cokernel_cofork.is_colimit.desc' hp2 _ h
  rw [cokernel_cofork.π_of_π] at ht
  have htt : t = 0 := by
    rw [← category.id_comp t]
    change 𝟙 A ≫ t = 0
    rw [← limits.prod.lift_snd (𝟙 A) (𝟙 A), category.assoc, ht, ← category.assoc,
      cokernel.condition, zero_comp]
  apply (cancel_epi (cokernel.π (diag A))).1
  rw [← ht, htt, comp_zero, comp_zero]
#align category_theory.non_preadditive_abelian.epi_r CategoryTheory.NonPreadditiveAbelian.epi_r

instance isIso_r {A : C} : IsIso (r A) :=
  isIso_of_mono_of_epi _
#align category_theory.non_preadditive_abelian.is_iso_r CategoryTheory.NonPreadditiveAbelian.isIso_r

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
    followed by the inverse of `r`. In the category of modules, using the normal kernels and
    cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
    "subtraction". -/
abbrev σ {A : C} : A ⨯ A ⟶ A :=
  cokernel.π (diag A) ≫ inv (r A)
#align category_theory.non_preadditive_abelian.σ CategoryTheory.NonPreadditiveAbelian.σ

end

@[simp, reassoc.1]
theorem diag_σ {X : C} : diag X ≫ σ = 0 := by rw [cokernel.condition_assoc, zero_comp]
#align category_theory.non_preadditive_abelian.diag_σ CategoryTheory.NonPreadditiveAbelian.diag_σ

@[simp, reassoc.1]
theorem lift_σ {X : C} : prod.lift (𝟙 X) 0 ≫ σ = 𝟙 X := by rw [← category.assoc, is_iso.hom_inv_id]
#align category_theory.non_preadditive_abelian.lift_σ CategoryTheory.NonPreadditiveAbelian.lift_σ

@[reassoc.1]
theorem lift_map {X Y : C} (f : X ⟶ Y) :
    prod.lift (𝟙 X) 0 ≫ Limits.prod.map f f = f ≫ prod.lift (𝟙 Y) 0 := by simp
#align category_theory.non_preadditive_abelian.lift_map CategoryTheory.NonPreadditiveAbelian.lift_map

/-- σ is a cokernel of Δ X. -/
def isColimitσ {X : C} : IsColimit (CokernelCofork.ofπ σ diag_σ) :=
  cokernel.cokernelIso _ σ (asIso (r X)).symm (by rw [iso.symm_hom, as_iso_inv])
#align category_theory.non_preadditive_abelian.is_colimit_σ CategoryTheory.NonPreadditiveAbelian.isColimitσ

/-- This is the key identity satisfied by `σ`. -/
theorem σ_comp {X Y : C} (f : X ⟶ Y) : σ ≫ f = Limits.prod.map f f ≫ σ :=
  by
  obtain ⟨g, hg⟩ :=
    cokernel_cofork.is_colimit.desc' is_colimit_σ (limits.prod.map f f ≫ σ) (by simp)
  suffices hfg : f = g
  · rw [← hg, cofork.π_of_π, hfg]
  calc
    f = f ≫ prod.lift (𝟙 Y) 0 ≫ σ := by rw [lift_σ, category.comp_id]
    _ = prod.lift (𝟙 X) 0 ≫ limits.prod.map f f ≫ σ := by rw [lift_map_assoc]
    _ = prod.lift (𝟙 X) 0 ≫ σ ≫ g := by rw [← hg, cokernel_cofork.π_of_π]
    _ = g := by rw [← category.assoc, lift_σ, category.id_comp]
    
#align category_theory.non_preadditive_abelian.σ_comp CategoryTheory.NonPreadditiveAbelian.σ_comp

section

-- We write `f - g` for `prod.lift f g ≫ σ`.
/-- Subtraction of morphisms in a `non_preadditive_abelian` category. -/
def hasSub {X Y : C} : Sub (X ⟶ Y) :=
  ⟨fun f g => prod.lift f g ≫ σ⟩
#align category_theory.non_preadditive_abelian.has_sub CategoryTheory.NonPreadditiveAbelian.hasSub

attribute [local instance] Sub

-- We write `-f` for `0 - f`.
/-- Negation of morphisms in a `non_preadditive_abelian` category. -/
def hasNeg {X Y : C} : Neg (X ⟶ Y) :=
  ⟨fun f => 0 - f⟩
#align category_theory.non_preadditive_abelian.has_neg CategoryTheory.NonPreadditiveAbelian.hasNeg

attribute [local instance] Neg

-- We write `f + g` for `f - (-g)`.
/-- Addition of morphisms in a `non_preadditive_abelian` category. -/
def hasAdd {X Y : C} : Add (X ⟶ Y) :=
  ⟨fun f g => f - -g⟩
#align category_theory.non_preadditive_abelian.has_add CategoryTheory.NonPreadditiveAbelian.hasAdd

attribute [local instance] Add

theorem sub_def {X Y : C} (a b : X ⟶ Y) : a - b = prod.lift a b ≫ σ :=
  rfl
#align category_theory.non_preadditive_abelian.sub_def CategoryTheory.NonPreadditiveAbelian.sub_def

theorem add_def {X Y : C} (a b : X ⟶ Y) : a + b = a - -b :=
  rfl
#align category_theory.non_preadditive_abelian.add_def CategoryTheory.NonPreadditiveAbelian.add_def

theorem neg_def {X Y : C} (a : X ⟶ Y) : -a = 0 - a :=
  rfl
#align category_theory.non_preadditive_abelian.neg_def CategoryTheory.NonPreadditiveAbelian.neg_def

theorem sub_zero {X Y : C} (a : X ⟶ Y) : a - 0 = a :=
  by
  rw [sub_def]
  conv_lhs =>
    congr
    congr
    rw [← category.comp_id a]
    skip
    rw [show 0 = a ≫ (0 : Y ⟶ Y) by simp]
  rw [← prod.comp_lift, category.assoc, lift_σ, category.comp_id]
#align category_theory.non_preadditive_abelian.sub_zero CategoryTheory.NonPreadditiveAbelian.sub_zero

theorem sub_self {X Y : C} (a : X ⟶ Y) : a - a = 0 := by
  rw [sub_def, ← category.comp_id a, ← prod.comp_lift, category.assoc, diag_σ, comp_zero]
#align category_theory.non_preadditive_abelian.sub_self CategoryTheory.NonPreadditiveAbelian.sub_self

theorem lift_sub_lift {X Y : C} (a b c d : X ⟶ Y) :
    prod.lift a b - prod.lift c d = prod.lift (a - c) (b - d) :=
  by
  simp only [sub_def]
  ext
  · rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_fst, prod.lift_fst, prod.lift_fst]
  · rw [category.assoc, σ_comp, prod.lift_map_assoc, prod.lift_snd, prod.lift_snd, prod.lift_snd]
#align category_theory.non_preadditive_abelian.lift_sub_lift CategoryTheory.NonPreadditiveAbelian.lift_sub_lift

theorem sub_sub_sub {X Y : C} (a b c d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) := by
  rw [sub_def, ← lift_sub_lift, sub_def, category.assoc, σ_comp, prod.lift_map_assoc]; rfl
#align category_theory.non_preadditive_abelian.sub_sub_sub CategoryTheory.NonPreadditiveAbelian.sub_sub_sub

theorem neg_sub {X Y : C} (a b : X ⟶ Y) : -a - b = -b - a := by
  conv_lhs => rw [neg_def, ← sub_zero b, sub_sub_sub, sub_zero, ← neg_def]
#align category_theory.non_preadditive_abelian.neg_sub CategoryTheory.NonPreadditiveAbelian.neg_sub

theorem neg_neg {X Y : C} (a : X ⟶ Y) : - -a = a :=
  by
  rw [neg_def, neg_def]
  conv_lhs =>
    congr
    rw [← sub_self a]
  rw [sub_sub_sub, sub_zero, sub_self, sub_zero]
#align category_theory.non_preadditive_abelian.neg_neg CategoryTheory.NonPreadditiveAbelian.neg_neg

theorem add_comm {X Y : C} (a b : X ⟶ Y) : a + b = b + a :=
  by
  rw [add_def]
  conv_lhs => rw [← neg_neg a]
  rw [neg_def, neg_def, neg_def, sub_sub_sub]
  conv_lhs =>
    congr
    skip
    rw [← neg_def, neg_sub]
  rw [sub_sub_sub, add_def, ← neg_def, neg_neg b, neg_def]
#align category_theory.non_preadditive_abelian.add_comm CategoryTheory.NonPreadditiveAbelian.add_comm

theorem add_neg {X Y : C} (a b : X ⟶ Y) : a + -b = a - b := by rw [add_def, neg_neg]
#align category_theory.non_preadditive_abelian.add_neg CategoryTheory.NonPreadditiveAbelian.add_neg

theorem add_neg_self {X Y : C} (a : X ⟶ Y) : a + -a = 0 := by rw [add_neg, sub_self]
#align category_theory.non_preadditive_abelian.add_neg_self CategoryTheory.NonPreadditiveAbelian.add_neg_self

theorem neg_add_self {X Y : C} (a : X ⟶ Y) : -a + a = 0 := by rw [add_comm, add_neg_self]
#align category_theory.non_preadditive_abelian.neg_add_self CategoryTheory.NonPreadditiveAbelian.neg_add_self

theorem neg_sub' {X Y : C} (a b : X ⟶ Y) : -(a - b) = -a + b :=
  by
  rw [neg_def, neg_def]
  conv_lhs => rw [← sub_self (0 : X ⟶ Y)]
  rw [sub_sub_sub, add_def, neg_def]
#align category_theory.non_preadditive_abelian.neg_sub' CategoryTheory.NonPreadditiveAbelian.neg_sub'

theorem neg_add {X Y : C} (a b : X ⟶ Y) : -(a + b) = -a - b := by rw [add_def, neg_sub', add_neg]
#align category_theory.non_preadditive_abelian.neg_add CategoryTheory.NonPreadditiveAbelian.neg_add

theorem sub_add {X Y : C} (a b c : X ⟶ Y) : a - b + c = a - (b - c) := by
  rw [add_def, neg_def, sub_sub_sub, sub_zero]
#align category_theory.non_preadditive_abelian.sub_add CategoryTheory.NonPreadditiveAbelian.sub_add

theorem add_assoc {X Y : C} (a b c : X ⟶ Y) : a + b + c = a + (b + c) :=
  by
  conv_lhs =>
    congr
    rw [add_def]
  rw [sub_add, ← add_neg, neg_sub', neg_neg]
#align category_theory.non_preadditive_abelian.add_assoc CategoryTheory.NonPreadditiveAbelian.add_assoc

theorem add_zero {X Y : C} (a : X ⟶ Y) : a + 0 = a := by rw [add_def, neg_def, sub_self, sub_zero]
#align category_theory.non_preadditive_abelian.add_zero CategoryTheory.NonPreadditiveAbelian.add_zero

theorem comp_sub {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h := by
  rw [sub_def, ← category.assoc, prod.comp_lift, sub_def]
#align category_theory.non_preadditive_abelian.comp_sub CategoryTheory.NonPreadditiveAbelian.comp_sub

theorem sub_comp {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h := by
  rw [sub_def, category.assoc, σ_comp, ← category.assoc, prod.lift_map, sub_def]
#align category_theory.non_preadditive_abelian.sub_comp CategoryTheory.NonPreadditiveAbelian.sub_comp

theorem comp_add (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  rw [add_def, comp_sub, neg_def, comp_sub, comp_zero, add_def, neg_def]
#align category_theory.non_preadditive_abelian.comp_add CategoryTheory.NonPreadditiveAbelian.comp_add

theorem add_comp (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  rw [add_def, sub_comp, neg_def, sub_comp, zero_comp, add_def, neg_def]
#align category_theory.non_preadditive_abelian.add_comp CategoryTheory.NonPreadditiveAbelian.add_comp

/-- Every `non_preadditive_abelian` category is preadditive. -/
def preadditive : Preadditive C
    where
  homGroup X Y :=
    { add := (· + ·)
      add_assoc := add_assoc
      zero := 0
      zero_add := neg_neg
      add_zero := add_zero
      neg := fun f => -f
      add_left_neg := neg_add_self
      add_comm := add_comm }
  add_comp' := add_comp
  comp_add' := comp_add
#align category_theory.non_preadditive_abelian.preadditive CategoryTheory.NonPreadditiveAbelian.preadditive

end

end CategoryTheory.NonPreadditiveAbelian

