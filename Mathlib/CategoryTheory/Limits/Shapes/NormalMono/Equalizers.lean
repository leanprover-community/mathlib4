/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

#align_import category_theory.limits.shapes.normal_mono.equalizers from "leanprover-community/mathlib"@"3a061790136d13594ec10c7c90d202335ac5d854"

/-!
# Normal mono categories with finite products and kernels have all equalizers.

This, and the dual result, are used in the development of abelian categories.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

namespace CategoryTheory.NormalMonoCategory

variable [HasFiniteProducts C] [HasKernels C] [NormalMonoCategory C]

/-- The pullback of two monomorphisms exists. -/
@[irreducible, nolint defLemma] -- Porting note: changed to irreducible and a def
def pullback_of_mono {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [Mono a] [Mono b] :
    HasLimit (cospan a b) :=
  let ⟨P, f, haf, i⟩ := normalMonoOfMono a
  let ⟨Q, g, hbg, i'⟩ := normalMonoOfMono b
  let ⟨a', ha'⟩ :=
    KernelFork.IsLimit.lift' i (kernel.ι (prod.lift f g)) <|
      calc kernel.ι (prod.lift f g) ≫ f
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.fst := by rw [prod.lift_fst]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.fst := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp

  let ⟨b', hb'⟩ :=
    KernelFork.IsLimit.lift' i' (kernel.ι (prod.lift f g)) <|
      calc kernel.ι (prod.lift f g) ≫ g
        _ = kernel.ι (prod.lift f g) ≫ prod.lift f g ≫ Limits.prod.snd := by rw [prod.lift_snd]
        _ = (0 : kernel (prod.lift f g) ⟶ P ⨯ Q) ≫ Limits.prod.snd := by rw [kernel.condition_assoc]
        _ = 0 := zero_comp

  HasLimit.mk
    { cone :=
        PullbackCone.mk a' b' <| by
          simp? at ha' hb' says
            simp only [parallelPair_obj_zero, Fork.ofι_pt, Fork.ι_ofι] at ha' hb'
          rw [ha', hb']
      isLimit :=
        PullbackCone.IsLimit.mk _
          (fun s =>
            kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) <|
              prod.hom_ext
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.fst =
                      PullbackCone.snd s ≫ b ≫ f := by simp only [prod.lift_fst, Category.assoc]
                  _ = PullbackCone.fst s ≫ a ≫ f := by rw [PullbackCone.condition_assoc]
                  _ = PullbackCone.fst s ≫ 0 := by rw [haf]
                  _ = 0 ≫ Limits.prod.fst := by rw [comp_zero, zero_comp]
                  )
                (calc
                  ((PullbackCone.snd s ≫ b) ≫ prod.lift f g) ≫ Limits.prod.snd =
                      PullbackCone.snd s ≫ b ≫ g := by
                    simp only [prod.lift_snd, Category.assoc]
                  _ = PullbackCone.snd s ≫ 0 := by rw [hbg]
                  _ = 0 ≫ Limits.prod.snd := by rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_mono a).1 <| by
              rw [KernelFork.ι_ofι] at ha'
              simp [ha', PullbackCone.condition s])
          (fun s =>
            (cancel_mono b).1 <| by
              rw [KernelFork.ι_ofι] at hb'
              simp [hb'])
          fun s m h₁ _ =>
          (cancel_mono (kernel.ι (prod.lift f g))).1 <|
            calc
              m ≫ kernel.ι (prod.lift f g) = m ≫ a' ≫ a := by
                congr
                exact ha'.symm
              _ = PullbackCone.fst s ≫ a := by rw [← Category.assoc, h₁]
              _ = PullbackCone.snd s ≫ b := PullbackCone.condition s
              _ =
                  kernel.lift (prod.lift f g) (PullbackCone.snd s ≫ b) _ ≫
                    kernel.ι (prod.lift f g) := by rw [kernel.lift_ι]
               }
#align category_theory.normal_mono_category.pullback_of_mono CategoryTheory.NormalMonoCategory.pullback_of_mono

section

attribute [local instance] pullback_of_mono

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
private abbrev P {X Y : C} (f g : X ⟶ Y) [Mono (prod.lift (𝟙 X) f)] [Mono (prod.lift (𝟙 X) g)] :
    C :=
  pullback (prod.lift (𝟙 X) f) (prod.lift (𝟙 X) g)

/-- The equalizer of `f` and `g` exists. -/
 -- Porting note: changed to irreducible def since irreducible_def was breaking things
@[irreducible, nolint defLemma]
def hasLimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  have huv : (pullback.fst : P f g ⟶ X) = pullback.snd :=
    calc
      (pullback.fst : P f g ⟶ X) = pullback.fst ≫ 𝟙 _ := Eq.symm <| Category.comp_id _
      _ = pullback.fst ≫ prod.lift (𝟙 X) f ≫ Limits.prod.fst := by rw [prod.lift_fst]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ Limits.prod.fst := by rw [pullback.condition_assoc]
      _ = pullback.snd := by rw [prod.lift_fst, Category.comp_id]

  have hvu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.snd ≫ g :=
    calc
      (pullback.fst : P f g ⟶ X) ≫ f = pullback.fst ≫ prod.lift (𝟙 X) f ≫ Limits.prod.snd := by
        rw [prod.lift_snd]
      _ = pullback.snd ≫ prod.lift (𝟙 X) g ≫ Limits.prod.snd := by rw [pullback.condition_assoc]
      _ = pullback.snd ≫ g := by rw [prod.lift_snd]

  have huu : (pullback.fst : P f g ⟶ X) ≫ f = pullback.fst ≫ g := by rw [hvu, ← huv]
  HasLimit.mk
    { cone := Fork.ofι pullback.fst huu
      isLimit :=
        Fork.IsLimit.mk _
          (fun s =>
            pullback.lift (Fork.ι s) (Fork.ι s) <|
              prod.hom_ext (by simp only [prod.lift_fst, Category.assoc])
                (by simp only [prod.comp_lift, Fork.condition s]))
          (fun s => by simp) fun s m h =>
          pullback.hom_ext (by simpa only [pullback.lift_fst] using h)
            (by simpa only [huv.symm, pullback.lift_fst] using h) }
#align category_theory.normal_mono_category.has_limit_parallel_pair CategoryTheory.NormalMonoCategory.hasLimit_parallelPair

end

section

attribute [local instance] hasLimit_parallelPair

/-- A `NormalMonoCategory` category with finite products and kernels has all equalizers. -/
instance (priority := 100) hasEqualizers : HasEqualizers C :=
  hasEqualizers_of_hasLimit_parallelPair _
#align category_theory.normal_mono_category.has_equalizers CategoryTheory.NormalMonoCategory.hasEqualizers

end

/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
theorem epi_of_zero_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsColimit (CokernelCofork.ofπ (0 : Y ⟶ Z) (show f ≫ 0 = 0 by simp))) : Epi f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalMonoOfMono (equalizer.ι u v)
    obtain ⟨m, hm⟩ := equalizer.lift' f huv
    have hwf : f ≫ w = 0 := by rw [← hm, Category.assoc, hw, comp_zero]
    obtain ⟨n, hn⟩ := CokernelCofork.IsColimit.desc' l _ hwf
    rw [Cofork.π_ofπ, zero_comp] at hn
    have : IsIso (equalizer.ι u v) := by apply isIso_limit_cone_parallelPair_of_eq hn.symm hl
    apply (cancel_epi (equalizer.ι u v)).1
    exact equalizer.condition _ _⟩
#align category_theory.normal_mono_category.epi_of_zero_cokernel CategoryTheory.NormalMonoCategory.epi_of_zero_cokernel

section

variable [HasZeroObject C]

open ZeroObject

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
theorem epi_of_zero_cancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) : Epi f :=
  epi_of_zero_cokernel f 0 <| zeroCokernelOfZeroCancel f hf
#align category_theory.normal_mono_category.epi_of_zero_cancel CategoryTheory.NormalMonoCategory.epi_of_zero_cancel

end

end CategoryTheory.NormalMonoCategory

namespace CategoryTheory.NormalEpiCategory

variable [HasFiniteCoproducts C] [HasCokernels C] [NormalEpiCategory C]

/-- The pushout of two epimorphisms exists. -/
@[irreducible, nolint defLemma] -- Porting note: made a def and re-added irreducible
def pushout_of_epi {X Y Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [Epi a] [Epi b] :
    HasColimit (span a b) :=
  let ⟨P, f, hfa, i⟩ := normalEpiOfEpi a
  let ⟨Q, g, hgb, i'⟩ := normalEpiOfEpi b
  let ⟨a', ha'⟩ :=
    CokernelCofork.IsColimit.desc' i (cokernel.π (coprod.desc f g)) <|
      calc
        f ≫ cokernel.π (coprod.desc f g) =
            coprod.inl ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inl_desc_assoc]
        _ = coprod.inl ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _

  let ⟨b', hb'⟩ :=
    CokernelCofork.IsColimit.desc' i' (cokernel.π (coprod.desc f g)) <|
      calc
        g ≫ cokernel.π (coprod.desc f g) =
            coprod.inr ≫ coprod.desc f g ≫ cokernel.π (coprod.desc f g) := by
          rw [coprod.inr_desc_assoc]
        _ = coprod.inr ≫ (0 : P ⨿ Q ⟶ cokernel (coprod.desc f g)) := by rw [cokernel.condition]
        _ = 0 := HasZeroMorphisms.comp_zero _ _

  HasColimit.mk
    { cocone :=
        PushoutCocone.mk a' b' <| by
          simp only [Cofork.π_ofπ] at ha' hb'
          rw [ha', hb']
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s =>
            cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) <|
              coprod.hom_ext
                (calc
                  coprod.inl ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      f ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inl_desc_assoc]
                  _ = f ≫ a ≫ PushoutCocone.inl s := by rw [PushoutCocone.condition]
                  _ = 0 ≫ PushoutCocone.inl s := by rw [← Category.assoc, eq_whisker hfa]
                  _ = coprod.inl ≫ 0 := by rw [comp_zero, zero_comp]
                  )
                (calc
                  coprod.inr ≫ coprod.desc f g ≫ b ≫ PushoutCocone.inr s =
                      g ≫ b ≫ PushoutCocone.inr s := by rw [coprod.inr_desc_assoc]
                  _ = 0 ≫ PushoutCocone.inr s := by rw [← Category.assoc, eq_whisker hgb]
                  _ = coprod.inr ≫ 0 := by rw [comp_zero, zero_comp]
                  ))
          (fun s =>
            (cancel_epi a).1 <| by
              rw [CokernelCofork.π_ofπ] at ha'
              have reassoced {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : a ≫ a' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker ha']
              simp [reassoced , PushoutCocone.condition s])
          (fun s =>
            (cancel_epi b).1 <| by
              rw [CokernelCofork.π_ofπ] at hb'
              have reassoced' {W : C} (h : cokernel (coprod.desc f g) ⟶ W) : b ≫ b' ≫ h
                = cokernel.π (coprod.desc f g) ≫ h := by rw [← Category.assoc, eq_whisker hb']
              simp [reassoced'])
          fun s m h₁ _ =>
          (cancel_epi (cokernel.π (coprod.desc f g))).1 <|
            calc
              cokernel.π (coprod.desc f g) ≫ m = (a ≫ a') ≫ m := by
                congr
                exact ha'.symm
              _ = a ≫ PushoutCocone.inl s := by rw [Category.assoc, h₁]
              _ = b ≫ PushoutCocone.inr s := PushoutCocone.condition s
              _ =
                  cokernel.π (coprod.desc f g) ≫
                    cokernel.desc (coprod.desc f g) (b ≫ PushoutCocone.inr s) _ := by
                rw [cokernel.π_desc]
               }
#align category_theory.normal_epi_category.pushout_of_epi CategoryTheory.NormalEpiCategory.pushout_of_epi

section

attribute [local instance] pushout_of_epi

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
private abbrev Q {X Y : C} (f g : X ⟶ Y) [Epi (coprod.desc (𝟙 Y) f)] [Epi (coprod.desc (𝟙 Y) g)] :
    C :=
  pushout (coprod.desc (𝟙 Y) f) (coprod.desc (𝟙 Y) g)

/-- The coequalizer of `f` and `g` exists. -/
@[irreducible, nolint defLemma] -- Porting note: changed to def and restored irreducible
def hasColimit_parallelPair {X Y : C} (f g : X ⟶ Y) : HasColimit (parallelPair f g) :=
  have huv : (pushout.inl : Y ⟶ Q f g) = pushout.inr :=
    calc
      (pushout.inl : Y ⟶ Q f g) = 𝟙 _ ≫ pushout.inl := Eq.symm <| Category.id_comp _
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl := by rw [coprod.inl_desc]
      _ = (coprod.inl ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr := by
        simp only [Category.assoc, pushout.condition]
      _ = pushout.inr := by rw [coprod.inl_desc, Category.id_comp]

  have hvu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inr :=
    calc
      f ≫ (pushout.inl : Y ⟶ Q f g) = (coprod.inr ≫ coprod.desc (𝟙 Y) f) ≫ pushout.inl := by
        rw [coprod.inr_desc]
      _ = (coprod.inr ≫ coprod.desc (𝟙 Y) g) ≫ pushout.inr := by
        simp only [Category.assoc, pushout.condition]
      _ = g ≫ pushout.inr := by rw [coprod.inr_desc]

  have huu : f ≫ (pushout.inl : Y ⟶ Q f g) = g ≫ pushout.inl := by rw [hvu, huv]
  HasColimit.mk
    { cocone := Cofork.ofπ pushout.inl huu
      isColimit :=
        Cofork.IsColimit.mk _
          (fun s =>
            pushout.desc (Cofork.π s) (Cofork.π s) <|
              coprod.hom_ext (by simp only [coprod.inl_desc_assoc])
                (by simp only [coprod.desc_comp, Cofork.condition s]))
          (fun s => by simp only [pushout.inl_desc, Cofork.π_ofπ]) fun s m h =>
          pushout.hom_ext (by simpa only [pushout.inl_desc] using h)
            (by simpa only [huv.symm, pushout.inl_desc] using h) }
#align category_theory.normal_epi_category.has_colimit_parallel_pair CategoryTheory.NormalEpiCategory.hasColimit_parallelPair

end

section

attribute [local instance] hasColimit_parallelPair

/-- A `NormalEpiCategory` category with finite coproducts and cokernels has all coequalizers. -/
instance (priority := 100) hasCoequalizers : HasCoequalizers C :=
  hasCoequalizers_of_hasColimit_parallelPair _
#align category_theory.normal_epi_category.has_coequalizers CategoryTheory.NormalEpiCategory.hasCoequalizers

end

/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
theorem mono_of_zero_kernel {X Y : C} (f : X ⟶ Y) (Z : C)
    (l : IsLimit (KernelFork.ofι (0 : Z ⟶ X) (show 0 ≫ f = 0 by simp))) : Mono f :=
  ⟨fun u v huv => by
    obtain ⟨W, w, hw, hl⟩ := normalEpiOfEpi (coequalizer.π u v)
    obtain ⟨m, hm⟩ := coequalizer.desc' f huv
    have reassoced {W : C} (h : coequalizer u v ⟶ W) : w ≫ coequalizer.π u v ≫ h = 0 ≫ h := by
      rw [← Category.assoc, eq_whisker hw]
    have hwf : w ≫ f = 0 := by rw [← hm, reassoced, zero_comp]
    obtain ⟨n, hn⟩ := KernelFork.IsLimit.lift' l _ hwf
    rw [Fork.ι_ofι, HasZeroMorphisms.comp_zero] at hn
    have : IsIso (coequalizer.π u v) := by
      apply isIso_colimit_cocone_parallelPair_of_eq hn.symm hl
    apply (cancel_mono (coequalizer.π u v)).1
    exact coequalizer.condition _ _⟩
#align category_theory.normal_epi_category.mono_of_zero_kernel CategoryTheory.NormalEpiCategory.mono_of_zero_kernel

section

variable [HasZeroObject C]

open ZeroObject

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
theorem mono_of_cancel_zero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) : Mono f :=
  mono_of_zero_kernel f 0 <| zeroKernelOfCancelZero f hf
#align category_theory.normal_epi_category.mono_of_cancel_zero CategoryTheory.NormalEpiCategory.mono_of_cancel_zero

end

end CategoryTheory.NormalEpiCategory
