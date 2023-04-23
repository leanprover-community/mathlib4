import Mathlib.Algebra.Homology.ShortComplex.RightHomology

namespace CategoryTheory

open Category Limits

variable {C D : Type _} [Category C] [Abelian C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

namespace ShortComplex

@[simp]
noncomputable def abelianImageToKernel :
    Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      equalizer_as_kernel, kernel.lift_ι_assoc, zero, comp_zero])

@[reassoc (attr := simp)]
lemma abelianImageToKernel_comp_kernel_ι :
  S.abelianImageToKernel ≫ kernel.ι S.g = Abelian.image.ι S.f := kernel.lift_ι _ _ _

namespace LeftHomologyData

noncomputable def of_abelian : S.LeftHomologyData := by
  let γ := kernel.ι S.g ≫ cokernel.π S.f
  let f' := kernel.lift S.g S.f S.zero
  have hf' : f' = kernel.lift γ f' (by simp) ≫ kernel.ι γ := by rw [kernel.lift_ι]
  have wπ : f' ≫ cokernel.π (kernel.ι γ) = 0 := by
    rw [hf']
    simp only [assoc, cokernel.condition, comp_zero]
  let α := kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [←cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])
  haveI : Mono (α ≫ kernel.ι S.g) := by
    simp only [kernel.lift_ι]
    infer_instance
  haveI : Mono α := mono_of_mono α (kernel.ι S.g)
  have αγ : α ≫ γ = 0 := by simp
  have hα : IsLimit (KernelFork.ofι α αγ) :=
    KernelFork.IsLimit.ofι _ _
      (fun k hk => kernel.lift _ (k ≫ kernel.ι S.g) (by rw [assoc, hk]))
      (fun k hk => by simp only [← cancel_mono (kernel.ι S.g), assoc, kernel.lift_ι])
      (fun k hk b hb => by simp only [← cancel_mono α,
        ← cancel_mono (kernel.ι S.g), hb, assoc, kernel.lift_ι])
  let e : Abelian.image S.f ≅ kernel γ :=
    IsLimit.conePointUniqueUpToIso hα (limit.isLimit _)
  have he : e.hom ≫ kernel.ι γ = S.abelianImageToKernel :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have fac : f' = Abelian.factorThruImage S.f ≫ e.hom ≫ kernel.ι γ := by
    rw [hf', he]
    simp only [kernel.lift_ι, abelianImageToKernel, ← cancel_mono (kernel.ι S.g), assoc]
  have hπ : IsColimit (CokernelCofork.ofπ _ wπ) :=
    CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => cokernel.desc _ x (by
      simp only [← cancel_epi e.hom, ← cancel_epi (Abelian.factorThruImage S.f), comp_zero]
      simpa only [fac, assoc] using hx))
    (fun x hx => cokernel.π_desc _ _ _)
    (fun x hx b hb => coequalizer.hom_ext (by simp only [hb, cokernel.π_desc]))
  exact
  { K := kernel S.g,
    H := Abelian.coimage (kernel.ι S.g ≫ cokernel.π S.f)
    i := kernel.ι _
    π := cokernel.π _
    wi := kernel.condition _
    hi := kernelIsKernel _
    wπ := wπ
    hπ := hπ }

end LeftHomologyData

end ShortComplex

end CategoryTheory
