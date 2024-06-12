import Mathlib.Algebra.Homology.ShortComplex.Abelian

open CategoryTheory Limits Category

variable {A : Type*} [Category A] [Abelian A]
variable {X Y : A} (f : X ⟶ Y)

noncomputable def test : KernelFork (cokernel.π f) := by
  refine KernelFork.ofι (image.ι f) ?_
  refine Eq.symm (image.ext f ?w)
  simp only [comp_zero, image.fac_assoc, cokernel.condition]



variable (S : ShortComplex A)

namespace ShortComplex

noncomputable def LeftHomologyData.ofIsColimitCokernelCoforkAbelianImageToKernel
    (cc : CokernelCofork S.abelianImageToKernel) (hcc : IsColimit cc) :
    S.LeftHomologyData where
  K := kernel S.g
  H := cc.pt
  i := kernel.ι S.g
  π := cc.π
  wi := by simp
  hi := kernelIsKernel S.g
  wπ := by
    have h := Abelian.factorThruImage S.f ≫= cc.condition
    rw [comp_zero, ← assoc] at h
    convert h
    simp [← cancel_mono (kernel.ι _)]
  hπ := CokernelCofork.IsColimit.ofπ _ _
      (fun a ha ↦ hcc.desc (CokernelCofork.ofπ (π := a) (by
        rw [← cancel_epi (Abelian.factorThruImage S.f), comp_zero, ← assoc]
        convert ha
        simp [← cancel_mono (kernel.ι _)])))
      (fun a ha ↦ hcc.fac _ _)
      (fun a ha b hb ↦ Cofork.IsColimit.hom_ext hcc (by simpa using hb))

noncomputable def homologyIsoCokernelAbelianImageToKernel :
    S.homology ≅ cokernel S.abelianImageToKernel :=
  (LeftHomologyData.ofIsColimitCokernelCoforkAbelianImageToKernel S _
    (cokernelIsCokernel _)).homologyIso

end ShortComplex

#exit





#check Limits.image.ι f

#check Limits.cokernel.π f

example : 0 = 0 := by
  set c : KernelFork (Limits.cokernel.π f) := by
    refine KernelFork.ofι (Limits.image.ι f) ?_
    refine Eq.symm (image.ext f ?w)
    simp only [comp_zero, image.fac_assoc, cokernel.condition]
  have : IsLimit c := by
    refine IsKernel.isoKernel (cokernel.π f) (image.ι f) ?hs ?i ?h
