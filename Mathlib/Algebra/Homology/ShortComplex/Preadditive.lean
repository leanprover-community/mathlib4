import Mathlib.Algebra.Homology.ShortComplex.Homology

namespace CategoryTheory

open Category Limits

variable {C : Type _} [Category C] [Preadditive C]

lemma mono_of_isZero_kernel' {X Y : C} {f : X ⟶ Y} (c : KernelFork f) (hc : IsLimit c)
    (h : IsZero c.pt) : Mono f := ⟨fun g₁ g₂ eq => by
  rw [← sub_eq_zero, ← Preadditive.sub_comp] at eq
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hc _ eq
  rw [← sub_eq_zero, ← ha, h.eq_of_tgt a 0, zero_comp]⟩

lemma mono_of_isZero_kernel {X Y : C} (f : X ⟶ Y) [HasKernel f] (h : IsZero (kernel f)) :
    Mono f :=
  mono_of_isZero_kernel' _ (kernelIsKernel _) h

lemma epi_of_isZero_cokernel' {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) (hc : IsColimit c)
    (h : IsZero c.pt) : Epi f := ⟨fun g₁ g₂ eq => by
  rw [← sub_eq_zero, ← Preadditive.comp_sub] at eq
  obtain ⟨a, ha⟩ := CokernelCofork.IsColimit.desc' hc _ eq
  rw [← sub_eq_zero, ← ha, h.eq_of_src a 0, comp_zero]⟩

lemma epi_of_isZero_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (h : IsZero (cokernel f)) :
    Epi f :=
  epi_of_isZero_cokernel' _ (cokernelIsCokernel _) h

end CategoryTheory
