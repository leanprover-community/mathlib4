/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Exact sequences with four terms

The main definition in this file is `ComposableArrows.Exact.cokerIsoKer`:
given an exact sequence `S` (involving at least four objects),
this is the isomorphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. This is intended
to be used for exact sequences in abelian categories, but the
construction works for preadditive balanced categories.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

section

/-- If `S` is a complex, this is the morphism from a cokernel of `S.map' k (k + 1)`
to a kernel of `S.map' (k + 2) (k + 3)`. -/
def cokerToKer' (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

@[reassoc (attr := simp)]
lemma cokerToKer'_fac (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι =
      S.map' (k + 1) (k + 2) := by
  simp [cokerToKer']

end

section

/-- If `S` is a complex, this is the morphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. -/
noncomputable def cokerToKer (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1)) ⟶ kernel (S.map' (k + 2) (k + 3)) :=
  hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
lemma cokerToKer_fac (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ hS.cokerToKer k hk ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

end

section

/-- If `S` is a complex, this is the morphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`. -/
noncomputable def opcyclesToCycles (hk : k ≤ n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).opcycles ⟶ (S.sc hS (k + 1) _).cycles :=
  hS.cokerToKer' k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
lemma opcyclesToCycles_fac (hk : k ≤ n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).pOpcycles ≫ hS.opcyclesToCycles k ≫ (S.sc hS (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

end

end IsComplex

end HasZeroMorphisms

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {n : ℕ} {S : ComposableArrows C (n + 3)}

namespace IsComplex

variable (hS : S.IsComplex) (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

lemma epi_cokerToKer' (hS' : (S.sc hS (k + 1)).Exact) :
    Epi (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Epi cc.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext hcc⟩
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      assoc, IsComplex.cokerToKer'_fac]
  exact epi_of_epi_fac fac

lemma mono_cokerToKer' (hS' : (S.sc hS k).Exact) :
    Mono (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Mono kf.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext hkf⟩
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      cokerToKer'_fac]
  exact mono_of_mono_fac fac

end IsComplex

end Preadditive

section Balanced

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : ℕ}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

namespace Exact

section

variable (k : ℕ) (hk : k ≤ n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

/-- If `S` is an exact sequence, this is the morphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
abbrev cokerToKer' : cc.pt ⟶ kf.pt :=
  hS.toIsComplex.cokerToKer' k hk cc kf hcc hkf

instance isIso_cokerToKer' : IsIso (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have : Mono (hS.cokerToKer' k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer' k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer' k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer' k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

/-- If `S` is an exact sequence, this is the isomorphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
@[simps! hom]
noncomputable def cokerIsoKer' : cc.pt ≅ kf.pt :=
  asIso (hS.cokerToKer' k hk cc kf hcc hkf)

@[reassoc (attr := simp)]
lemma cokerIsoKer'_hom_inv_id :
    hS.cokerToKer' k hk cc kf hcc hkf ≫ (hS.cokerIsoKer' k hk cc kf hcc hkf).inv = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
lemma cokerIsoKer'_inv_hom_id :
    (hS.cokerIsoKer' k hk cc kf hcc hkf).inv ≫ hS.cokerToKer' k hk cc kf hcc hkf = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id

end

section

/-- If `S` is an exact sequence, this is the isomorphism from the cokernel
of `S.map' k (k + 1)` to the kernel of `S.map' (k + 2) (k + 3)`. -/
noncomputable def cokerIsoKer (k : ℕ) (hk : k ≤ n := by lia)
  [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1) _ _) ≅ kernel (S.map' (k + 2) (k + 3) _ _) :=
  hS.cokerIsoKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
lemma cokerIsoKer_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ (hS.cokerIsoKer k).hom ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.cokerToKer_fac k

end

section

/-- If `S` is an exact sequence, this is the isomorphism from the opcycles of `S` in
degree `k + 1` to the cycles of `S` in degree `k + 2`. -/
noncomputable def opcyclesIsoCycles (k : ℕ) (hk : k ≤ n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).opcycles ≅ (hS.sc (k + 1) _).cycles :=
  hS.cokerIsoKer' k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
lemma opcyclesIsoCycles_hom_fac (k : ℕ) (hk : k ≤ n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).pOpcycles ≫ (hS.opcyclesIsoCycles k).hom ≫ (hS.sc (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.opcyclesToCycles_fac k hk

end

end Exact

end Balanced

end ComposableArrows

end CategoryTheory
