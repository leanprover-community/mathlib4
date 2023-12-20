import Mathlib.Algebra.Homology.ExactSequence

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : ℕ} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : ℕ)

section

variable (hk : k ≤ n) (cc : CokernelCofork (S.map' k (k + 1)))
  (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf)

def cokerToKer : cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = 0 from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

@[reassoc (attr := simp)]
lemma cokerToKer_fac : cc.π ≫ hS.cokerToKer k hk cc kf hcc hkf ≫ kf.ι =
    S.map' (k + 1) (k + 2) := by
  simp [cokerToKer]

end

section

variable (hk : k ≤ n := by linarith)
  [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology]

noncomputable def opcyclesToCycles :
    (S.sc hS k _).opcycles ⟶ (S.sc hS (k + 1) _).cycles :=
  hS.cokerToKer k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
lemma opcyclesToCycles_fac :
    (S.sc hS k _).pOpcycles ≫ hS.opcyclesToCycles k ≫ (S.sc hS (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.cokerToKer_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
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

lemma epi_cokerToKer (hS' : (S.sc hS (k + 1)).Exact) :
    Epi (hS.cokerToKer k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Epi cc.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext hcc⟩
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      assoc, IsComplex.cokerToKer_fac]
  exact epi_of_epi_fac fac

lemma mono_cokerToKer (hS' : (S.sc hS k).Exact) :
    Mono (hS.cokerToKer k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Mono kf.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext hkf⟩
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      cokerToKer_fac]
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

def cokerToKer : cc.pt ⟶ kf.pt :=
  hS.toIsComplex.cokerToKer k hk cc kf hcc hkf

@[reassoc (attr := simp)]
lemma cokerToKer_fac : cc.π ≫ hS.cokerToKer k hk cc kf hcc hkf ≫ kf.ι =
    S.map' (k + 1) (k + 2) := by
  simp [cokerToKer]

instance isIso_cokerToKer : IsIso (hS.cokerToKer k hk cc kf hcc hkf) := by
  have : Mono (hS.cokerToKer k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

@[simps! hom]
noncomputable def cokerIsoKer : cc.pt ≅ kf.pt :=
  asIso (hS.cokerToKer k hk cc kf hcc hkf)

@[reassoc (attr := simp)]
lemma cokerIsoKer_hom_inv_id :
    hS.cokerToKer k hk cc kf hcc hkf ≫ (hS.cokerIsoKer k hk cc kf hcc hkf).inv = 𝟙 _ :=
  (hS.cokerIsoKer k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
lemma cokerIsoKer_inv_hom_id :
    (hS.cokerIsoKer k hk cc kf hcc hkf).inv ≫ hS.cokerToKer k hk cc kf hcc hkf = 𝟙 _ :=
  (hS.cokerIsoKer k hk cc kf hcc hkf).inv_hom_id

end

variable (k : ℕ) (hk : k ≤ n := by linarith)
  [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology]

noncomputable def opcyclesIsoCycles :
    (hS.sc k _).opcycles ≅ (hS.sc (k + 1) _).cycles :=
  hS.cokerIsoKer k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

lemma opcyclesIsoCycles_hom :
    (hS.opcyclesIsoCycles k).hom = hS.toIsComplex.opcyclesToCycles k hk := rfl

@[reassoc (attr := simp)]
lemma opcyclesIsoCycles_hom_fac :
    (hS.sc k _).pOpcycles ≫ (hS.opcyclesIsoCycles k).hom ≫ (hS.sc (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.opcyclesToCycles_fac k hk

end Exact

end Balanced

end ComposableArrows

end CategoryTheory
