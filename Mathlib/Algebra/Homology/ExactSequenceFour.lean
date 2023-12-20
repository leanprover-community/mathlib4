import Mathlib.Algebra.Homology.ExactSequence

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {S : ComposableArrows C 3}
  (hS : S.IsComplex)

variable (cc : CokernelCofork (S.map' 0 1)) (kf : KernelFork (S.map' 2 3))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

def cokerToKer : cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' 0 1 ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero' 1 2 3)) = 0 from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero 0)))

@[reassoc (attr := simp)]
lemma cokerToKer_fac : cc.π ≫ hS.cokerToKer cc kf hcc hkf ≫ kf.ι = S.map' 1 2 := by
  simp [cokerToKer]

noncomputable def opcyclesToCycles
    [(S.sc' hS 0 1 2).HasRightHomology] [(S.sc' hS 1 2 3).HasLeftHomology] :
    (S.sc' hS 0 1 2 _ _ _).opcycles ⟶ (S.sc' hS 1 2 3 _ _ _).cycles :=
  hS.cokerToKer _ _ (S.sc' hS 0 1 2 _ _ _).opcyclesIsCokernel
    (S.sc' hS 1 2 3 _ _ _).cyclesIsKernel

@[reassoc (attr := simp)]
lemma opcyclesToCycles_fac
    [(S.sc' hS 0 1 2 _ _ _).HasRightHomology] [(S.sc' hS 1 2 3 _ _ _).HasLeftHomology] :
    (S.sc' hS 0 1 2 _ _ _).pOpcycles ≫ hS.opcyclesToCycles ≫ (S.sc' hS 1 2 3 _ _ _).iCycles =
      S.map' 1 2 :=
  hS.cokerToKer_fac _ _ (S.sc' hS 0 1 2 _ _ _).opcyclesIsCokernel
    (S.sc' hS 1 2 3 _ _ _).cyclesIsKernel

end IsComplex

end HasZeroMorphisms

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {S : ComposableArrows C 3}

namespace IsComplex

variable (hS : S.IsComplex) (cc : CokernelCofork (S.map' 0 1)) (kf : KernelFork (S.map' 2 3))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

lemma epi_cokerToKer (hS' : (S.sc' hS 1 2 3).Exact) :
    Epi (hS.cokerToKer cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Epi cc.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext hcc⟩
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i, h.f'_i, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i,
      assoc, IsComplex.cokerToKer_fac]
  exact epi_of_epi_fac fac

lemma mono_cokerToKer (hS' : (S.sc' hS 0 1 2).Exact) :
    Mono (hS.cokerToKer cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  have : Mono kf.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext hkf⟩
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p, h.p_g', ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p,
      cokerToKer_fac]
  exact mono_of_mono_fac fac

end IsComplex

end Preadditive

section Balanced

variable {C : Type*} [Category C] [Preadditive C] [Balanced C]
  {S : ComposableArrows C 3}

namespace Exact

variable (hS : S.Exact) (cc : CokernelCofork (S.map' 0 1)) (kf : KernelFork (S.map' 2 3))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

def cokerToKer : cc.pt ⟶ kf.pt :=
  hS.toIsComplex.cokerToKer cc kf hcc hkf

@[reassoc (attr := simp)]
lemma cokerToKer_fac : cc.π ≫ hS.cokerToKer cc kf hcc hkf ≫ kf.ι = S.map' 1 2 := by
  simp [cokerToKer]

noncomputable def opcyclesToCycles
    [(hS.sc' 0 1 2).HasRightHomology] [(hS.sc' 1 2 3).HasLeftHomology] :
    (hS.sc' 0 1 2 _ _ _).opcycles ⟶ (hS.sc' 1 2 3 _ _ _).cycles :=
  hS.toIsComplex.opcyclesToCycles

@[reassoc (attr := simp)]
lemma opcyclesToCycles_fac
    [(hS.sc' 0 1 2 _ _ _).HasRightHomology] [(hS.sc' 1 2 3 _ _ _).HasLeftHomology] :
    (hS.sc' 0 1 2 _ _ _).pOpcycles ≫ hS.opcyclesToCycles ≫ (hS.sc' 1 2 3 _ _ _).iCycles =
      S.map' 1 2 :=
  hS.toIsComplex.opcyclesToCycles_fac

instance isIso_cokerToKer : IsIso (hS.cokerToKer cc kf hcc hkf) := by
  have : Mono (hS.cokerToKer cc kf hcc hkf) := hS.toIsComplex.mono_cokerToKer cc kf hcc hkf
    (hS.exact 0)
  have : Epi (hS.cokerToKer cc kf hcc hkf) := hS.epi_cokerToKer cc kf hcc hkf (hS.exact 1)
  apply isIso_of_mono_of_epi

@[simps! hom]
noncomputable def cokerIsoKer : cc.pt ≅ kf.pt :=
  asIso (hS.cokerToKer cc kf hcc hkf)

@[reassoc (attr := simp)]
lemma cokerIsoKer_hom_inv_id :
    hS.cokerToKer cc kf hcc hkf ≫ (hS.cokerIsoKer cc kf hcc hkf).inv = 𝟙 _ :=
  (hS.cokerIsoKer cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
lemma cokerIsoKer_inv_hom_id :
    (hS.cokerIsoKer cc kf hcc hkf).inv ≫ hS.cokerToKer cc kf hcc hkf = 𝟙 _ :=
  (hS.cokerIsoKer cc kf hcc hkf).inv_hom_id

section

variable [(hS.sc' 0 1 2).HasRightHomology] [(hS.sc' 1 2 3).HasLeftHomology]

instance isIso_opcyclesToCycles : IsIso hS.opcyclesToCycles := by
  apply hS.isIso_cokerToKer

noncomputable def opcyclesIsoCycles :
    (hS.sc' 0 1 2 _ _ _).opcycles ≅ (hS.sc' 1 2 3 _ _ _).cycles :=
  hS.cokerIsoKer _ _ (hS.sc' 0 1 2 _ _ _).opcyclesIsCokernel
    (hS.sc' 1 2 3 _ _ _).cyclesIsKernel

@[simp]
lemma opcyclesIsoCycles_hom :
    hS.opcyclesIsoCycles.hom = hS.opcyclesToCycles := rfl

@[reassoc (attr := simp)]
lemma opcyclesIsoCycles_hom_inv_id :
    hS.opcyclesToCycles ≫ hS.opcyclesIsoCycles.inv = 𝟙 _ :=
  hS.opcyclesIsoCycles.hom_inv_id

@[reassoc (attr := simp)]
lemma opcyclesIsoCycles_inv_hom_id :
    hS.opcyclesIsoCycles.inv ≫ hS.opcyclesToCycles = 𝟙 _ :=
  hS.opcyclesIsoCycles.inv_hom_id

end

end Exact

end Balanced

end ComposableArrows

end CategoryTheory
