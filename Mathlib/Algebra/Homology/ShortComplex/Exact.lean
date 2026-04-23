/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Exact short complexes

When `S : ShortComplex C`, this file defines a structure
`S.Exact` which expresses the exactness of `S`, i.e. there
exists a homology data `h : S.HomologyData` such that
`h.left.H` is zero. When `[S.HasHomology]`, it is equivalent
to the assertion `IsZero S.homology`.

Almost by construction, this notion of exactness is self dual,
see `Exact.op` and `Exact.unop`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- The assertion that the short complex `S : ShortComplex C` is exact. -/
structure Exact : Prop where
  /-- the condition that there exists a homology data whose `left.H` field is zero -/
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

variable {S}

lemma Exact.hasHomology (h : S.Exact) : S.HasHomology :=
  HasHomology.mk' h.condition.choose

lemma Exact.hasZeroObject (h : S.Exact) : HasZeroObject C :=
  ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

variable (S)

lemma exact_iff_isZero_homology [S.HasHomology] :
    S.Exact ↔ IsZero S.homology := by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

variable {S}

lemma LeftHomologyData.exact_iff [S.HasHomology]
    (h : S.LeftHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

lemma RightHomologyData.exact_iff [S.HasHomology]
    (h : S.RightHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

variable (S)

lemma exact_iff_isZero_leftHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.leftHomology :=
  LeftHomologyData.exact_iff _

lemma exact_iff_isZero_rightHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.rightHomology :=
  RightHomologyData.exact_iff _

variable {S}

lemma HomologyData.exact_iff (h : S.HomologyData) :
    S.Exact ↔ IsZero h.left.H := by
  haveI := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left

lemma HomologyData.exact_iff' (h : S.HomologyData) :
    S.Exact ↔ IsZero h.right.H := by
  haveI := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

variable (S)

lemma exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] :
    S.Exact ↔ Nonempty (S.homology ≅ 0) := by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

lemma exact_of_iso (e : S₁ ≅ S₂) (h : S₁.Exact) : S₂.Exact := by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩

lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

lemma exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Mono S₁.f ↔ S₂.Exact ∧ Mono S₂.f := by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e, this]

lemma exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact ∧ Epi S₂.g := by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e, this]

lemma exact_of_isZero_X₂ (h : IsZero S.X₂) : S.Exact := by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

lemma exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    S₁.Exact ↔ S₂.Exact := by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

variable {S}

lemma HomologyData.exact_iff_i_p_zero (h : S.HomologyData) :
    S.Exact ↔ h.left.i ≫ h.right.p = 0 := by
  haveI := HasHomology.mk' h
  rw [h.left.exact_iff, ← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0, zero_comp, comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

variable (S)

lemma exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 :=
  (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

lemma exact_iff_iCycles_pOpcycles_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0 :=
  S.exact_iff_i_p_zero _ _

lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  haveI := HasLeftHomology.hasCokernel S
  haveI := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

variable {S}

lemma Exact.op (h : S.Exact) : S.op.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩

lemma Exact.unop {S : ShortComplex Cᵒᵖ} (h : S.Exact) : S.unop.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

variable (S)

@[simp]
lemma exact_op_iff : S.op.Exact ↔ S.Exact :=
  ⟨Exact.unop, Exact.op⟩

@[simp]
lemma exact_unop_iff (S : ShortComplex Cᵒᵖ) : S.unop.Exact ↔ S.Exact :=
  S.unop.exact_op_iff.symm

variable {S}

lemma LeftHomologyData.exact_map_iff (h : S.LeftHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff

lemma RightHomologyData.exact_map_iff (h : S.RightHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) :=
  (h.map F).exact_iff

lemma Exact.map_of_preservesLeftHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F, IsZero.iff_id_eq_zero,
    ← F.map_id, h, F.map_zero]

lemma Exact.map_of_preservesRightHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesRightHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have : S.HasHomology := h.hasHomology
  rw [S.rightHomologyData.exact_iff, IsZero.iff_id_eq_zero] at h
  rw [S.rightHomologyData.exact_map_iff F, IsZero.iff_id_eq_zero,
    ← F.map_id, h, F.map_zero]

lemma Exact.map (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (S.map F).Exact := by
  have := h.hasHomology
  exact h.map_of_preservesLeftHomologyOf F

variable (S)

lemma exact_map_iff_of_faithful [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [F.Faithful] :
    (S.map F).Exact ↔ S.Exact := by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff, IsZero.iff_id_eq_zero,
      LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id, F.map_zero, h]
  · intro h
    exact h.map F

variable {S}

@[reassoc]
lemma Exact.comp_eq_zero (h : S.Exact) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
    {b : S.X₂ ⟶ Y} (hb : S.f ≫ b = 0) : a ≫ b = 0 := by
  have := h.hasHomology
  have eq := h
  rw [exact_iff_iCycles_pOpcycles_zero] at eq
  rw [← S.liftCycles_i a ha, ← S.p_descOpcycles b hb, assoc, reassoc_of% eq,
    zero_comp, comp_zero]

lemma Exact.isZero_of_both_zeros (ex : S.Exact) (hf : S.f = 0) (hg : S.g = 0) :
    IsZero S.X₂ :=
  (ShortComplex.HomologyData.ofZeros S hf hg).exact_iff.1 ex

end

section Preadditive

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

lemma exact_iff_mono [HasZeroObject C] (hf : S.f = 0) :
    S.Exact ↔ Mono S.g := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pOpcycles hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromOpcycles]
    apply mono_comp
  · intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofMonoOfIsZero (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

lemma exact_iff_epi [HasZeroObject C] (hg : S.g = 0) :
    S.Exact ↔ Epi S.f := by
  constructor
  · intro h
    have := h.hasHomology
    simp only [exact_iff_isZero_homology] at h
    haveI := S.isIso_iCycles hg
    haveI : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  · intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofEpiOfIsZero (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

variable {S}

lemma Exact.epi_f' (hS : S.Exact) (h : LeftHomologyData S) : Epi h.f' :=
  epi_of_isZero_cokernel' _ h.hπ (by
    haveI := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

lemma Exact.mono_g' (hS : S.Exact) (h : RightHomologyData S) : Mono h.g' :=
  mono_of_isZero_kernel' _ h.hι (by
    haveI := hS.hasHomology
    dsimp
    simpa only [← h.exact_iff] using hS)

lemma Exact.epi_toCycles (hS : S.Exact) [S.HasLeftHomology] : Epi S.toCycles :=
  hS.epi_f' _

lemma Exact.mono_fromOpcycles (hS : S.Exact) [S.HasRightHomology] : Mono S.fromOpcycles :=
  hS.mono_g' _

lemma LeftHomologyData.exact_iff_epi_f' [S.HasHomology] (h : LeftHomologyData S) :
    S.Exact ↔ Epi h.f' := by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

lemma RightHomologyData.exact_iff_mono_g' [S.HasHomology] (h : RightHomologyData S) :
    S.Exact ↔ Mono h.g' := by
  constructor
  · intro hS
    exact hS.mono_g' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a limit kernel fork `kf` for `S.g`, this is the
left homology data for `S` with `K := kf.pt` and `H := 0`. -/
@[simps]
noncomputable def Exact.leftHomologyDataOfIsLimitKernelFork
    (hS : S.Exact) [HasZeroObject C] (kf : KernelFork S.g) (hkf : IsLimit kf) :
    S.LeftHomologyData where
  K := kf.pt
  H := 0
  i := kf.ι
  π := 0
  wi := kf.condition
  hi := IsLimit.ofIsoLimit hkf (Fork.ext (Iso.refl _) (by simp))
  wπ := comp_zero
  hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff ?_).1
      hS.epi_toCycles
    refine Arrow.isoMk (Iso.refl _)
      (IsLimit.conePointUniqueUpToIso S.cyclesIsKernel hkf) ?_
    apply Fork.IsLimit.hom_ext hkf
    simp [IsLimit.conePointUniqueUpToIso]) (isZero_zero C)

set_option backward.isDefEq.respectTransparency false in
/-- Given an exact short complex `S` and a colimit cokernel cofork `cc` for `S.f`, this is the
right homology data for `S` with `Q := cc.pt` and `H := 0`. -/
@[simps]
noncomputable def Exact.rightHomologyDataOfIsColimitCokernelCofork
    (hS : S.Exact) [HasZeroObject C] (cc : CokernelCofork S.f) (hcc : IsColimit cc) :
    S.RightHomologyData where
  Q := cc.pt
  H := 0
  p := cc.π
  ι := 0
  wp := cc.condition
  hp := IsColimit.ofIsoColimit hcc (Cofork.ext (Iso.refl _) (by simp))
  wι := zero_comp
  hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
    have := hS.hasHomology
    refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
      hS.mono_fromOpcycles
    refine Arrow.isoMk (IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel)
      (Iso.refl _) ?_
    apply Cofork.IsColimit.hom_ext hcc
    simp [IsColimit.coconePointUniqueUpToIso]) (isZero_zero C)

variable (S)

lemma exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles :=
  S.leftHomologyData.exact_iff_epi_f'

lemma exact_iff_mono_fromOpcycles [S.HasHomology] : S.Exact ↔ Mono S.fromOpcycles :=
  S.rightHomologyData.exact_iff_mono_g'

lemma exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] :
    S.Exact ↔ Epi (kernel.lift S.g S.f S.zero) := by
  rw [exact_iff_epi_toCycles]
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) S.cyclesIsoKernel (by cat_disch)

lemma exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero) := by
  rw [exact_iff_mono_fromOpcycles]
  refine (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (Iso.symm ?_)
  exact Arrow.isoMk S.opcyclesIsoCokernel.symm (Iso.refl _) (by cat_disch)

variable {S} in
lemma Exact.mono_cokernelDesc [S.HasHomology] [HasCokernel S.f] (hS : S.Exact) :
    Mono (Limits.cokernel.desc S.f S.g S.zero) :=
  S.exact_iff_mono_cokernel_desc.1 hS

variable {S} in
lemma Exact.epi_kernelLift [S.HasHomology] [HasKernel S.g] (hS : S.Exact) :
    Epi (Limits.kernel.lift S.g S.f S.zero) :=
  S.exact_iff_epi_kernel_lift.1 hS

lemma QuasiIso.exact_iff {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [QuasiIso φ] : S₁.Exact ↔ S₂.Exact := by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))

lemma exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles, assoc, toCycles_i, id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

lemma exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_mono_fromOpcycles]
  have : IsSplitMono S.fromOpcycles :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles)
        id := by
          rw [← cancel_epi S.pOpcycles, p_fromOpcycles_assoc, comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

variable {S}

lemma Exact.mono_g (hS : S.Exact) (hf : S.f = 0) : Mono S.g := by
  have := hS.hasHomology
  have := hS.epi_toCycles
  have : S.iCycles = 0 := by rw [← cancel_epi S.toCycles, comp_zero, toCycles_i, hf]
  apply Preadditive.mono_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.liftCycles_i x₂ hx₂, this, comp_zero]

lemma Exact.epi_f (hS : S.Exact) (hg : S.g = 0) : Epi S.f := by
  have := hS.hasHomology
  have := hS.mono_fromOpcycles
  have : S.pOpcycles = 0 := by rw [← cancel_mono S.fromOpcycles, zero_comp, p_fromOpcycles, hg]
  apply Preadditive.epi_of_cancel_zero
  intro A x₂ hx₂
  rw [← S.p_descOpcycles x₂ hx₂, this, zero_comp]

lemma Exact.mono_g_iff (hS : S.Exact) : Mono S.g ↔ S.f = 0 := by
  constructor
  · intro
    rw [← cancel_mono S.g, zero, zero_comp]
  · exact hS.mono_g

lemma Exact.epi_f_iff (hS : S.Exact) : Epi S.f ↔ S.g = 0 := by
  constructor
  · intro
    rw [← cancel_epi S.f, zero, comp_zero]
  · exact hS.epi_f

lemma Exact.isZero_X₂ (hS : S.Exact) (hf : S.f = 0) (hg : S.g = 0) : IsZero S.X₂ := by
  have := hS.mono_g hf
  rw [IsZero.iff_id_eq_zero, ← cancel_mono S.g, hg, comp_zero, comp_zero]

lemma Exact.isZero_X₂_iff (hS : S.Exact) : IsZero S.X₂ ↔ S.f = 0 ∧ S.g = 0 := by
  constructor
  · intro h
    exact ⟨h.eq_of_tgt _ _, h.eq_of_src _ _⟩
  · rintro ⟨hf, hg⟩
    exact hS.isZero_X₂ hf hg

variable (S)

/-- A splitting for a short complex `S` consists of the data of a retraction `r : X₂ ⟶ X₁`
of `S.f` and section `s : X₃ ⟶ X₂` of `S.g` which satisfy `r ≫ S.f + S.g ≫ s = 𝟙 _` -/
structure Splitting (S : ShortComplex C) where
  /-- a retraction of `S.f` -/
  r : S.X₂ ⟶ S.X₁
  /-- a section of `S.g` -/
  s : S.X₃ ⟶ S.X₂
  /-- the condition that `r` is a retraction of `S.f` -/
  f_r : S.f ≫ r = 𝟙 _ := by cat_disch
  /-- the condition that `s` is a section of `S.g` -/
  s_g : s ≫ S.g = 𝟙 _ := by cat_disch
  /-- the compatibility between the given section and retraction -/
  id : r ≫ S.f + S.g ≫ s = 𝟙 _ := by cat_disch

namespace Splitting

attribute [reassoc (attr := simp)] f_r s_g

variable {S}

@[reassoc]
lemma r_f (s : S.Splitting) : s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s := by rw [← s.id, add_sub_cancel_right]

@[reassoc]
lemma g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f := by rw [← s.id, add_sub_cancel_left]

/-- Given a splitting of a short complex `S`, this shows that `S.f` is a split monomorphism. -/
@[simps] def splitMono_f (s : S.Splitting) : SplitMono S.f := ⟨s.r, s.f_r⟩

lemma isSplitMono_f (s : S.Splitting) : IsSplitMono S.f := ⟨⟨s.splitMono_f⟩⟩

lemma mono_f (s : S.Splitting) : Mono S.f := by
  have := s.isSplitMono_f
  infer_instance

/-- Given a splitting of a short complex `S`, this shows that `S.g` is a split epimorphism. -/
@[simps] def splitEpi_g (s : S.Splitting) : SplitEpi S.g := ⟨s.s, s.s_g⟩

lemma isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g := ⟨⟨s.splitEpi_g⟩⟩

lemma epi_g (s : S.Splitting) : Epi S.g := by
  have := s.isSplitEpi_g
  infer_instance

@[reassoc (attr := simp)]
lemma s_r (s : S.Splitting) : s.s ≫ s.r = 0 := by
  have := s.epi_g
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]

lemma ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s' := by
  have := s.epi_g
  have eq := s.id
  rw [← s'.id, h, add_right_inj, cancel_epi S.g] at eq
  cases s
  congr

lemma ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s' := by
  have := s.mono_f
  have eq := s.id
  rw [← s'.id, h, add_left_inj, cancel_mono S.f] at eq
  cases s
  congr

/-- The left homology data on a short complex equipped with a splitting. -/
@[simps]
noncomputable def leftHomologyData [HasZeroObject C] (s : S.Splitting) :
    LeftHomologyData S := by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by simp [f']
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofEpiOfIsZero _
      (by rw [hf']; infer_instance) (isZero_zero _)
  exact
    { K := S.X₁
      H := 0
      i := S.f
      wi := S.zero
      hi := hi
      π := 0
      wπ := wπ
      hπ := hπ }

/-- The right homology data on a short complex equipped with a splitting. -/
@[simps]
noncomputable def rightHomologyData [HasZeroObject C] (s : S.Splitting) :
    RightHomologyData S := by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by simp [g']
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofMonoOfIsZero _
      (by rw [hg']; dsimp; infer_instance) (isZero_zero _)
  exact
    { Q := S.X₃
      H := 0
      p := S.g
      wp := S.zero
      hp := hp
      ι := 0
      wι := wι
      hι := hι }

/-- The homology data on a short complex equipped with a splitting. -/
@[simps]
noncomputable def homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where
  left := s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

/-- A short complex equipped with a splitting is exact. -/
lemma exact [HasZeroObject C] (s : S.Splitting) : S.Exact :=
  ⟨s.homologyData, isZero_zero _⟩

/-- If a short complex `S` is equipped with a splitting, then `S.X₁` is the kernel of `S.g`. -/
noncomputable def fIsKernel [HasZeroObject C] (s : S.Splitting) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  s.homologyData.left.hi

/-- If a short complex `S` is equipped with a splitting, then `S.X₃` is the cokernel of `S.f`. -/
noncomputable def gIsCokernel [HasZeroObject C] (s : S.Splitting) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  s.homologyData.right.hp

set_option backward.isDefEq.respectTransparency false in
/-- If a short complex `S` has a splitting and `F` is an additive functor, then
`S.map F` also has a splitting. -/
@[simps]
def map (s : S.Splitting) (F : C ⥤ D) [F.Additive] : (S.map F).Splitting where
  r := F.map s.r
  s := F.map s.s
  f_r := by
    dsimp [ShortComplex.map]
    rw [← F.map_comp, f_r, F.map_id]
  s_g := by
    dsimp [ShortComplex.map]
    simp only [← F.map_comp, s_g, F.map_id]
  id := by
    dsimp [ShortComplex.map]
    simp only [← F.map_id, ← s.id, Functor.map_comp, Functor.map_add]

/-- A splitting on a short complex induces splittings on isomorphic short complexes. -/
@[simps]
def ofIso {S₁ S₂ : ShortComplex C} (s : S₁.Splitting) (e : S₁ ≅ S₂) : S₂.Splitting where
  r := e.inv.τ₂ ≫ s.r ≫ e.hom.τ₁
  s := e.inv.τ₃ ≫ s.s ≫ e.hom.τ₂
  f_r := by rw [← e.inv.comm₁₂_assoc, s.f_r_assoc, ← comp_τ₁, e.inv_hom_id, id_τ₁]
  s_g := by rw [assoc, assoc, e.hom.comm₂₃, s.s_g_assoc, ← comp_τ₃, e.inv_hom_id, id_τ₃]
  id := by
    have eq := e.inv.τ₂ ≫= s.id =≫ e.hom.τ₂
    rw [id_comp, ← comp_τ₂, e.inv_hom_id, id_τ₂] at eq
    rw [← eq, assoc, assoc, add_comp, assoc, assoc, comp_add,
      e.hom.comm₁₂, e.inv.comm₂₃_assoc]

/-- The obvious splitting of the short complex `X₁ ⟶ X₁ ⊞ X₂ ⟶ X₂`. -/
noncomputable def ofHasBinaryBiproduct (X₁ X₂ : C) [HasBinaryBiproduct X₁ X₂] :
    Splitting (ShortComplex.mk (biprod.inl : X₁ ⟶ _) (biprod.snd : _ ⟶ X₂) (by simp)) where
  r := biprod.fst
  s := biprod.inr

variable (S)

/-- The obvious splitting of a short complex when `S.X₁` is zero and `S.g` is an isomorphism. -/
noncomputable def ofIsZeroOfIsIso (hf : IsZero S.X₁) (hg : IsIso S.g) : Splitting S where
  r := 0
  s := inv S.g
  f_r := hf.eq_of_src _ _

/-- The obvious splitting of a short complex when `S.f` is an isomorphism and `S.X₃` is zero. -/
noncomputable def ofIsIsoOfIsZero (hf : IsIso S.f) (hg : IsZero S.X₃) : Splitting S where
  r := inv S.f
  s := 0
  s_g := hg.eq_of_src _ _

variable {S}

set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.op` deduced from a splitting of `S`. -/
@[simps]
def op (h : Splitting S) : Splitting S.op where
  r := h.s.op
  s := h.r.op
  f_r := Quiver.Hom.unop_inj (by simp)
  s_g := Quiver.Hom.unop_inj (by simp)
  id := Quiver.Hom.unop_inj (by
    simp only [op_X₂, Opposite.unop_op, op_X₁, op_f, op_X₃, op_g, unop_add, unop_comp,
      Quiver.Hom.unop_op, unop_id, ← h.id]
    abel)

set_option backward.isDefEq.respectTransparency false in
/-- The splitting of the short complex `S.unop` deduced from a splitting of `S`. -/
@[simps]
def unop {S : ShortComplex Cᵒᵖ} (h : Splitting S) : Splitting S.unop where
  r := h.s.unop
  s := h.r.unop
  f_r := Quiver.Hom.op_inj (by simp)
  s_g := Quiver.Hom.op_inj (by simp)
  id := Quiver.Hom.op_inj (by
    simp only [unop_X₂, Opposite.op_unop, unop_X₁, unop_f, unop_X₃, unop_g, op_add,
      op_comp, Quiver.Hom.op_unop, op_id, ← h.id]
    abel)

/-- The isomorphism `S.X₂ ≅ S.X₁ ⊞ S.X₃` induced by a splitting of the short complex `S`. -/
@[simps]
noncomputable def isoBinaryBiproduct (h : Splitting S) [HasBinaryBiproduct S.X₁ S.X₃] :
    S.X₂ ≅ S.X₁ ⊞ S.X₃ where
  hom := biprod.lift h.r S.g
  inv := biprod.desc S.f h.s
  hom_inv_id := by simp [h.id]

end Splitting

section Balanced

variable {S}
variable [Balanced C]

namespace Exact

lemma isIso_f' (hS : S.Exact) (h : S.LeftHomologyData) [Mono S.f] :
    IsIso h.f' := by
  have := hS.epi_f' h
  have := mono_of_mono_fac h.f'_i
  exact isIso_of_mono_of_epi h.f'

lemma isIso_toCycles (hS : S.Exact) [Mono S.f] [S.HasLeftHomology] :
    IsIso S.toCycles :=
  hS.isIso_f' _

lemma isIso_g' (hS : S.Exact) (h : S.RightHomologyData) [Epi S.g] :
    IsIso h.g' := by
  have := hS.mono_g' h
  have := epi_of_epi_fac h.p_g'
  exact isIso_of_mono_of_epi h.g'

lemma isIso_fromOpcycles (hS : S.Exact) [Epi S.g] [S.HasRightHomology] :
    IsIso S.fromOpcycles :=
  hS.isIso_g' _

/-- In a balanced category, if a short complex `S` is exact and `S.f` is a mono, then
`S.X₁` is the kernel of `S.g`. -/
noncomputable def fIsKernel (hS : S.Exact) [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Fork.ext (asIso S.toCycles).symm (by simp))

lemma map_of_mono_of_preservesKernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Mono S.f)
    (_ : PreservesLimit (parallelPair S.g 0) F) :
    (S.map F).Exact :=
  exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

set_option backward.isDefEq.respectTransparency false in
/-- In a balanced category, if a short complex `S` is exact and `S.g` is an epi, then
`S.X₃` is the cokernel of `S.g`. -/
noncomputable def gIsCokernel (hS : S.Exact) [Epi S.g] :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_fromOpcycles
  exact IsColimit.ofIsoColimit S.opcyclesIsCokernel
    (Cofork.ext (asIso S.fromOpcycles) (by simp))

lemma map_of_epi_of_preservesCokernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Epi S.g)
    (_ : PreservesColimit (parallelPair S.f 0) F) :
    (S.map F).Exact :=
  exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

/-- If a short complex `S` in a balanced category is exact and such that `S.f` is a mono,
then a morphism `k : A ⟶ S.X₂` such that `k ≫ S.g = 0` lifts to a morphism `A ⟶ S.X₁`. -/
noncomputable def lift (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    A ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma lift_f (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    hS.lift k hk ≫ S.f = k :=
  Fork.IsLimit.lift_ι _

lemma lift' (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    ∃ (l : A ⟶ S.X₁), l ≫ S.f = k :=
  ⟨hS.lift k hk, by simp⟩

/-- If a short complex `S` in a balanced category is exact and such that `S.g` is an epi,
then a morphism `k : S.X₂ ⟶ A` such that `S.f ≫ k = 0` descends to a morphism `S.X₃ ⟶ A`. -/
noncomputable def desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.X₃ ⟶ A := hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma g_desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.g ≫ hS.desc k hk = k :=
  Cofork.IsColimit.π_desc (hS.gIsCokernel)

lemma desc' (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    ∃ (l : S.X₃ ⟶ A), S.g ≫ l = k :=
  ⟨hS.desc k hk, by simp⟩

end Exact

lemma mono_τ₂_of_exact_of_mono {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) [Mono S₁.f] [Mono S₂.f] [Mono φ.τ₁] [Mono φ.τ₃] : Mono φ.τ₂ := by
  rw [mono_iff_cancel_zero]
  intro A x₂ hx₂
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S₁.f = x₂ := ⟨_, h₁.lift_f x₂
    (by simp only [← cancel_mono φ.τ₃, assoc, zero_comp, ← φ.comm₂₃, reassoc_of% hx₂])⟩
  suffices x₁ = 0 by rw [← hx₁, this, zero_comp]
  simp only [← cancel_mono φ.τ₁, ← cancel_mono S₂.f, assoc, φ.comm₁₂, zero_comp,
    reassoc_of% hx₁, hx₂]

attribute [local instance] balanced_opposite

lemma epi_τ₂_of_exact_of_epi {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [Epi φ.τ₃] : Epi φ.τ₂ := by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

variable (S)

lemma exact_and_mono_f_iff_f_is_kernel [S.HasHomology] :
    S.Exact ∧ Mono S.f ↔ Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_f_is_kernel hS, mono_of_isLimit_fork hS⟩

lemma exact_and_epi_g_iff_g_is_cokernel [S.HasHomology] :
    S.Exact ∧ Epi S.g ↔ Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) := by
  constructor
  · intro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨hS⟩
    exact ⟨S.exact_of_g_is_cokernel hS, epi_of_isColimit_cofork hS⟩

end Balanced

end Preadditive

section Abelian

variable [Abelian C]

section

variable {X Y : C} (f : X ⟶ Y)

/-- The exact short complex `kernel f ⟶ X ⟶ Y` for any morphism `f : X ⟶ Y`. -/
@[simps]
noncomputable def kernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (kernel.condition f)

/-- The exact short complex `X ⟶ Y ⟶ cokernel f` for any morphism `f : X ⟶ Y`. -/
@[simps]
noncomputable def cokernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (cokernel.condition f)

instance : Mono (kernelSequence f).f := by
  dsimp
  infer_instance

instance : Epi (cokernelSequence f).g := by
  dsimp
  infer_instance

lemma kernelSequence_exact : (kernelSequence f).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)

lemma cokernelSequence_exact : (cokernelSequence f).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

end

/-- Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁.f`
and `S₁.g` are zero (e.g. when `S₁` is of the form `0 ⟶ S₁.X₂ ⟶ 0`) and `S₂.f = 0`
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ S₂.X₃`), then `φ` is a quasi-isomorphism iff
the obvious short complex `S₁.X₂ ⟶ S₂.X₂ ⟶ S₂.X₃` is exact and `φ.τ₂` is a mono. -/
lemma quasiIso_iff_of_zeros {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk φ.τ₂ S₂.g (by rw [φ.comm₂₃, hg₁, zero_comp])).Exact ∧ Mono φ.τ₂ := by
  have w : φ.τ₂ ≫ S₂.g = 0 := by rw [φ.comm₂₃, hg₁, zero_comp]
  rw [quasiIso_iff_isIso_liftCycles φ hf₁ hg₁ hf₂]
  constructor
  · intro h
    have : Mono φ.τ₂ := by
      rw [← S₂.liftCycles_i φ.τ₂ w]
      apply mono_comp
    refine ⟨?_, this⟩
    apply exact_of_f_is_kernel
    exact IsLimit.ofIsoLimit S₂.cyclesIsKernel
      (Fork.ext (asIso (S₂.liftCycles φ.τ₂ w)).symm (by simp))
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁.lift S₂.iCycles (by simp), ?_, ?_⟩⟩
    · rw [← cancel_mono φ.τ₂, assoc, h₁.lift_f, liftCycles_i, id_comp]
    · rw [← cancel_mono S₂.iCycles, assoc, liftCycles_i, h₁.lift_f, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of short complexes `φ : S₁ ⟶ S₂` in an abelian category, if `S₁.g = 0`
(e.g when `S₁` is of the form `S₁.X₁ ⟶ S₁.X₂ ⟶ 0`) and both `S₂.f` and `S₂.g` are zero
(e.g when `S₂` is of the form `0 ⟶ S₂.X₂ ⟶ 0`), then `φ` is a quasi-isomorphism iff
the obvious short complex `S₁.X₁ ⟶ S₁.X₂ ⟶ S₂.X₂` is exact and `φ.τ₂` is an epi. -/
lemma quasiIso_iff_of_zeros' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    QuasiIso φ ↔
      (ShortComplex.mk S₁.f φ.τ₂ (by rw [← φ.comm₁₂, hf₂, comp_zero])).Exact ∧ Epi φ.τ₂ := by
  rw [← quasiIso_opMap_iff, quasiIso_iff_of_zeros]
  rotate_left
  · dsimp
    rw [hg₂, op_zero]
  · dsimp
    rw [hf₂, op_zero]
  · dsimp
    rw [hg₁, op_zero]
  rw [← exact_unop_iff]
  have : Mono φ.τ₂.op ↔ Epi φ.τ₂ :=
    ⟨fun _ => unop_epi_of_mono φ.τ₂.op, fun _ => op_mono_of_epi _⟩
  tauto

variable {S : ShortComplex C}

/-- If `S` is an exact short complex and `f : S.X₂ ⟶ J` is a morphism to an injective object `J`
such that `S.f ≫ f = 0`, this is a morphism `φ : S.X₃ ⟶ J` such that `S.g ≫ φ = f`. -/
noncomputable def Exact.descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.X₃ ⟶ J := by
  have := hS.mono_fromOpcycles
  exact Injective.factorThru (S.descOpcycles f hf) S.fromOpcycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma Exact.comp_descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Injective J] (hf : S.f ≫ f = 0) :
    S.g ≫ hS.descToInjective f hf = f := by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Injective.comp_factorThru, p_descOpcycles]

/-- If `S` is an exact short complex and `f : P ⟶ S.X₂` is a morphism from a projective object `P`
such that `f ≫ S.g = 0`, this is a morphism `φ : P ⟶ S.X₁` such that `φ ≫ S.f = f`. -/
noncomputable def Exact.liftFromProjective
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    P ⟶ S.X₁ := by
  have := hS.epi_toCycles
  exact Projective.factorThru (S.liftCycles f hf) S.toCycles

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma Exact.liftFromProjective_comp
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    hS.liftFromProjective f hf ≫ S.f = f := by
  dsimp [liftFromProjective]
  rw [← toCycles_i, Projective.factorThru_comp_assoc, liftCycles_i]


end Abelian

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [Preadditive C] [Preadditive D] [HasZeroObject C]
  [HasZeroObject D] [F.PreservesZeroMorphisms] [F.PreservesHomology]

set_option backward.isDefEq.respectTransparency false in
instance : F.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk (0 : X ⟶ X) f zero_comp
    exact ((S.map F).exact_iff_mono (by simp [S])).1
      (((S.exact_iff_mono rfl).2 hf).map F)


set_option backward.isDefEq.respectTransparency false in
instance : F.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk f (0 : Y ⟶ Y) comp_zero
    exact ((S.map F).exact_iff_epi (by simp [S])).1
      (((S.exact_iff_epi rfl).2 hf).map F)


end Functor

namespace ShortComplex

namespace Splitting

variable [Preadditive C] [Balanced C]

/-- This is the splitting of a short complex `S` in a balanced category induced by
a section of the morphism `S.g : S.X₂ ⟶ S.X₃` -/
noncomputable def ofExactOfSection (S : ShortComplex C) (hS : S.Exact) (s : S.X₃ ⟶ S.X₂)
    (s_g : s ≫ S.g = 𝟙 S.X₃) (hf : Mono S.f) :
    S.Splitting where
  r := hS.lift (𝟙 S.X₂ - S.g ≫ s) (by simp [s_g])
  s := s
  f_r := by rw [← cancel_mono S.f, assoc, Exact.lift_f, comp_sub, comp_id,
    zero_assoc, zero_comp, sub_zero, id_comp]
  s_g := s_g

/-- This is the splitting of a short complex `S` in a balanced category induced by
a retraction of the morphism `S.f : S.X₁ ⟶ S.X₂` -/
noncomputable def ofExactOfRetraction (S : ShortComplex C) (hS : S.Exact) (r : S.X₂ ⟶ S.X₁)
    (f_r : S.f ≫ r = 𝟙 S.X₁) (hg : Epi S.g) :
    S.Splitting where
  r := r
  s := hS.desc (𝟙 S.X₂ - r ≫ S.f) (by simp [reassoc_of% f_r])
  f_r := f_r
  s_g := by
    rw [← cancel_epi S.g, Exact.g_desc_assoc, sub_comp, id_comp, assoc, zero,
      comp_zero, sub_zero, comp_id]

end Splitting

end ShortComplex

end CategoryTheory
