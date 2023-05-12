import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Balanced

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type _} [Category C] [Category D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

structure Exact : Prop :=
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

variable {S}

lemma Exact.hasHomology (h : S.Exact) : S.HasHomology :=
  HasHomology.mk' h.condition.choose

variable (S)

lemma exact_iff_isZero_homology [S.HasHomology] :
    S.Exact ↔ IsZero S.homology := by
  constructor
  . rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  . intro h
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

lemma exact_iff_isZero_right_homology [S.HasHomology] :
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
  . intro h
    exact ⟨h.isoZero⟩
  . rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

lemma exact_of_iso (e : S₁ ≅ S₂) (h : S₁.Exact) : S₂.Exact := by
  obtain ⟨⟨h, z⟩⟩ := h
  exact ⟨⟨HomologyData.ofIso e h, z⟩⟩

lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

lemma exact_of_isZero_X₂ (h : IsZero S.X₂) : S.Exact := by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

lemma exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    S₁.Exact ↔ S₂.Exact := by
  constructor
  . rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  . rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

variable {S}

lemma HomologyData.exact_iff_i_p_zero (h : S.HomologyData) :
    S.Exact ↔ h.left.i ≫ h.right.p = 0 := by
  haveI := HasHomology.mk' h
  rw [h.left.exact_iff, ← h.comm]
  constructor
  . intro z
    rw [IsZero.eq_of_src z h.iso.hom 0, zero_comp, comp_zero]
  . intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

variable (S)

lemma exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 :=
  (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

lemma exact_iff_iCycles_pCyclesCo_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pCyclesCo = 0 :=
  S.exact_iff_i_p_zero _ _

lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  haveI : HasCokernel _ := HasLeftHomology.hasCokernel S
  haveI : HasKernel _ := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofKerOfCoker S)
    (RightHomologyData.ofKerOfCoker S)

variable {S}

lemma Exact.op (h : S.Exact) : S.op.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.op, (IsZero.of_iso z h.iso.symm).op⟩⟩

lemma Exact.unop {S : ShortComplex Cᵒᵖ} (h : S.Exact) : S.unop.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

variable (S)

lemma exact_iff_op : S.Exact ↔ S.op.Exact :=
  ⟨Exact.op, Exact.unop⟩

lemma exact_iff_unop (S : ShortComplex Cᵒᵖ) : S.Exact ↔ S.unop.Exact :=
  S.unop.exact_iff_op.symm

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
    rw [(S.leftHomologyData).exact_iff, IsZero.iff_id_eq_zero] at h
    rw [(S.leftHomologyData).exact_map_iff F, IsZero.iff_id_eq_zero,
      ← F.map_id, h, F.map_zero]

lemma Exact.map_of_preservesRightHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesRightHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
    have : S.HasHomology := h.hasHomology
    rw [(S.rightHomologyData).exact_iff, IsZero.iff_id_eq_zero] at h
    rw [(S.rightHomologyData).exact_map_iff F, IsZero.iff_id_eq_zero,
      ← F.map_id, h, F.map_zero]

lemma Exact.map (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] : (S.map F).Exact := by
    have := h.hasHomology
    exact h.map_of_preservesLeftHomologyOf F

variable (S)

lemma exact_map_iff_of_faithful [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [Faithful F] :
    (S.map F).Exact ↔ S.Exact := by
    constructor
    . intro h
      rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
      rw [(S.leftHomologyData.map F).exact_iff, IsZero.iff_id_eq_zero,
        LeftHomologyData.map_H] at h
      apply F.map_injective
      rw [F.map_id, F.map_zero, h]
    . intro h
      exact h.map F


variable {S}

lemma Exact.comp_eq_zero (h : S.Exact) {X Y : C} {a : X ⟶ S.X₂} (ha : a ≫ S.g = 0)
  {b : S.X₂ ⟶ Y} (hb : S.f ≫ b = 0) : a ≫ b = 0 := by
    have := h.hasHomology
    have eq := h
    rw [exact_iff_iCycles_pCyclesCo_zero] at eq
    rw [← S.liftCycles_i a ha, ← S.p_descCyclesCo b hb, assoc, reassoc_of% eq,
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
  . intro h
    have : S.HasHomology := HasHomology.mk' h.condition.choose
    simp only [exact_iff_isZero_homology] at h
    have := S.isIso_pCyclesCo_of_zero hf
    have := mono_of_isZero_kernel' _ S.homologyIsKernel h
    rw [← S.p_fromCyclesCo]
    apply mono_comp
  . intro
    rw [(HomologyData.ofIsLimitKernelFork S hf _
      (KernelFork.IsLimit.ofIsZeroOfMono (KernelFork.ofι (0 : 0 ⟶ S.X₂) zero_comp)
        inferInstance (isZero_zero C))).exact_iff]
    exact isZero_zero C

lemma exact_iff_epi [HasZeroObject C] (hg : S.g = 0) :
    S.Exact ↔ Epi S.f := by
  constructor
  . intro h
    haveI : S.HasHomology := HasHomology.mk' h.condition.choose
    simp only [exact_iff_isZero_homology] at h
    haveI := S.isIso_iCycles_of_zero hg
    haveI : Epi S.toCycles := epi_of_isZero_cokernel' _ S.homologyIsCokernel h
    rw [← S.toCycles_i]
    apply epi_comp
  . intro
    rw [(HomologyData.ofIsColimitCokernelCofork S hg _
      (CokernelCofork.IsColimit.ofIsZeroOfEpi (CokernelCofork.ofπ (0 : S.X₂ ⟶ 0) comp_zero)
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

lemma Exact.mono_fromCyclesCo (hS : S.Exact) [S.HasRightHomology] : Mono S.fromCyclesCo :=
  hS.mono_g' _

lemma LeftHomologyData.exact_iff_epi_f' [S.HasHomology] (h : LeftHomologyData S) :
    S.Exact ↔ Epi h.f' := by
  constructor
  . intro hS
    exact hS.epi_f' h
  . intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

lemma RightHomologyData.exact_iff_mono_g' [S.HasHomology] (h : RightHomologyData S) :
    S.Exact ↔ Mono h.g' := by
  constructor
  . intro hS
    exact hS.mono_g' h
  . intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_mono h.ι, ← cancel_mono h.g',
      id_comp, h.ι_g', zero_comp]

variable (S)

lemma exact_iff_epi_toCycles [S.HasHomology] : S.Exact ↔ Epi S.toCycles :=
  S.leftHomologyData.exact_iff_epi_f'

lemma exact_iff_mono_fromCyclesCo [S.HasHomology] : S.Exact ↔ Mono S.fromCyclesCo :=
  S.rightHomologyData.exact_iff_mono_g'

lemma exact_iff_epi_kernel_lift [S.HasHomology] [HasKernel S.g] :
    S.Exact ↔ Epi (kernel.lift S.g S.f S.zero) := by
  rw [exact_iff_epi_toCycles]
  have eq₁ : kernel.lift S.g S.f S.zero = S.toCycles ≫ S.cyclesIsoKernel.hom := by
    simp only [cyclesIsoKernel_hom, ← cancel_mono (kernel.ι S.g), kernel.lift_ι,
      assoc, toCycles_i]
  have eq₂ : S.toCycles = kernel.lift S.g S.f S.zero ≫ S.cyclesIsoKernel.inv := by
    rw [eq₁, assoc, Iso.hom_inv_id, comp_id]
  constructor
  . intro
    rw [eq₁]
    apply epi_comp
  . intro
    rw [eq₂]
    apply epi_comp

lemma exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero) := by
  rw [exact_iff_mono_fromCyclesCo]
  have eq₁ : cokernel.desc S.f S.g S.zero = S.cyclesCoIsoCokernel.inv ≫ S.fromCyclesCo := by
    simp only [← cancel_epi (cokernel.π S.f), cokernel.π_desc, cyclesCoIsoCokernel_inv,
      cokernel.π_desc_assoc, p_fromCyclesCo]
  have eq₂ : S.fromCyclesCo = S.cyclesCoIsoCokernel.hom ≫ cokernel.desc S.f S.g S.zero := by
    rw [eq₁, Iso.hom_inv_id_assoc]
  constructor
  . intro
    rw [eq₁]
    apply mono_comp
  . intro
    rw [eq₂]
    apply mono_comp

lemma QuasiIso.exact_iff {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [QuasiIso φ] : S₁.Exact ↔ S₂.Exact := by
  simp only [exact_iff_isZero_homology]
  exact Iso.isZero_iff (QuasiIso.iso φ)

lemma HomotopyEquiv.exact_iff {S₁ S₂ : ShortComplex C} (e : HomotopyEquiv S₁ S₂)
    [S₁.HasHomology] [S₂.HasHomology] : S₁.Exact ↔ S₂.Exact :=
  QuasiIso.exact_iff e.hom

lemma exact_of_f_is_kernel (hS : IsLimit (KernelFork.ofι S.f S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_epi_toCycles]
  have : IsSplitEpi S.toCycles :=
    ⟨⟨{ section_ := hS.lift (KernelFork.ofι S.iCycles S.iCycles_g)
        id := by
          rw [← cancel_mono S.iCycles]
          simp only [assoc, toCycles_i, id_comp]
          exact Fork.IsLimit.lift_ι hS }⟩⟩
  infer_instance

lemma exact_of_g_is_cokernel (hS : IsColimit (CokernelCofork.ofπ S.g S.zero))
    [S.HasHomology] : S.Exact := by
  rw [exact_iff_mono_fromCyclesCo]
  have : IsSplitMono S.fromCyclesCo :=
    ⟨⟨{ retraction := hS.desc (CokernelCofork.ofπ S.pCyclesCo S.f_pCyclesCo)
        id := by
          rw [← cancel_epi S.pCyclesCo]
          simp only [assoc, p_fromCyclesCo_assoc, comp_id]
          exact Cofork.IsColimit.π_desc hS }⟩⟩
  infer_instance

structure Splitting (S : ShortComplex C) where
  r : S.X₂ ⟶ S.X₁
  s : S.X₃ ⟶ S.X₂
  f_r : S.f ≫ r = 𝟙 _ := by aesop_cat
  s_g : s ≫ S.g = 𝟙 _ := by aesop_cat
  id : r ≫ S.f + S.g ≫ s = 𝟙 _ := by aesop_cat

namespace Splitting

attribute [reassoc (attr := simp)] f_r s_g

variable {S}

@[reassoc]
lemma r_f (s : S.Splitting) : s.r ≫ S.f = 𝟙 _ - S.g ≫ s.s := by rw [← s.id, add_sub_cancel]

@[reassoc]
lemma g_s (s : S.Splitting) : S.g ≫ s.s = 𝟙 _ - s.r ≫ S.f := by rw [← s.id, add_sub_cancel']

@[simps] def splitMono_f (s : S.Splitting) : SplitMono S.f := ⟨s.r, s.f_r⟩
lemma isSplitMono_f (s : S.Splitting) : IsSplitMono S.f := ⟨⟨s.splitMono_f⟩⟩
lemma mono_f (s : S.Splitting) : Mono S.f := by
  have := s.isSplitMono_f
  infer_instance

@[simps] def splitEpi_g (s : S.Splitting) : SplitEpi S.g := ⟨s.s, s.s_g⟩
lemma isSplitEpi_g (s : S.Splitting) : IsSplitEpi S.g := ⟨⟨s.splitEpi_g⟩⟩
lemma epi_g (s : S.Splitting) : Epi S.g := by
  have := s.isSplitEpi_g
  infer_instance

lemma ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s' := by
  have := s.epi_g
  have eq : 𝟙 S.X₂ = 𝟙 S.X₂ := rfl
  nth_rw 1 [← s.id] at eq
  rw [← s'.id, h, add_right_inj, cancel_epi S.g] at eq
  cases s
  cases s'
  obtain rfl := eq
  obtain rfl := h
  rfl

lemma ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s' := by
  have := s.mono_f
  have eq : 𝟙 S.X₂ = 𝟙 S.X₂ := rfl
  nth_rw 1 [← s.id] at eq
  rw [← s'.id, h, add_left_inj, cancel_mono S.f] at eq
  cases s
  cases s'
  obtain rfl := eq
  obtain rfl := h
  rfl

@[simp]
noncomputable def leftHomologyData [HasZeroObject C] (s : S.Splitting) :
    LeftHomologyData S := by
  have hi := KernelFork.IsLimit.ofι S.f S.zero
    (fun x _ => x ≫ s.r)
    (fun x hx => by simp only [assoc, s.r_f, comp_sub, comp_id,
      sub_eq_self, reassoc_of% hx, zero_comp])
    (fun x _ b hb => by simp only [← hb, assoc, f_r, comp_id])
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 _ := by
    apply Fork.IsLimit.hom_ext hi
    dsimp
    erw [Fork.IsLimit.lift_ι hi]
    simp only [Fork.ι_ofι, id_comp]
  have wπ : f' ≫ (0 : S.X₁ ⟶ 0) = 0 := comp_zero
  have hπ : IsColimit (CokernelCofork.ofπ 0 wπ) := CokernelCofork.IsColimit.ofIsZeroOfEpi _
      (by rw [hf'] ; infer_instance) (isZero_zero _)
  exact
  { K := S.X₁
    H := 0
    i := S.f
    wi := S.zero
    hi := hi
    π := 0
    wπ := wπ
    hπ := hπ }

@[simp]
noncomputable def rightHomologyData [HasZeroObject C] (s : S.Splitting) :
    RightHomologyData S := by
  have hp := CokernelCofork.IsColimit.ofπ S.g S.zero
    (fun x _ => s.s ≫ x)
    (fun x hx => by simp only [s.g_s_assoc, sub_comp, id_comp, sub_eq_self, assoc, hx, comp_zero])
    (fun x _ b hb => by simp only [← hb, s.s_g_assoc])
  let g' := hp.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 _ := by
    apply Cofork.IsColimit.hom_ext hp
    dsimp
    erw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, comp_id]
  have wι : (0 : 0 ⟶ S.X₃) ≫ g' = 0 := zero_comp
  have hι : IsLimit (KernelFork.ofι 0 wι) := KernelFork.IsLimit.ofIsZeroOfMono _
      (by rw [hg'] ; dsimp ; infer_instance) (isZero_zero _)
  exact
  { Q := S.X₃
    H := 0
    p := S.g
    wp := S.zero
    hp := hp
    ι := 0
    wι := wι
    hι := hι }

@[simps]
noncomputable def homologyData [HasZeroObject C] (s : S.Splitting) : S.HomologyData where
  left := s.leftHomologyData
  right := s.rightHomologyData
  iso := Iso.refl 0

lemma exact [HasZeroObject C] (s : S.Splitting) : S.Exact :=
  ⟨s.homologyData, isZero_zero _⟩

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

end Splitting

section Balanced

variable {S}
variable [Balanced C]

namespace Exact

variable (hS : S.Exact)

lemma isIso_f' (h : S.LeftHomologyData) [Mono S.f] :
    IsIso h.f' := by
    have := hS.epi_f' h
    have := mono_of_mono_fac h.f'_i
    exact isIso_of_mono_of_epi h.f'

lemma isIso_toCycles [Mono S.f] [S.HasLeftHomology] :
    IsIso S.toCycles := by
    exact hS.isIso_f' _

lemma isIso_g' (h : S.RightHomologyData) [Epi S.g] :
    IsIso h.g' := by
    have := hS.mono_g' h
    have := epi_of_epi_fac h.p_g'
    exact isIso_of_mono_of_epi h.g'

lemma isIso_fromCyclesCo [Epi S.g] [S.HasRightHomology] :
    IsIso S.fromCyclesCo := by
    exact hS.isIso_g' _

noncomputable def fIsKernel [Mono S.f] : IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_toCycles
  exact IsLimit.ofIsoLimit S.cyclesIsKernel
    (Iso.symm (Fork.ext (asIso S.toCycles) (by simp)))

noncomputable def gIsCokernel [Epi S.g] : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.hasHomology
  have := hS.isIso_fromCyclesCo
  exact IsColimit.ofIsoColimit S.cyclesCoIsCokernel
    ((Cofork.ext (asIso S.fromCyclesCo) (by simp)))

noncomputable def lift {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    A ⟶ S.X₁ := hS.fIsKernel.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
lemma lift_f {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    hS.lift k hk ≫ S.f = k :=
  Fork.IsLimit.lift_ι _

noncomputable def desc {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.X₃ ⟶ A := hS.gIsCokernel.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma g_desc {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.g ≫ hS.desc k hk = k :=
  Cofork.IsColimit.π_desc (hS.gIsCokernel)

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

lemma mono_τ₂_of_exact_of_mono' {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.Exact) (hf₁ : Mono S₁.f) (hf₂ : Mono S₂.f) (hτ₁ : Mono φ.τ₁) (hτ₂ : Mono φ.τ₃) :
    Mono φ.τ₂ := by
  apply mono_τ₂_of_exact_of_mono φ h₁

attribute [local instance] balanced_opposite

lemma epi_τ₂_of_exact_of_epi {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [Epi φ.τ₃] : Epi φ.τ₂ := by
  have := mono_τ₂_of_exact_of_mono' (opMap φ) h₂.op (op_mono_of_epi S₂.g)
    (op_mono_of_epi S₁.g) (op_mono_of_epi φ.τ₃) (op_mono_of_epi φ.τ₁)
  exact unop_epi_of_mono (opMap φ).τ₂

end Balanced

end Preadditive

end ShortComplex

end CategoryTheory
