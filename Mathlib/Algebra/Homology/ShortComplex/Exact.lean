import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
--algebra.homology.short_complex.homology
--import algebra.homology.short_complex.abelian
--import algebra.homology.short_complex.preserves_homology
--import category_theory.preadditive.opposite

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type _} [Category C]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C]
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

lemma exact_iff_is_zero_right_homology [S.HasHomology] :
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

end

section Preadditive

variable [Preadditive C] (S : ShortComplex C)

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

end Splitting

end Preadditive

end ShortComplex

end CategoryTheory

#exit

variable {S}

lemma left_homology_data.exact_map_iff (h : S.left_homology_data) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h.is_preserved_by F] [(S.map F).has_homology]:
  (S.map F).exact ↔ is_zero (F.obj h.H) :=
(h.map F).exact_iff

lemma right_homology_data.exact_map_iff (h : S.right_homology_data) (F : C ⥤ D)
  [F.preserves_zero_morphisms] [h.is_preserved_by F] [(S.map F).has_homology]:
  (S.map F).exact ↔ is_zero (F.obj h.H) :=
(h.map F).exact_iff


lemma exact_map_of_preserves_homology (hS : S.exact)
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] : (S.map F).exact :=
begin
  haveI : S.has_homology := hS.has_homology,
  let h := S.some_homology_data,
  haveI := functor.preserves_left_homology_of.condition F S,
  haveI := functor.preserves_right_homology_of.condition F S,
  rw [h.exact_iff, is_zero.iff_id_eq_zero] at hS,
  simpa only [(h.map F).exact_iff, is_zero.iff_id_eq_zero,
    category_theory.functor.map_id, functor.map_zero] using F.congr_map hS,
end

variable (S)

lemma exact_map_iff_of_preserves_homology [S.has_homology]
  (F : C ⥤ D) [F.preserves_zero_morphisms] [F.preserves_left_homology_of S]
  [F.preserves_right_homology_of S] [faithful F] :
  (S.map F).exact ↔ S.exact :=
begin
  let h := S.some_homology_data,
  have e : F.map (𝟙 h.left.H) = 0 ↔ (𝟙 h.left.H) = 0,
  { split,
    { intro eq,
      apply F.map_injective,
      rw [eq, F.map_zero], },
    { intro eq,
      rw [eq, F.map_zero], }, },
  haveI := functor.preserves_left_homology_of.condition F S,
  haveI := functor.preserves_right_homology_of.condition F S,
  simpa only [h.exact_iff, is_zero.iff_id_eq_zero, (h.map F).exact_iff,
    F.map_id] using e,
end


variable {S}

lemma exact.comp_eq_zero (h : S.exact) {X Y : C} {ι : X ⟶ S.X₂} (hι : ι ≫ S.g = 0)
  {π : S.X₂ ⟶ Y} (hπ : S.f ≫ π = 0) : ι ≫ π = 0 :=
begin
  haveI : S.has_homology := h.has_homology,
  rw exact_iff_cycles_i_p_cycles_co_zero at h,
  rw [← S.lift_cycles_i ι hι, ← S.p_desc_cycles_co π hπ, assoc,
    reassoc_of h, zero_comp, comp_zero],
end

end

section preadditive

variables [preadditive C] {S₁ S₂ : short_complex C}

lemma homotopy_equiv.exact_iff (e : homotopy_equiv S₁ S₂) [S₁.has_homology] [S₂.has_homology] :
  S₁.exact ↔ S₂.exact :=
begin
  simp only [exact_iff_is_zero_homology],
  exact ⟨λ h, is_zero.of_iso h e.homology_iso.symm, λ h, is_zero.of_iso h e.homology_iso⟩,
end

end preadditive

end short_complex

end category_theory
