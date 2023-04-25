import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
--algebra.homology.short_complex.homology
--import algebra.homology.short_complex.abelian
--import algebra.homology.short_complex.preserves_homology
--import category_theory.preadditive.opposite

namespace CategoryTheory

open Category Limits ZeroObject

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

section preadditive

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

end preadditive

#exit



end ShortComplex

end CategoryTheory

#exit

variable (S)



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

variable (S : short_complex C)

structure splitting (S : short_complex C) :=
(r : S.X₂ ⟶ S.X₁)
(s : S.X₃ ⟶ S.X₂)
(f_r : S.f ≫ r = 𝟙 _)
(s_g : s ≫ S.g = 𝟙 _)
(id : r ≫ S.f + S.g ≫ s = 𝟙 _)

namespace splitting

attribute [reassoc] f_r s_g

variable {S}

@[simps] def split_mono_f (s : S.splitting) : split_mono S.f := ⟨s.r, s.f_r⟩
lemma is_split_mono_f (s : S.splitting) : is_split_mono S.f := ⟨⟨s.split_mono_f⟩⟩
lemma mono_f (s : S.splitting) : mono S.f := by { haveI := s.is_split_mono_f, apply_instance, }

@[simps] def split_epi_g (s : S.splitting) : split_epi S.g := ⟨s.s, s.s_g⟩
lemma is_split_epi_g (s : S.splitting) : is_split_epi S.g := ⟨⟨s.split_epi_g⟩⟩
lemma epi_g (s : S.splitting) : epi S.g := by { haveI := s.is_split_epi_g, apply_instance, }

lemma ext_r (s s' : S.splitting) (h : s.r = s'.r) : s = s' :=
begin
  haveI := s.epi_g,
  have eq : 𝟙 S.X₂ = 𝟙 S.X₂ := rfl,
  nth_rewrite 0 ← s.id at eq,
  rw [← s'.id, h, add_right_inj, cancel_epi S.g] at eq,
  cases s,
  cases s',
  tidy,
end

lemma ext_s (s s' : S.splitting) (h : s.s = s'.s) : s = s' :=
begin
  haveI := s.mono_f,
  have eq : 𝟙 S.X₂ = 𝟙 S.X₂ := rfl,
  nth_rewrite 0 ← s.id at eq,
  rw [← s'.id, h, add_left_inj, cancel_mono S.f] at eq,
  cases s,
  cases s',
  tidy,
end

@[simp]
def left_homology_data [has_zero_object C] (s : S.splitting) :
  left_homology_data S :=
begin
  have hi := kernel_fork.is_limit.of_ι S.f S.zero (λ A x hx, x ≫ s.r)
    (λ A x hx, by { conv_rhs { rw [← comp_id x, ← s.id, comp_add, reassoc_of hx,
      zero_comp, add_zero, ← assoc], }, })
    (λ A x hx b hb, by { dsimp, rw [← hb, assoc, s.f_r, comp_id], }),
  let f' := hi.lift (kernel_fork.of_ι S.f S.zero),
  have hf' : f' = 𝟙 _,
  { apply fork.is_limit.hom_ext hi,
    simp only [fork.is_limit.lift_ι, id_comp], },
  have hπ₀ : f' ≫ (0 : _ ⟶ 0) = 0 := comp_zero,
  have hπ := cokernel_cofork.is_colimit.of_π 0 hπ₀
    (λ A x hx, 0)
    (λ A x hx, begin
      dsimp,
      rw [hf', id_comp] at hx,
      rw [hx, comp_zero],
    end)
    (λ A x hx b hb, is_zero.eq_of_src (is_zero_zero _) _ _),
  exact ⟨S.X₁, 0, S.f, 0, S.zero, hi, hπ₀, hπ⟩,
end

@[simp]
def right_homology_data [has_zero_object C] (s : S.splitting) :
  right_homology_data S :=
begin
  have hp := cokernel_cofork.is_colimit.of_π S.g S.zero (λ A x hx, s.s ≫ x)
    (λ A x hx, by { dsimp, conv_rhs { rw [← id_comp x, ← s.id, add_comp, assoc,
      hx, comp_zero, zero_add, assoc], }, })
  (λ A x hx b hb, by { dsimp, rw [← hb, s.s_g_assoc], }),
  let g' := hp.desc (cokernel_cofork.of_π S.g S.zero),
  have hg' : g' = 𝟙 _,
  { apply cofork.is_colimit.hom_ext hp,
    simp only [cofork.is_colimit.π_desc],
    erw comp_id, },
  have hι₀ : (0 : 0 ⟶ _) ≫ g' = 0 := zero_comp,
  have hι := kernel_fork.is_limit.of_ι 0 hι₀
    (λ A x hx, 0)
    (λ A x hx, begin
      dsimp,
      rw [hg', comp_id] at hx,
      rw [hx, zero_comp],
    end)
    (λ A x hx b hb, is_zero.eq_of_tgt (is_zero_zero _) _ _),
  exact ⟨S.X₃, 0, S.g, 0, S.zero, hp, hι₀, hι⟩,
end

@[simps]
def homology_data [has_zero_object C] (s : S.splitting) :
  homology_data S :=
{ left := s.left_homology_data,
  right := s.right_homology_data,
  iso := iso.refl 0,
  comm := by tidy, }

lemma exact [has_zero_object C] (s : S.splitting) : S.exact :=
⟨s.homology_data, is_zero_zero _⟩

end splitting

variable {S}

variable (S)


end preadditive

end short_complex

end category_theory
