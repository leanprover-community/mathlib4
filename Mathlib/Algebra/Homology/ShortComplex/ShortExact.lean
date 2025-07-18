/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Short exact short complexes

A short complex `S : ShortComplex C` is short exact (`S.ShortExact`) when it is exact,
`S.f` is a mono and `S.g` is an epi.

-/

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type*} [Category C] [Category D]

namespace ShortComplex

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- A short complex `S` is short exact if it is exact, `S.f` is a mono and `S.g` is an epi. -/
structure ShortExact : Prop where
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]

variable {S}

lemma ShortExact.mk' (h : S.Exact) (_ : Mono S.f) (_ : Epi S.g) : S.ShortExact where
  exact := h

lemma shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where
  exact := exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    apply mono_comp
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.comm₂₃]
    apply epi_comp

lemma shortExact_iff_of_iso (e : S₁ ≅ S₂) : S₁.ShortExact ↔ S₂.ShortExact := by
  constructor
  · exact shortExact_of_iso e
  · exact shortExact_of_iso e.symm

lemma ShortExact.op (h : S.ShortExact) : S.op.ShortExact where
  exact := h.exact.op
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

lemma ShortExact.unop {S : ShortComplex Cᵒᵖ} (h : S.ShortExact) : S.unop.ShortExact where
  exact := h.exact.unop
  mono_f := by
    have := h.epi_g
    dsimp
    infer_instance
  epi_g := by
    have := h.mono_f
    dsimp
    infer_instance

variable (S)

lemma shortExact_iff_op : S.ShortExact ↔ S.op.ShortExact :=
  ⟨ShortExact.op, ShortExact.unop⟩

lemma shortExact_iff_unop (S : ShortComplex Cᵒᵖ) : S.ShortExact ↔ S.unop.ShortExact :=
  S.unop.shortExact_iff_op.symm

variable {S}

lemma ShortExact.map (h : S.ShortExact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [Mono (F.map S.f)] [Epi (F.map S.g)] :
    (S.map F).ShortExact where
  exact := h.exact.map F
  mono_f := (inferInstance : Mono (F.map S.f))
  epi_g := (inferInstance : Epi (F.map S.g))

lemma ShortExact.map_of_exact (hS : S.ShortExact)
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (S.map F).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have := preserves_mono_of_preservesLimit F S.f
  have := preserves_epi_of_preservesColimit F S.g
  exact hS.map F

end

section Preadditive

variable [Preadditive C]

lemma ShortExact.isIso_f_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.f ↔ IsZero S.X₃ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

lemma ShortExact.isIso_g_iff {S : ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.g ↔ IsZero S.X₁ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

lemma isIso₂_of_shortExact_of_isIso₁₃ [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₃] : IsIso φ.τ₂ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

lemma isIso₂_of_shortExact_of_isIso₁₃' [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (_ : IsIso φ.τ₁) (_ : IsIso φ.τ₃) : IsIso φ.τ₂ :=
  isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂

/-- If `S` is a short exact short complex in a balanced category,
then `S.X₁` is the kernel of `S.g`. -/
noncomputable def ShortExact.fIsKernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  have := hS.mono_f
  exact hS.exact.fIsKernel

/-- If `S` is a short exact short complex in a balanced category,
then `S.X₃` is the cokernel of `S.f`. -/
noncomputable def ShortExact.gIsCokernel [Balanced C] {S : ShortComplex C} (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  have := hS.epi_g
  exact hS.exact.gIsCokernel

/-- Is `S` is an exact short complex and `h : S.HomologyData`, there is
a short exact sequence `0 ⟶ h.left.K ⟶ S.X₂ ⟶ h.right.Q ⟶ 0`. -/
lemma Exact.shortExact {S : ShortComplex C} (hS : S.Exact) (h : S.HomologyData) :
    (ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)).ShortExact where
  exact := by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := h.right.g' }
    rwa [ShortComplex.exact_iff_of_epi_of_isIso_of_mono b,
      ← ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]

/-- A split short complex is short exact. -/
lemma Splitting.shortExact {S : ShortComplex C} [HasZeroObject C] (s : S.Splitting) :
    S.ShortExact where
  exact := s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

namespace ShortExact

/-- A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₁` is injective. -/
noncomputable def splittingOfInjective {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₁] [Balanced C] :
    S.Splitting :=
  have := hS.mono_f
  Splitting.ofExactOfRetraction S hS.exact (Injective.factorThru (𝟙 S.X₁) S.f) (by simp) hS.epi_g

/-- A choice of splitting for a short exact short complex `S` in a balanced category
such that `S.X₃` is projective. -/
noncomputable def splittingOfProjective {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₃] [Balanced C] :
    S.Splitting :=
  have := hS.epi_g
  Splitting.ofExactOfSection S hS.exact (Projective.factorThru (𝟙 S.X₃) S.g) (by simp) hS.mono_f

end ShortExact

end Preadditive

end ShortComplex

end CategoryTheory
