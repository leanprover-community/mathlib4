import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type _} [Category C] [Category D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

structure ShortExact : Prop :=
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]

attribute [local instance] mono_comp epi_comp

variable {S}

lemma ShortExact.mk' (h : S.Exact) (hf : Mono S.f) (hg : Epi S.g) : S.ShortExact where
  exact := h
  mono_f := hf
  epi_g := hg

lemma shortExact_of_iso (e : S₁ ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where
  exact := exact_of_iso e h.exact
  mono_f := by
    suffices Mono (S₂.f ≫ e.inv.τ₂) by
      exact mono_of_mono _ e.inv.τ₂
    have := h.mono_f
    rw [← e.inv.comm₁₂]
    infer_instance
  epi_g := by
    suffices Epi (e.hom.τ₂ ≫ S₂.g) by
      exact epi_of_epi e.hom.τ₂ _
    have := h.epi_g
    rw [e.hom.comm₂₃]
    infer_instance

lemma shortExact_iff_of_iso (e : S₁ ≅ S₂) : S₁.ShortExact ↔ S₂.ShortExact := by
  constructor
  . exact shortExact_of_iso e
  . exact shortExact_of_iso e.symm

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

lemma isIso₂_of_shortExact_of_isIso₁₃ [Balanced C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₃] : IsIso φ.τ₂ := by
  have := h₁.mono_f
  have := h₂.mono_f
  have := h₁.epi_g
  have := h₂.epi_g
  have := mono_τ₂_of_exact_of_mono φ h₁.exact
  have := epi_τ₂_of_exact_of_epi φ h₂.exact
  apply isIso_of_mono_of_epi

end Preadditive

end ShortComplex

end CategoryTheory
