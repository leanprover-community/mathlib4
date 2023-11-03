/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Homology

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

namespace CategoryTheory

open Category Limits ZeroObject

variable {C D : Type*} [Category C] [Category D]

namespace ShortComplex

section

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/-- The assertion that the short complex `S : ShortComplex C` is exact. -/
structure Exact : Prop where
  /-- the condition that there exists an homology data whose `left.H` field is zero -/
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

end

end ShortComplex

end CategoryTheory
