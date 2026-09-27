/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! # Boundedness of seminorms -/

@[expose] public noncomputable section

open NNReal

variable {ι 𝕜 E : Type*}

namespace Seminorm

section IsBoundedBy

section SMul

variable [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]

/-- A seminorm `p` is bounded by another seminorm `q` if there exists `C : ℝ≥0` such that
`p ≤ C • q`. -/
def IsBoundedBy (p q : Seminorm 𝕜 E) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q

variable {p p' q q' : Seminorm 𝕜 E}

variable (p q) in
theorem isBoundedBy_iff : p.IsBoundedBy q ↔ ∃ (C : ℝ≥0), p ≤ C • q := by rfl

variable (p q) in
/-- A seminorm `p` is bounded by another seminorm `q` if and only if there exists `C : ℝ` such that
for all `x`, `p x ≤ C * q x`. -/
@[grind =]
theorem isBoundedBy_iff_exists_real : p.IsBoundedBy q ↔ ∃ C, ∀ x, p x ≤ C * q x := by
  rw [isBoundedBy_iff]
  constructor
  · intro ⟨C, h⟩
    use C
    intro x
    rw [Seminorm.le_def] at h
    grw [h x]
    norm_cast
  · intro ⟨C, h⟩
    use C.toNNReal
    rw [Seminorm.le_def]
    intro x
    grw [h x]
    suffices C • q x ≤ (C.toNNReal : ℝ) • q x by simpa using! this
    gcongr
    simp

variable (p) in
@[grind .]
theorem isBoundedBy_self : p.IsBoundedBy p := by
  use 1
  simp

@[grind →, trans]
theorem IsBoundedBy.trans (h : p.IsBoundedBy q) (h' : q.IsBoundedBy q') :
    p.IsBoundedBy q' := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use C * C'
  grw [h, h']
  simp [← smul_assoc]

variable {R : Type*} [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]
  [Preorder R] [Zero R] [IsOrderedModule R ℝ]

@[grind .]
theorem IsBoundedBy.smul_left (h : p.IsBoundedBy q) (a : R) : (a • p).IsBoundedBy q := by
  obtain ⟨C, h⟩ := h
  use a • C
  grw [h, smul_assoc]

@[grind ←]
theorem IsBoundedBy.smul_right (h : p.IsBoundedBy q) {a : ℝ≥0} (ha : a ≠ 0) :
    p.IsBoundedBy (a • q) := by
  obtain ⟨C, h⟩ := h
  use a⁻¹ • C
  calc
    _ ≤ C • q := h
    _ = _ := by
      rw [← smul_assoc]
      congr
      simp [field]

@[grind .]
theorem IsBoundedBy.add (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q') :
    (p + p').IsBoundedBy (q + q') := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use max C C'
  calc
    _ ≤ C • q + C' • q' := by grw [h, h']
    _ ≤ max C C' • q + max C C' • q' := by
      gcongr
      all_goals simp
    _ = _ := by simp

instance : IsStrictOrderedModule ℕ ℝ where

@[grind .]
theorem IsBoundedBy.add_left (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q) :
    (p + p').IsBoundedBy q := by
  have h₁ : (p + p').IsBoundedBy (q + q) := h.add h'
  have h₂ : (2 • q).IsBoundedBy q := by grind
  grind [two_nsmul]

end SMul

section Module

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem isBoundedBy_congr_sup {p q : ι → Seminorm 𝕜 E} {s : Finset ι}
    (h : ∀ i ∈ s, (p i).IsBoundedBy (q i)) :
    (s.sup p).IsBoundedBy (s.sup q) := by
  choose C hC using h
  classical
  use s.sup (fun i ↦ if h : i ∈ s then C i h else 0)
  simp only [Finset.sup_le_iff]
  intro i hi
  grw [hC i hi]
  gcongr
  · exact Finset.le_sup_dite_pos _ hi hi
  · exact Finset.le_sup hi

@[grind .]
theorem isBoundedBy_sup_mono {p : ι → Seminorm 𝕜 E} {s s' : Finset ι}
    (h : s ⊆ s') :
    (s.sup p).IsBoundedBy (s'.sup p) := by
  use 1
  grind [one_smul, Finset.sup_le_iff, Finset.le_sup]

end Module

end IsBoundedBy

section IsEquivalent

variable [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]

/-- Two seminorms `p, q` are equivalent if `p` is bounded by `q` and `q` is bounded by `p`. -/
def IsEquivalent (p q : Seminorm 𝕜 E) : Prop :=
  ∃ (C : ℝ≥0), p ≤ C • q ∧ q ≤ C • p

variable {p p' q q' : Seminorm 𝕜 E}

@[symm]
theorem IsEquivalent.symm (h : p.IsEquivalent q) : q.IsEquivalent p := by
  obtain ⟨C, h⟩ := h
  exact ⟨C, h.symm⟩

@[trans]
theorem IsEquivalent.trans (h : p.IsEquivalent q) (h' : q.IsEquivalent q') : p.IsEquivalent q' := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use C * C'
  constructor
  · grw [h.1, h'.1]
    simp [← smul_assoc]
  · grw [h'.2, h.2]
    simp [← smul_assoc, mul_comm]

variable (p q) in
theorem isEquivalent_comm : p.IsEquivalent q ↔ q.IsEquivalent p :=
  ⟨(·.symm), (·.symm)⟩

variable (p q) in
theorem isEquivalent_iff_isBoundedBy : p.IsEquivalent q ↔ p.IsBoundedBy q ∧ q.IsBoundedBy p := by
  constructor
  · intro ⟨C, h₁, h₂⟩
    exact ⟨⟨C, h₁⟩, ⟨C, h₂⟩⟩
  · intro ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩
    use max C₁ C₂
    constructor
    · grw [h₁]
      gcongr
      simp
    · grw [h₂]
      gcongr
      simp

variable (p) in
@[refl]
theorem isEquivalent_self : p.IsEquivalent p := by grind [isEquivalent_iff_isBoundedBy]

end IsEquivalent

end Seminorm
