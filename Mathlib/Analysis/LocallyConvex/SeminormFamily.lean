/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Bounded

/-! # Family of seminorms

-/

@[expose] public section


open NormedField Set Seminorm TopologicalSpace Filter List Bornology

open NNReal Pointwise Topology Uniformity

variable {𝕜 𝕜₁ 𝕜₂ E F ι ι' ι'' : Type*}

section FilterBasis

section definition

variable [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]

variable (𝕜 E ι) in
/-- An abbreviation for indexed families of seminorms. This is mainly to allow for dot-notation. -/
abbrev SeminormFamily := ι → Seminorm 𝕜 E

end definition

namespace SeminormFamily

section comp

variable [SeminormedRing 𝕜₁] [AddCommGroup E] [Module 𝕜₁ E]
variable [SeminormedRing 𝕜₂] [AddCommGroup F] [Module 𝕜₂ F]
variable {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-- The family of seminorms obtained by composing each seminorm by a linear map. -/
def comp (q : SeminormFamily 𝕜₂ F ι) (f : E →ₛₗ[σ₁₂] F) : SeminormFamily 𝕜₁ E ι :=
  (q · |>.comp f)

@[simp]
theorem comp_apply (q : SeminormFamily 𝕜₂ F ι) (i : ι) (f : E →ₛₗ[σ₁₂] F) :
    q.comp f i = (q i).comp f :=
  rfl

@[simp, grind .]
theorem comp_id (q : SeminormFamily 𝕜₂ F ι) : q.comp LinearMap.id = q := by
  rfl

@[simp]
theorem comp_const (q : Seminorm 𝕜₂ F) (f : E →ₛₗ[σ₁₂] F) :
    SeminormFamily.comp (fun _ : ι ↦ q) f = (fun _ : ι ↦ q.comp f) := rfl

theorem comp_smul_nnreal (q : SeminormFamily 𝕜₂ F ι) (c : ℝ≥0) (f : E →ₛₗ[σ₁₂] F) :
    c • q.comp f = (c • q).comp f := by
  ext
  simp

theorem finset_sup_comp (q : SeminormFamily 𝕜₂ F ι) (s : Finset ι)
    (f : E →ₛₗ[σ₁₂] F) : (s.sup q).comp f = s.sup (q.comp f) := by
  ext
  simp [Seminorm.finset_sup_apply]

end comp

section IsBoundedBy

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}

variable (p q) in
/-- foo -/
def IsBoundedBy : Prop :=
  ∀ i, ∃ (s : Finset ι'), (p i).IsBoundedBy (s.sup q)

variable (p q) in
/-- A seminorm `p` is bounded by another seminorm `q` if and only if there exists `C : ℝ` such that
for all `x`, `p x ≤ C * q x`. -/
@[grind =]
theorem isBoundedBy_iff_exists_real : p.IsBoundedBy q ↔
    ∀ i, ∃ (s : Finset ι'), ∃ C, ∀ x, p i x ≤ C * (s.sup q) x := by
  congrm (∀ i, ∃ s, ?_)
  exact (p i).isBoundedBy_iff_exists_real (s.sup q)

variable (p) in
@[grind .]
theorem isBoundedBy_self : p.IsBoundedBy p := by
  intro i
  use {i}
  grind [Finset.sup_singleton]

@[trans]
theorem IsBoundedBy.trans {q' : SeminormFamily 𝕜 E ι''} (h : p.IsBoundedBy q)
    (h' : q.IsBoundedBy q') : p.IsBoundedBy q' := by
  intro i
  obtain ⟨s, hs⟩ := h i
  choose y hy using h'
  classical
  use s.biUnion y
  apply hs.trans
  grind [isBoundedBy_congr_sup]

@[simp]
theorem const_isBoundedBy [Nonempty ι'] {q : Seminorm 𝕜 E} :
    SeminormFamily.IsBoundedBy (fun _ : ι' ↦ q) p ↔ ∃ (s : Finset ι), q.IsBoundedBy (s.sup p) := by
  simp [IsBoundedBy]

@[simp]
theorem isBoundedBy_const [Nonempty ι] {p : Seminorm 𝕜 E} :
    q.IsBoundedBy (fun _ : ι ↦ p) ↔ ∀ i, (q i).IsBoundedBy p := by
  constructor <;> intro h i
  · rcases h i with ⟨s, C, h⟩
    use C
    grw [h]
    gcongr
    simp
  · use {Classical.arbitrary ι}
    simp [h]

theorem IsBoundedBy.isBoundedBy_sup (h : p.IsBoundedBy q) {s : Finset ι} : ∃ s' : Finset ι',
    (s.sup p).IsBoundedBy (s'.sup q) := by
  classical
  obtain rfl | _ := s.eq_empty_or_nonempty
  · exact ⟨∅, 1, by simp [Seminorm.bot_eq_zero]⟩
  choose fₛ fC hf using h
  use Finset.biUnion s fₛ, s.card • s.sup fC
  suffices ∀ i : ι, i ∈ s → (p i) ≤ s.sup fC • (Finset.biUnion s fₛ).sup q by
    grw [finset_sup_le_sum p s, Finset.sum_le_sum this, Finset.sum_const, smul_assoc]
  intro i hi
  grw [hf i]
  gcongr
  · exact Finset.le_sup hi
  · grind

variable {R : Type*} [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]
  [Preorder R] [Zero R] [IsOrderedModule R ℝ]

@[grind .]
theorem IsBoundedBy.smul_left (h : p.IsBoundedBy q) (a : R) : (a • p).IsBoundedBy q := by
  intro i
  obtain ⟨s, hs⟩ := h i
  use s
  apply hs.smul_left

@[grind ←]
theorem IsBoundedBy.smul_right (h : p.IsBoundedBy q) {a : ℝ≥0} (ha : a ≠ 0) :
    p.IsBoundedBy (a • q) := by
  intro i
  obtain ⟨s, hs⟩ := h i
  use s
  rw [finset_sup_smul q s a]
  apply hs.smul_right ha

variable {p' : SeminormFamily 𝕜 E ι} {q' : SeminormFamily 𝕜 E ι'}

@[grind .]
theorem IsBoundedBy.add_left (h : p.IsBoundedBy q) (h' : p'.IsBoundedBy q) :
    (p + p').IsBoundedBy q := by
  intro i
  obtain ⟨s, hs⟩ := h i
  obtain ⟨s', hs'⟩ := h' i
  classical
  use s ∪ s'
  apply Seminorm.IsBoundedBy.add_left
  · apply hs.trans
    grind
  · apply hs'.trans
    grind

end IsBoundedBy

section IsEquivalent

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 E ι'}

variable (p q) in
/-- foo -/
@[grind =]
def IsEquivalent : Prop :=
  p.IsBoundedBy q ∧ q.IsBoundedBy p

variable (p) in
theorem isEquivalent_finset_sup : p.IsEquivalent (fun s : Finset ι ↦ s.sup p) := by
  constructor
  · intro i
    exact ⟨{{i}}, 1, by simp⟩
  · intro s
    exact ⟨s, 1, by simp⟩

variable (p) in
theorem isEquivalent_partial_sup [Preorder ι] [LocallyFiniteOrderBot ι] :
    p.IsEquivalent (fun i ↦ (Finset.Iic i).sup p) := by
  constructor
  · intro i
    use {i}, 1
    rw [Finset.sup_singleton, one_smul]
    exact (Finset.le_sup (Finset.mem_Iic.mpr le_rfl) : p i ≤ (Finset.Iic i).sup p)
  · intro i
    exact ⟨Finset.Iic i, 1, by simp⟩

variable (p) in
theorem isEquivalent_equiv (e : ι' ≃ ι) : p.IsEquivalent (p ∘ e) := by
  constructor
  · intro i
    use {e.symm i}
    simp; grind
  · intro i
    use {e i}
    simp; grind

end IsEquivalent

end SeminormFamily
