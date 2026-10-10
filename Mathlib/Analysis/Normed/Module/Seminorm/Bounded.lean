/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! # Boundedness of seminorms

In this file we define boundedness and equivalence of seminorms. A seminorm `p` is bounded by
another seminorm `q` if there exists `C ≥ 0` such that `p ≤ C • q`. Equivalently, if there exists
a *real* `C` such that for all `x`, `p x ≤ C * q x`.

Two seminorms `p, q` are equivalent if there exists `C ≥ 0` such that `p ≤ C • q` and `q ≤ C • p`
or equivalently, if `p` is bounded by `q` and `q` is bounded by `p`.



-/

@[expose] public noncomputable section

open NNReal

section abstract

variable {α β γ : Type*}

section IsBoundedBy

variable (α β) in
/-- The less-sim relation: `a ≲ b`. -/
class LES where
  /-- The less-sim relation: `a ≲ b`. -/
  les : α → β → Prop

open scoped LES

@[inherit_doc] scoped[LES] infix:50 " ≲ " => LES.les

/-- The approx relation: `a ≈ b`. -/
def approx [LES α β] [LES β α] (a : α) (b : β) : Prop := a ≲ b ∧ b ≲ a

@[inherit_doc] scoped[LES] infix:50 " ≈ " => approx

section refl

variable (α) in
class LESRefl [LES α α] where
  protected les_refl : ∀ a : α, a ≲ a

variable [LES α α] [LESRefl α] {a b c : α}

/-- The relation `≤` is reflexive. -/
@[refl, grind .] lemma les_refl : ∀ a : α, a ≲ a := LESRefl.les_refl

/-- A version of `le_refl` where the argument is implicit -/
lemma les_rfl : a ≲ a := les_refl a

/-- The relation `≈` is reflexive if `≲` is reflexive. -/
@[refl, grind .] lemma approx_refl : ∀ a : α, a ≈ a := by
  grind [approx]

/-- A version of `le_refl` where the argument is implicit -/
lemma approx_rfl : a ≈ a := approx_refl a

end refl

section trans

variable (α β γ) in
class LESTrans [LES α β] [LES β γ] [LES α γ] where
  protected les_trans : ∀ (a : α) (b : β) (c : γ), a ≲ b → b ≲ c → a ≲ c

variable [LES α β] [LES β γ] [LES α γ] [LESTrans α β γ] {a : α} {b : β} {c : γ}

/-- The relation `≲` is transitive. -/
lemma les_trans : a ≲ b → b ≲ c → a ≲ c := LESTrans.les_trans _ _ _

instance instTransLES : @Trans α β γ LES.les LES.les LES.les := ⟨les_trans⟩

variable [LES β α] [LES γ β] [LES γ α] [LESTrans γ β α]

/-- The relation `≈` is transitive if `≲` is transitive. -/
lemma approx_trans : a ≈ b → b ≈ c → a ≈ c := by grind [approx, les_trans]

instance instTransApprox : @Trans α β γ approx approx approx := ⟨approx_trans⟩

@[symm]
lemma approx_symm (h : a ≈ b) : b ≈ a := by grind [approx]

lemma approx_comm : a ≈ b ↔ b ≈ a := by grind [approx]

instance instTransApproxLES : @Trans α β γ approx LES.les LES.les := ⟨by grind [approx, les_trans]⟩

instance instTransLESApprox : @Trans α β γ LES.les approx LES.les := ⟨by grind [approx, les_trans]⟩

end trans

end IsBoundedBy

end abstract

variable {ι 𝕜 E : Type*}

namespace Seminorm

open scoped LES

section IsBoundedBy

section SMul

variable [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]

instance : LES (Seminorm 𝕜 E) (Seminorm 𝕜 E) where
  les p q := ∃ C : ℝ≥0, p ≤ C • q

instance : LESRefl (Seminorm 𝕜 E) where
  les_refl p := by
    use 1
    simp

instance : LESTrans (Seminorm 𝕜 E) (Seminorm 𝕜 E) (Seminorm 𝕜 E) where
  les_trans p q q' hp hq := by
    obtain ⟨C, hp⟩ := hp
    obtain ⟨C', hq⟩ := hq
    use C * C'
    grw [hp, hq]
    simp [← smul_assoc]

variable {p p' q q' : Seminorm 𝕜 E}

variable (p q) in
theorem les_iff : p ≲ q ↔ ∃ (C : ℝ≥0), p ≤ C • q := by rfl

variable (p q) in
/-- A seminorm `p` is bounded by another seminorm `q` if and only if there exists `C : ℝ` such that
for all `x`, `p x ≤ C * q x`. -/
@[grind =]
theorem les_iff_exists_real : p ≲ q ↔ ∃ C, ∀ x, p x ≤ C * q x := by
  constructor
  · intro ⟨C, h⟩
    use C
    intro x
    rw [le_def] at h
    grw [h x]
    norm_cast
  · intro ⟨C, h⟩
    use C.toNNReal
    rw [le_def]
    intro x
    grw [h x]
    suffices C • q x ≤ (C.toNNReal : ℝ) • q x by simpa using! this
    gcongr
    simp

variable {R : Type*} [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]
  [Preorder R] [Zero R] [IsOrderedModule R ℝ]

@[grind .]
theorem smul_les (h : p ≲ q) (a : R) : a • p ≲ q := by
  obtain ⟨C, h⟩ := h
  use a • C
  grw [h, smul_assoc]

@[grind ←]
theorem les_smul (h : p ≲ q) {a : ℝ≥0} (ha : a ≠ 0) : p ≲ a • q := by
  obtain ⟨C, h⟩ := h
  use a⁻¹ • C
  calc
    _ ≤ C • q := h
    _ = ((a⁻¹ • C) • a) • q := by congr; simp [field]
    _ = _ := by module

@[grind .]
theorem add_les_add (h : p ≲ q) (h' : p' ≲ q') :
    p + p' ≲ q + q' := by
  obtain ⟨C, h⟩ := h
  obtain ⟨C', h'⟩ := h'
  use max C C'
  calc
    _ ≤ C • q + C' • q' := by grw [h, h']
    _ ≤ max C C' • q + max C C' • q' := by gcongr <;> simp
    _ = _ := by simp

@[grind .]
theorem add_les (h : p ≲ q) (h' : p' ≲ q) :
    p + p' ≲ q := calc
  p + p' ≲ q + q := by grind
  _ = 2 • q := by grind
  _ ≲ q := by grind

end SMul

section Module

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

@[gcongr]
theorem les_congr_sup {p q : ι → Seminorm 𝕜 E} {s : Finset ι}
    (h : ∀ i ∈ s, p i ≲ q i) : s.sup p ≲ s.sup q := by
  choose C hC using h
  classical
  use s.sup (fun i ↦ if h : i ∈ s then C i h else 0)
  simp only [Finset.sup_le_iff]
  intro i hi
  grw [hC i hi]
  gcongr
  · exact Finset.le_sup_dite_pos _ hi hi
  · grind [Finset.le_sup]

@[grind ., gcongr]
theorem les_sup_mono {p : ι → Seminorm 𝕜 E} {s s' : Finset ι}
    (h : s ⊆ s') : s.sup p ≲ s'.sup p := by
  use 1
  grind [one_smul, Finset.sup_le_iff, Finset.le_sup]

end Module

end IsBoundedBy

section IsEquivalent

variable [SeminormedRing 𝕜] [AddCommGroup E] [SMul 𝕜 E]

variable {p p' q q' : Seminorm 𝕜 E}

variable (p q) in
theorem approx_iff_exists : p ≈ q ↔ ∃ (C : ℝ≥0), p ≤ C • q ∧ q ≤ C • p := by
  constructor
  · intro ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩
    use max C₁ C₂
    constructor
    · grw [h₁]
      gcongr
      simp
    · grw [h₂]
      gcongr
      simp
  · intro ⟨C, h₁, h₂⟩
    exact ⟨⟨C, h₁⟩, ⟨C, h₂⟩⟩

variable (p q) in
theorem approx_iff_exists_real : p ≈ q ↔ ∃ C : ℝ, ∀ x, p x ≤ C * q x ∧ q x ≤ C * p x := by
  rw [approx_iff_exists]
  constructor
  · intro ⟨C, h₁, h₂⟩
    use C
    intro x
    simp only [le_def, smul_apply, NNReal.smul_def] at h₁ h₂
    constructor
    · grw [h₁]
      simp
    · grw [h₂]
      simp
  · intro ⟨C, h⟩
    use C.toNNReal
    constructor
    · intro x
      grw [(h x).1]
      simp only [smul_apply, smul_def, Real.coe_toNNReal', smul_eq_mul]
      gcongr
      simp
    · intro x
      grw [(h x).2]
      simp only [smul_apply, smul_def, Real.coe_toNNReal', smul_eq_mul]
      gcongr
      simp

end IsEquivalent

end Seminorm
