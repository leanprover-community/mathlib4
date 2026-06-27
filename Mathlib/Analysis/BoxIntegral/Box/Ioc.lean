/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Creech, Jaume de Dios, Bogdan Georgiev, Harald Helfgott, Ayush Khaitan, Terence Tao
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Basic
public import Mathlib.Data.Prod.Lex

/-! # Intervals as one-dimensional boxes
In this file we define the interval `(a, b]` as a `Box (Fin 1)`, and provide API for it.

Thanks to ICERM for hosting the workshop "Formalization of Analysis" where most of this work
was conducted.
-/
@[expose] public section

namespace BoxIntegral

/-! ## One-dimensional boxes
We specialize some API for `Box` to `Box (Fin 1)`, subscripting with `₁` to indicate the
one-dimensionality.
-/

variable {a b c d : ℝ} (J K : Box (Fin 1))

/-- The left endpoint of a one-dimensional box. -/
def Box.lower₁ : ℝ := J.lower 0

/-- The right endpoint of a one-dimensional box. -/
def Box.upper₁ : ℝ := J.upper 0

lemma Box.lower_lt_upper₁ : J.lower₁ < J.upper₁ := J.lower_lt_upper 0

lemma Box.lower_le_upper₁ : J.lower₁ ≤ J.upper₁ := J.lower_le_upper 0

/-- The length of a one-dimensional box. -/
def Box.length : ℝ := J.upper₁ - J.lower₁

lemma Box.length_pos : 0 < J.length := sub_pos.mpr J.lower_lt_upper₁

lemma Box.length_nonneg : 0 ≤ J.length := J.length_pos.le

/-- The underlying set `(J.lower₁, J.upper₁]` of a one-dimensional box. -/
def Box.toSet₁ : Set ℝ := Set.Ioc J.lower₁ J.upper₁

@[simp]
lemma Box.toSet₁_def : J.toSet₁ = Set.Ioc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.mem₁ (x : Fin 1 → ℝ) :
    x ∈ J ↔ x 0 ∈ J.toSet₁ := by simp [mem_def, lower₁, upper₁]

lemma Box.upper_mem₁ : J.upper₁ ∈ J.toSet₁ := by simp [toSet₁_def, lower_lt_upper₁]

lemma Box.ext_iff₁ : J = K ↔ J.lower₁ = K.lower₁ ∧ J.upper₁ = K.upper₁ :=
  ⟨by aesop, fun ⟨hlow, hup⟩ ↦ by ext; simp [hlow, hup]⟩

lemma Box.le_iff₁ : J ≤ K ↔ K.lower₁ ≤ J.lower₁ ∧ J.upper₁ ≤ K.upper₁ := by
  simp [Box.le_iff_bounds, Pi.le_def, lower₁, upper₁]

lemma Box.disjoint_iff₁ {J J' : Box (Fin 1)} :
    Disjoint J.toSet J'.toSet ↔ J.upper₁ ≤ J'.lower₁ ∨ J'.upper₁ ≤ J.lower₁ := by
  simp only [Set.disjoint_left, mem_coe, mem₁, toSet₁_def, Fin.isValue, Set.mem_Ioc,
    not_and, not_le, and_imp]
  refine ⟨fun h ↦ ?_, by grind⟩
  specialize h (a := min J.upper J'.upper)
  simp at h; grind [lower_lt_upper₁, lower₁, upper₁]

lemma Box.disjoint_iff_disjoint₁ {J J' : Box (Fin 1)} :
    Disjoint J.toSet J'.toSet ↔ Disjoint J.toSet₁ J'.toSet₁ := by
  simp [disjoint_iff₁]; grind [lower_lt_upper₁]

/-- The closed interval `[J.lower₁, J.upper₁]` underlying a one-dimensional box. -/
def Box.Icc₁ : Set ℝ := .Icc J.lower₁ J.upper₁

@[simp]
lemma Box.Icc₁_def : J.Icc₁ = .Icc J.lower₁ J.upper₁ := rfl

@[simp]
lemma Box.Icc₁_eq : J.Icc = {x | x 0 ∈ J.Icc₁} := by
  ext; simp [Box.Icc_def, Pi.le_def, upper₁, lower₁]

lemma Box.upper_mem_Icc₁ : J.upper₁ ∈ J.Icc₁ := by grind [Icc₁_def, upper₁, lower_lt_upper₁]

lemma Box.lower_mem_Icc₁ : J.lower₁ ∈ J.Icc₁ := by grind [Icc₁_def, lower₁, lower_lt_upper₁]

lemma Box.toSet₁_subset_Icc₁ : J.toSet₁ ⊆ J.Icc₁ := by grind [toSet₁_def, Icc₁_def]

lemma Box.mem_Icc₁ (x : Fin 1 → ℝ) : x ∈ J.Icc ↔ x 0 ∈ J.Icc₁ := by simp

lemma Box.Icc₁_subset_Icc₁ {J J' : Box (Fin 1)} (h : J ≤ J') : J.Icc₁ ⊆ J'.Icc₁ := by
  grind [le_iff₁, Icc₁]

lemma Box.dist_le_length_of_mem_Icc₁ {x y : ℝ} (hx : x ∈ J.Icc₁) (hy : y ∈ J.Icc₁) :
    |x - y| ≤ J.length := by grind [length, Icc₁_def]

lemma Box.dist_lt_length_of_mem₁ {x y : ℝ} (hx : x ∈ J.toSet₁) (hy : y ∈ J.toSet₁) :
    |x - y| < J.length := by grind [length, toSet₁_def]

/-! ## Intervals -/

/-- The interval `(a, b]` as a `Box (Fin 1)`. It is symmetric in `a` and `b` — hence named after
`Set.uIoc` — equalling the box `(min a b, max a b]` when `a ≠ b`. Returns the junk interval
`(-1, 1]` if `a = b` (a `Box` cannot be empty, so the empty set is unavailable as a junk value);
this value should rarely be needed. Analogous to, but distinct from, `Set.Ioc`/`Set.uIoc` and
`Finset.Ioc`/`Finset.uIoc`. -/
noncomputable def uIoc (a b : ℝ) : Box (Fin 1) :=
  if h : a = b then ⟨-1, 1, fun _ ↦ by norm_num⟩
  else ⟨fun _ ↦ min a b, fun _ ↦ max a b, fun _ ↦ by grind⟩

lemma uIoc.of_lt (h : a < b) : uIoc a b = ⟨fun _ ↦ a, fun _ ↦ b, fun _ ↦ h⟩ := by
  simp [uIoc, h.ne, h.le]

lemma uIoc.of_gt (h : b < a) : uIoc a b = ⟨fun _ ↦ b, fun _ ↦ a, fun _ ↦ h⟩ := by
  simp [uIoc, h.ne.symm, h.le]

lemma uIoc.of_eq : uIoc a a = ⟨fun _ ↦ -1, fun _ ↦ 1, fun _ ↦ by norm_num⟩ := by
  simp [uIoc]; aesop

@[simp]
lemma uIoc.upper (h : a < b) (i : Fin 1) : (uIoc a b).upper i = b := by simp [h, of_lt]

@[simp]
lemma uIoc.upper₁ (h : a < b) : (uIoc a b).upper₁ = b := upper h 0

@[simp]
lemma uIoc.lower (h : a < b) (i : Fin 1) : (uIoc a b).lower i = a := by simp [h, of_lt]

@[simp]
lemma uIoc.lower₁ (h : a < b) : (uIoc a b).lower₁ = a := lower h 0

@[simp]
lemma uIoc.length (h : a < b) : (uIoc a b).length = b - a := by simp [Box.length, h]

@[simp]
lemma uIoc.upper_gt (h : b < a) (i : Fin 1) : (uIoc a b).upper i = a := by simp [h, of_gt]

@[simp]
lemma uIoc.upper_gt₁ (h : b < a) : (uIoc a b).upper₁ = a := upper_gt h 0

@[simp]
lemma uIoc.lower_gt (h : b < a) (i : Fin 1) : (uIoc a b).lower i = b := by simp [h, of_gt]

@[simp]
lemma uIoc.lower_gt₁ (h : b < a) : (uIoc a b).lower₁ = b := lower_gt h 0

@[simp]
lemma uIoc.length_gt (h : b < a) : (uIoc a b).length = a - b := by simp [Box.length, h]

lemma uIoc.symm : uIoc a b = uIoc b a := by
  by_cases! h : a = b
  · simp [h]
  simp [uIoc]; grind

lemma Box.eq_uIoc (J : Box (Fin 1)) : J = uIoc J.lower₁ J.upper₁ := by
  ext; simp [mem₁, uIoc.of_lt J.lower_lt_upper₁]

lemma mem_uIoc (hab : a < b) (x : Fin 1 → ℝ) : x ∈ uIoc a b ↔ x 0 ∈ Set.Ioc a b := by simp [hab]

@[simp]
lemma uIoc_le_uIoc_iff (hab : a < b) (hcd : c < d) : uIoc c d ≤ uIoc a b ↔ a ≤ c ∧ d ≤ b := by
  simp [Box.le_iff₁, hab, hcd]

lemma uIoc.Icc_eq (hab : a < b) : Box.Icc (uIoc a b) = {x | x 0 ∈ Set.Icc a b} := by simp [hab]

lemma Box.le_uIoc_iff (hab : a < b) (J : Box (Fin 1)) :
    J ≤ uIoc a b ↔ a ≤ J.lower₁ ∧ J.upper₁ ≤ b := by simp [Box.le_iff₁, hab]

lemma Box.ge_uIoc_iff (hab : a < b) (J : Box (Fin 1)) :
    uIoc a b ≤ J ↔ J.lower₁ ≤ a ∧ b ≤ J.upper₁ := by simp [Box.le_iff₁, hab]

lemma Box.mem_of_le (hab : a < b) {J : Box (Fin 1)} (hJ : J ≤ uIoc a b) :
    J.lower₁ ∈ Set.Icc a b ∧ J.upper₁ ∈ Set.Icc a b := by grind [le_uIoc_iff, lower_lt_upper₁]

lemma Icc_subset_of_box_le_uIoc {a b : ℝ} {J : Box (Fin 1)} (hab : a < b) (hJ : J ≤ uIoc a b) :
    J.Icc₁ ⊆ Set.Icc a b := by simp; grind [Box.le_uIoc_iff]

/-! ## Mapping an interval -/

variable (φ : ℝ → ℝ)

/-- The push-forward `(φ J.lower₁, φ J.upper₁]` of a one-dimensional box `J` under `φ : ℝ → ℝ`. -/
noncomputable def uIoc.comp (J : Box (Fin 1)) := uIoc (φ J.lower₁) (φ J.upper₁)

@[simp]
lemma uIoc.comp_apply (hab : a < b) : comp φ (uIoc a b) = uIoc (φ a) (φ b) := by simp [comp, hab]

/-- The map `uIoc.comp φ` is injective on any set of boxes contained in `uIoc a b`, provided `φ` is
strictly monotone on `[a, b]`. -/
lemma uIoc.comp_injOn_of_strictMonoOn {φ : ℝ → ℝ} {S : Set (Box (Fin 1))}
    (hab : a < b) (hS : ∀ J ∈ S, J ≤ uIoc a b) (hmono : StrictMonoOn φ (.Icc a b)) :
    Set.InjOn (comp φ) S := by
  intro I hI J hJ hIJ
  have hI' := Box.mem_of_le hab (hS I hI)
  have hJ' := Box.mem_of_le hab (hS J hJ)
  have hIlt := hmono hI'.1 hI'.2 I.lower_lt_upper₁
  have hJlt := hmono hJ'.1 hJ'.2 J.lower_lt_upper₁
  rw [Box.ext_iff₁]; refine ⟨hmono.injOn hI'.1 hJ'.1 ?_, hmono.injOn hI'.2 hJ'.2 ?_⟩
  · simpa [comp, hIlt, hJlt] using congrArg Box.lower₁ hIJ
  · simpa [comp, hIlt, hJlt] using congrArg Box.upper₁ hIJ

end BoxIntegral
