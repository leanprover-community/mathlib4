/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Algebra.Field
import Mathlib.Data.Set.Intervals.ProjIcc
import Mathlib.Data.Set.Intervals.Instances

#align_import topology.unit_interval from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# The unit interval, as a topological space

Use `open unitInterval` to turn on the notation `I := Set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

noncomputable section

open Classical Topology Filter

open Set Int Set.Icc

/-! ### The unit interval -/


/-- The unit interval `[0,1]` in ℝ. -/
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1
#align unit_interval unitInterval

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

namespace unitInterval

theorem zero_mem : (0 : ℝ) ∈ I :=
  ⟨le_rfl, zero_le_one⟩
#align unit_interval.zero_mem unitInterval.zero_mem

theorem one_mem : (1 : ℝ) ∈ I :=
  ⟨zero_le_one, le_rfl⟩
#align unit_interval.one_mem unitInterval.one_mem

theorem mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
  ⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq <| one_mul 1⟩
#align unit_interval.mul_mem unitInterval.mul_mem

theorem div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
  ⟨div_nonneg hx hy, div_le_one_of_le hxy hy⟩
#align unit_interval.div_mem unitInterval.div_mem

theorem fract_mem (x : ℝ) : fract x ∈ I :=
  ⟨fract_nonneg _, (fract_lt_one _).le⟩
#align unit_interval.fract_mem unitInterval.fract_mem

theorem mem_iff_one_sub_mem {t : ℝ} : t ∈ I ↔ 1 - t ∈ I := by
  rw [mem_Icc, mem_Icc]
  constructor <;> intro <;> constructor <;> linarith
#align unit_interval.mem_iff_one_sub_mem unitInterval.mem_iff_one_sub_mem

instance hasZero : Zero I :=
  ⟨⟨0, zero_mem⟩⟩
#align unit_interval.has_zero unitInterval.hasZero

instance hasOne : One I :=
  ⟨⟨1, by constructor <;> norm_num⟩⟩
#align unit_interval.has_one unitInterval.hasOne

instance : ZeroLEOneClass I := ⟨@zero_le_one ℝ _ _ _ _⟩

instance : BoundedOrder I := Set.Icc.boundedOrder zero_le_one

lemma univ_eq_Icc : (univ : Set I) = Icc 0 1 := by
  ext ⟨t, t0, t1⟩; simp_rw [mem_univ, true_iff]; exact ⟨t0, t1⟩

theorem coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr coe_eq_zero
#align unit_interval.coe_ne_zero unitInterval.coe_ne_zero

theorem coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 :=
  not_iff_not.mpr coe_eq_one
#align unit_interval.coe_ne_one unitInterval.coe_ne_one

instance : Nonempty I :=
  ⟨0⟩

instance : Mul I :=
  ⟨fun x y => ⟨x * y, mul_mem x.2 y.2⟩⟩

-- todo: we could set up a `LinearOrderedCommMonoidWithZero I` instance
theorem mul_le_left {x y : I} : x * y ≤ x :=
  Subtype.coe_le_coe.mp <| (mul_le_mul_of_nonneg_left y.2.2 x.2.1).trans_eq <| mul_one x.1
#align unit_interval.mul_le_left unitInterval.mul_le_left

theorem mul_le_right {x y : I} : x * y ≤ y :=
  Subtype.coe_le_coe.mp <| (mul_le_mul_of_nonneg_right x.2.2 y.2.1).trans_eq <| one_mul y.1
#align unit_interval.mul_le_right unitInterval.mul_le_right

/-- Unit interval central symmetry. -/
def symm : I → I := fun t => ⟨1 - t, mem_iff_one_sub_mem.mp t.prop⟩
#align unit_interval.symm unitInterval.symm

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp]
theorem symm_zero : σ 0 = 1 :=
  Subtype.ext <| by simp [symm]
#align unit_interval.symm_zero unitInterval.symm_zero

@[simp]
theorem symm_one : σ 1 = 0 :=
  Subtype.ext <| by simp [symm]
#align unit_interval.symm_one unitInterval.symm_one

@[simp]
theorem symm_symm (x : I) : σ (σ x) = x :=
  Subtype.ext <| by simp [symm]
#align unit_interval.symm_symm unitInterval.symm_symm

@[simp]
theorem coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x :=
  rfl
#align unit_interval.coe_symm_eq unitInterval.coe_symm_eq

-- Porting note: Proof used to be `by continuity!`
@[continuity]
theorem continuous_symm : Continuous σ :=
  (continuous_const.add continuous_induced_dom.neg).subtype_mk _
#align unit_interval.continuous_symm unitInterval.continuous_symm

lemma strictAnti_symm : StrictAnti σ := fun _ _ h ↦ sub_lt_sub_left (α := ℝ) h _

lemma bijective_symm : Function.Bijective σ :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

lemma half_le_symm_iff (t : I) : 1 / 2 ≤ (σ t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 := by
  rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ←le_sub_iff_add_le, sub_half]

instance : ConnectedSpace I :=
  Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

/-- Verify there is an instance for `CompactSpace I`. -/
example : CompactSpace I := by infer_instance

theorem nonneg (x : I) : 0 ≤ (x : ℝ) :=
  x.2.1
#align unit_interval.nonneg unitInterval.nonneg

theorem one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2
#align unit_interval.one_minus_nonneg unitInterval.one_minus_nonneg

theorem le_one (x : I) : (x : ℝ) ≤ 1 :=
  x.2.2
#align unit_interval.le_one unitInterval.le_one

theorem one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1
#align unit_interval.one_minus_le_one unitInterval.one_minus_le_one

theorem add_pos {t : I} {x : ℝ} (hx : 0 < x) : 0 < (x + t : ℝ) :=
  add_pos_of_pos_of_nonneg hx <| nonneg _
#align unit_interval.add_pos unitInterval.add_pos

/-- like `unitInterval.nonneg`, but with the inequality in `I`. -/
theorem nonneg' {t : I} : 0 ≤ t :=
  t.2.1
#align unit_interval.nonneg' unitInterval.nonneg'

/-- like `unitInterval.le_one`, but with the inequality in `I`. -/
theorem le_one' {t : I} : t ≤ 1 :=
  t.2.2
#align unit_interval.le_one' unitInterval.le_one'

instance : NeZero (1 : I) := ⟨fun h ↦ one_ne_zero <| congrArg Subtype.val h⟩

theorem mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ Set.Icc (0 : ℝ) (1 / a) := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff ha, mul_comm] at h₂
#align unit_interval.mul_pos_mem_iff unitInterval.mul_pos_mem_iff

theorem two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
#align unit_interval.two_mul_sub_one_mem_iff unitInterval.two_mul_sub_one_mem_iff

end unitInterval

section partition

namespace Set.Icc

variable {α} [LinearOrderedAddCommGroup α] {a b c d : α} (h : a ≤ b) {δ : α}

-- TODO: Set.projIci, Set.projIic
/-- `Set.projIcc` is a contraction. -/
lemma _root_.Set.abs_projIcc_sub_projIcc : (|projIcc a b h c - projIcc a b h d| : α) ≤ |c - d| := by
  wlog hdc : d ≤ c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_le hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc), abs_eq_self.2 (sub_nonneg.2 <| monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (by rwa [sub_self]) ?_)
  refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rwa [sub_self, abs_zero]
  · exact (abs_eq_self.mpr hdc).le

/-- Equally spaced points in a closed interval. -/
def addNsmul (δ : α) (n : ℕ) : Icc a b := projIcc a b h (a + n • δ)

lemma addNsmul_zero : addNsmul h δ 0 = a := by
  rw [addNsmul, zero_smul, add_zero, projIcc_left]

lemma addNsmul_eq_right [Archimedean α] (hδ : 0 < δ) :
    ∃ m, ∀ n ≥ m, addNsmul h δ n = b := by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn ↦ ?_⟩
  rw [addNsmul, coe_projIcc, add_comm, min_eq_left_iff.mpr, max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul hδ.le hn)

lemma monotone_addNsmul (hδ : 0 ≤ δ) : Monotone (addNsmul h δ) :=
  fun _ _ hnm ↦ monotone_projIcc h <| (add_le_add_iff_left _).mpr (nsmul_le_nsmul hδ hnm)

lemma abs_sub_addNsmul_le (hδ : 0 ≤ δ) {t : Icc a b} (n : ℕ)
    (ht : t ∈ Icc (addNsmul h δ n) (addNsmul h δ (n+1))) :
    (|t - addNsmul h δ n| : α) ≤ δ :=
  (abs_eq_self.2 <| sub_nonneg.2 ht.1).trans_le <| (sub_le_sub_right (by exact ht.2) _).trans <|
    (le_abs_self _).trans <| (abs_projIcc_sub_projIcc h).trans <| by
      rw [add_sub_add_comm, sub_self, zero_add, succ_nsmul, add_sub_cancel]
      exact (abs_eq_self.mpr hδ).le

end Set.Icc

open scoped unitInterval

/-- Any open cover of a closed interval in ℝ can be refined to
  a finite partition into subintervals. -/
lemma lebesgue_number_lemma_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → Icc a b, t 0 = a ∧
      Monotone t ∧ (∃ m, ∀ n ≥ m, t n = b) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  refine ⟨addNsmul h (δ/2), addNsmul_zero h,
    monotone_addNsmul h hδ.le, addNsmul_eq_right h hδ, fun n ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNsmul h (δ/2) n) trivial
  exact ⟨i, fun t ht ↦ hsub ((abs_sub_addNsmul_le h hδ.le n ht).trans_lt <| half_lt_self δ_pos)⟩

/-- Any open cover of the unit interval can be refined to a finite partition into subintervals. -/
lemma lebesgue_number_lemma_unitInterval {ι} {c : ι → Set I} (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  simp_rw [← Subtype.coe_inj]
  exact lebesgue_number_lemma_Icc zero_le_one hc₁ hc₂

lemma lebesgue_number_lemma_unitInterval_prod_self {ι} {c : ι → Set (I × I)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  have hδ := half_pos δ_pos
  simp_rw [Subtype.ext_iff]
  have h : (0 : ℝ) ≤ 1 := zero_le_one
  refine ⟨addNsmul h (δ/2), addNsmul_zero h,
    monotone_addNsmul h hδ.le, addNsmul_eq_right h hδ, fun n m ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNsmul h (δ/2) n, addNsmul h (δ/2) m) trivial
  exact ⟨i, fun t ht ↦ hsub (Metric.mem_ball.mpr <| (max_le (abs_sub_addNsmul_le h hδ.le n ht.1) <|
    abs_sub_addNsmul_le h hδ.le m ht.2).trans_lt <| half_lt_self δ_pos)⟩

end partition

@[simp]
theorem projIcc_eq_zero {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
  projIcc_eq_left zero_lt_one
#align proj_Icc_eq_zero projIcc_eq_zero

@[simp]
theorem projIcc_eq_one {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
  projIcc_eq_right zero_lt_one
#align proj_Icc_eq_one projIcc_eq_one

namespace Tactic.Interactive

-- Porting note: This replaces an unsafe def tactic
/-- A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`. -/
macro "unit_interval" : tactic =>
  `(tactic| (first
  | apply unitInterval.nonneg
  | apply unitInterval.one_minus_nonneg
  | apply unitInterval.le_one
  | apply unitInterval.one_minus_le_one))
#noalign tactic.interactive.unit_interval

example (x : unitInterval) : 0 ≤ (x : ℝ) := by unit_interval

end Tactic.Interactive

section

variable {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]

-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
/-- The image of `[0,1]` under the homeomorphism `fun x ↦ a * x + b` is `[b, a+b]`.
-/
theorem affineHomeomorph_image_I (a b : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne.symm '' Set.Icc 0 1 = Set.Icc b (a + b) := by simp [h]
set_option linter.uppercaseLean3 false in
#align affine_homeomorph_image_I affineHomeomorph_image_I

/-- The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine' (e.trans _).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp
set_option linter.uppercaseLean3 false in
#align Icc_homeo_I iccHomeoI

@[simp]
theorem iccHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) :
    ((iccHomeoI a b h) x : 𝕜) = (x - a) / (b - a) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Icc_homeo_I_apply_coe iccHomeoI_apply_coe

@[simp]
theorem iccHomeoI_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜)) :
    ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a :=
  rfl
set_option linter.uppercaseLean3 false in
#align Icc_homeo_I_symm_apply_coe iccHomeoI_symm_apply_coe

end
