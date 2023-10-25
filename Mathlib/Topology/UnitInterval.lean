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

lemma antitone_symm : Antitone σ := fun _ _ h ↦ sub_le_sub_left (α := ℝ) h _

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

/-- Any open cover of a closed interval in ℝ can be refined to
  a finite partition into subintervals. -/
lemma lebesgue_number_lemma_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → Icc a b, t 0 = a ∧
      Monotone t ∧ (∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i) ∧ ∃ n, ∀ m ≥ n, t m = b := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  refine ⟨fun n ↦ projIcc a b h (n * (δ/2) + a), ?_, fun n m hnm ↦ ?_, fun n ↦ ?_, ?_⟩
  · dsimp only; rw [Nat.cast_zero, zero_mul, zero_add, projIcc_left]
  · apply monotone_projIcc
    rw [add_le_add_iff_right, mul_le_mul_right (div_pos δ_pos zero_lt_two)]
    exact_mod_cast hnm
  · obtain ⟨i, hsub⟩ := ball_subset (projIcc a b h (n * (δ/2) + a)) trivial
    refine ⟨i, fun x hx ↦ hsub ?_⟩
    rw [Metric.mem_ball]
    apply (abs_eq_self.mpr _).trans_lt
    · apply (sub_le_sub_right _ _).trans_lt
      on_goal 3 => exact hx.2
      refine (max_sub_max_le_max _ _ _ _).trans_lt (max_lt (by rwa [sub_self]) ?_)
      refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt ?_ ?_)
      · rwa [sub_self, abs_zero]
      · rw [add_sub_add_comm, sub_self, add_zero, ← sub_mul, Nat.cast_succ, add_sub_cancel',
          one_mul, abs_lt]; constructor <;> linarith only [δ_pos]
    · exact sub_nonneg_of_le hx.1
  · refine ⟨Nat.ceil ((b-a)/(δ/2)), fun n hn ↦ ?_⟩
    rw [coe_projIcc, min_eq_left_iff.mpr, max_eq_right h]
    rwa [GE.ge, Nat.ceil_le, div_le_iff (div_pos δ_pos zero_lt_two), sub_le_iff_le_add] at hn

/-- Any open cover of the unit interval can be refined to a finite partition into subintervals. -/
lemma lebesgue_number_lemma_unitInterval {ι} {c : ι → Set unitInterval} (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i) ∧ ∃ n, ∀ m ≥ n, t m = 1 := by
  simp_rw [← Subtype.coe_inj]
  exact lebesgue_number_lemma_Icc zero_le_one hc₁ hc₂

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
