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
