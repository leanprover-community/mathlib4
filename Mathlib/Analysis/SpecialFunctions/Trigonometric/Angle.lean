/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.CharZero.Quotient
import Mathlib.Topology.Instances.Sign

#align_import analysis.special_functions.trigonometric.angle from "leanprover-community/mathlib"@"213b0cff7bc5ab6696ee07cceec80829ce42efec"

/-!
# The type of angles

In this file we define `Real.Angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/


open Real

noncomputable section

namespace Real

-- Porting note: can't derive `NormedAddCommGroup, Inhabited`
/-- The type of angles -/
def Angle : Type :=
  AddCircle (2 * π)
#align real.angle Real.Angle

namespace Angle

-- Porting note: added due to missing instances due to no deriving
instance : NormedAddCommGroup Angle :=
  inferInstanceAs (NormedAddCommGroup (AddCircle (2 * π)))

-- Porting note: added due to missing instances due to no deriving
instance : Inhabited Angle :=
  inferInstanceAs (Inhabited (AddCircle (2 * π)))

-- Porting note: added due to missing instances due to no deriving
-- also, without this, a plain `QuotientAddGroup.mk`
-- causes coerced terms to be of type `ℝ ⧸ AddSubgroup.zmultiples (2 * π)`
/-- The canonical map from `ℝ` to the quotient `Angle`. -/
@[coe]
protected def coe (r : ℝ) : Angle := QuotientAddGroup.mk r

instance : Coe ℝ Angle := ⟨Angle.coe⟩

instance : CircularOrder Real.Angle :=
  @AddCircle.instCircularOrderAddCircle _ _ _ _ _ ⟨by norm_num [pi_pos]⟩ _
                                                      -- 🎉 no goals

@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → Angle) :=
  continuous_quotient_mk'
#align real.angle.continuous_coe Real.Angle.continuous_coe

/-- Coercion `ℝ → Angle` as an additive homomorphism. -/
def coeHom : ℝ →+ Angle :=
  QuotientAddGroup.mk' _
#align real.angle.coe_hom Real.Angle.coeHom

@[simp]
theorem coe_coeHom : (coeHom : ℝ → Angle) = ((↑) : ℝ → Angle) :=
  rfl
#align real.angle.coe_coe_hom Real.Angle.coe_coeHom

/-- An induction principle to deduce results for `Angle` from those for `ℝ`, used with
`induction θ using Real.Angle.induction_on`. -/
@[elab_as_elim]
protected theorem induction_on {p : Angle → Prop} (θ : Angle) (h : ∀ x : ℝ, p x) : p θ :=
  Quotient.inductionOn' θ h
#align real.angle.induction_on Real.Angle.induction_on

@[simp]
theorem coe_zero : ↑(0 : ℝ) = (0 : Angle) :=
  rfl
#align real.angle.coe_zero Real.Angle.coe_zero

@[simp]
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : Angle) :=
  rfl
#align real.angle.coe_add Real.Angle.coe_add

@[simp]
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : Angle) :=
  rfl
#align real.angle.coe_neg Real.Angle.coe_neg

@[simp]
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : Angle) :=
  rfl
#align real.angle.coe_sub Real.Angle.coe_sub

theorem coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = n • (↑x : Angle) :=
  rfl
#align real.angle.coe_nsmul Real.Angle.coe_nsmul

theorem coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = z • (↑x : Angle) :=
  rfl
#align real.angle.coe_zsmul Real.Angle.coe_zsmul

@[simp, norm_cast]
theorem coe_nat_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : Angle) := by
  simpa only [nsmul_eq_mul] using coeHom.map_nsmul x n
  -- 🎉 no goals
#align real.angle.coe_nat_mul_eq_nsmul Real.Angle.coe_nat_mul_eq_nsmul

@[simp, norm_cast]
theorem coe_int_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle) := by
  simpa only [zsmul_eq_mul] using coeHom.map_zsmul x n
  -- 🎉 no goals
#align real.angle.coe_int_mul_eq_zsmul Real.Angle.coe_int_mul_eq_zsmul

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [QuotientAddGroup.eq, AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]
  -- Porting note: added `rw`, `simp [Angle.coe, QuotientAddGroup.eq]` doesn't fire otherwise
  rw [Angle.coe, Angle.coe, QuotientAddGroup.eq]
  -- ⊢ -ψ + θ ∈ AddSubgroup.zmultiples (2 * π) ↔ ∃ k, θ - ψ = 2 * π * ↑k
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]
#align real.angle.angle_eq_iff_two_pi_dvd_sub Real.Angle.angle_eq_iff_two_pi_dvd_sub

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩
                                       -- 🎉 no goals
#align real.angle.coe_two_pi Real.Angle.coe_two_pi

@[simp]
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg, angle_eq_iff_two_pi_dvd_sub]
  -- ⊢ ∃ k, -π - π = 2 * π * ↑k
  use -1
  -- ⊢ -π - π = 2 * π * ↑(-1)
  simp [two_mul, sub_eq_add_neg]
  -- 🎉 no goals
#align real.angle.neg_coe_pi Real.Angle.neg_coe_pi

@[simp]
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_nsmul, two_nsmul, add_halves]
  -- 🎉 no goals
#align real.angle.two_nsmul_coe_div_two Real.Angle.two_nsmul_coe_div_two

@[simp]
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_zsmul, two_zsmul, add_halves]
  -- 🎉 no goals
#align real.angle.two_zsmul_coe_div_two Real.Angle.two_zsmul_coe_div_two

-- Porting note: @[simp] can prove it
theorem two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : Angle) = π := by
  rw [two_nsmul_coe_div_two, coe_neg, neg_coe_pi]
  -- 🎉 no goals
#align real.angle.two_nsmul_neg_pi_div_two Real.Angle.two_nsmul_neg_pi_div_two

-- Porting note: @[simp] can prove it
theorem two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : Angle) = π := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_neg_pi_div_two]
  -- 🎉 no goals
#align real.angle.two_zsmul_neg_pi_div_two Real.Angle.two_zsmul_neg_pi_div_two

theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg, neg_coe_pi]
  -- 🎉 no goals
#align real.angle.sub_coe_pi_eq_add_coe_pi Real.Angle.sub_coe_pi_eq_add_coe_pi

@[simp]
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : Angle) = 0 := by simp [← coe_nat_mul_eq_nsmul]
                                                           -- 🎉 no goals
#align real.angle.two_nsmul_coe_pi Real.Angle.two_nsmul_coe_pi

@[simp]
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : Angle) = 0 := by simp [← coe_int_mul_eq_zsmul]
                                                           -- 🎉 no goals
#align real.angle.two_zsmul_coe_pi Real.Angle.two_zsmul_coe_pi

@[simp]
theorem coe_pi_add_coe_pi : (π : Real.Angle) + π = 0 := by rw [← two_nsmul, two_nsmul_coe_pi]
                                                           -- 🎉 no goals
#align real.angle.coe_pi_add_coe_pi Real.Angle.coe_pi_add_coe_pi

theorem zsmul_eq_iff {ψ θ : Angle} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ) :=
  QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz
#align real.angle.zsmul_eq_iff Real.Angle.zsmul_eq_iff

theorem nsmul_eq_iff {ψ θ : Angle} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ) :=
  QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz
#align real.angle.nsmul_eq_iff Real.Angle.nsmul_eq_iff

theorem two_zsmul_eq_iff {ψ θ : Angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  -- Porting note: no `Int.natAbs_bit0` anymore
  have : Int.natAbs 2 = 2 := rfl
  -- ⊢ 2 • ψ = 2 • θ ↔ ψ = θ ∨ ψ = θ + ↑π
  rw [zsmul_eq_iff two_ne_zero, this, Fin.exists_fin_two, Fin.val_zero,
    Fin.val_one, zero_smul, coe_zero, add_zero, one_smul, Int.cast_two,
    mul_div_cancel_left (_ : ℝ) two_ne_zero]
#align real.angle.two_zsmul_eq_iff Real.Angle.two_zsmul_eq_iff

theorem two_nsmul_eq_iff {ψ θ : Angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  simp_rw [← coe_nat_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]
  -- 🎉 no goals
#align real.angle.two_nsmul_eq_iff Real.Angle.two_nsmul_eq_iff

theorem two_nsmul_eq_zero_iff {θ : Angle} : (2 : ℕ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  convert two_nsmul_eq_iff <;> simp
  -- ⊢ 0 = 2 • 0
                               -- 🎉 no goals
                               -- 🎉 no goals
#align real.angle.two_nsmul_eq_zero_iff Real.Angle.two_nsmul_eq_zero_iff

theorem two_nsmul_ne_zero_iff {θ : Angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_nsmul_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.two_nsmul_ne_zero_iff Real.Angle.two_nsmul_ne_zero_iff

theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.two_zsmul_eq_zero_iff Real.Angle.two_zsmul_eq_zero_iff

theorem two_zsmul_ne_zero_iff {θ : Angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_zsmul_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.two_zsmul_ne_zero_iff Real.Angle.two_zsmul_ne_zero_iff

theorem eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π := by
  rw [← add_eq_zero_iff_eq_neg, ← two_nsmul, two_nsmul_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.eq_neg_self_iff Real.Angle.eq_neg_self_iff

theorem ne_neg_self_iff {θ : Angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← eq_neg_self_iff.not]
  -- 🎉 no goals
#align real.angle.ne_neg_self_iff Real.Angle.ne_neg_self_iff

theorem neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π := by rw [eq_comm, eq_neg_self_iff]
                                                                   -- 🎉 no goals
#align real.angle.neg_eq_self_iff Real.Angle.neg_eq_self_iff

theorem neg_ne_self_iff {θ : Angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← neg_eq_self_iff.not]
  -- 🎉 no goals
#align real.angle.neg_ne_self_iff Real.Angle.neg_ne_self_iff

theorem two_nsmul_eq_pi_iff {θ : Angle} : (2 : ℕ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  have h : (π : Angle) = (2 : ℕ) • (π / 2 : ℝ) := by rw [two_nsmul, add_halves]
  -- ⊢ 2 • θ = ↑π ↔ θ = ↑(π / 2) ∨ θ = ↑(-π / 2)
  nth_rw 1 [h]
  -- ⊢ 2 • θ = ↑(2 • (π / 2)) ↔ θ = ↑(π / 2) ∨ θ = ↑(-π / 2)
  rw [coe_nsmul, two_nsmul_eq_iff]
  -- ⊢ θ = ↑(π / 2) ∨ θ = ↑(π / 2) + ↑π ↔ θ = ↑(π / 2) ∨ θ = ↑(-π / 2)
  -- Porting note: `congr` didn't simplify the goal of iff of `Or`s
  convert Iff.rfl
  -- ⊢ ↑(-π / 2) = ↑(π / 2) + ↑π
  rw [add_comm, ← coe_add, ← sub_eq_zero, ← coe_sub, neg_div, ←neg_sub, sub_neg_eq_add, add_assoc,
    add_halves, ← two_mul, coe_neg, coe_two_pi, neg_zero]
#align real.angle.two_nsmul_eq_pi_iff Real.Angle.two_nsmul_eq_pi_iff

theorem two_zsmul_eq_pi_iff {θ : Angle} : (2 : ℤ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_eq_pi_iff]
  -- 🎉 no goals
#align real.angle.two_zsmul_eq_pi_iff Real.Angle.two_zsmul_eq_pi_iff

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
    cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ := by
  constructor
  -- ⊢ cos θ = cos ψ → ↑θ = ↑ψ ∨ ↑θ = -↑ψ
  · intro Hcos
    -- ⊢ ↑θ = ↑ψ ∨ ↑θ = -↑ψ
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
      eq_false (two_ne_zero' ℝ), false_or_iff, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    -- ⊢ ↑θ = ↑ψ ∨ ↑θ = -↑ψ
    · right
      -- ⊢ ↑θ = -↑ψ
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), ← sub_eq_iff_eq_add] at hn
      -- ⊢ ↑θ = -↑ψ
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc, coe_int_mul_eq_zsmul,
        mul_comm, coe_two_pi, zsmul_zero]
    · left
      -- ⊢ ↑θ = ↑ψ
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), eq_sub_iff_add_eq] at hn
      -- ⊢ ↑θ = ↑ψ
      rw [← hn, coe_add, mul_assoc, coe_int_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero,
        zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    -- ⊢ ((∃ k, θ - ψ = 2 * π * ↑k) ∨ ∃ k, θ - -ψ = 2 * π * ↑k) → cos θ = cos ψ
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    -- ⊢ cos θ = cos ψ
    rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left _ (two_ne_zero' ℝ),
      mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
      mul_div_cancel_left _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero,
      zero_mul]
#align real.angle.cos_eq_iff_coe_eq_or_eq_neg Real.Angle.cos_eq_iff_coe_eq_or_eq_neg

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
    sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π := by
  constructor
  -- ⊢ sin θ = sin ψ → ↑θ = ↑ψ ∨ ↑θ + ↑ψ = ↑π
  · intro Hsin
    -- ⊢ ↑θ = ↑ψ ∨ ↑θ + ↑ψ = ↑π
    rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin
    -- ⊢ ↑θ = ↑ψ ∨ ↑θ + ↑ψ = ↑π
    cases' cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h h
    -- ⊢ ↑θ = ↑ψ ∨ ↑θ + ↑ψ = ↑π
    · left
      -- ⊢ ↑θ = ↑ψ
      rw [coe_sub, coe_sub] at h
      -- ⊢ ↑θ = ↑ψ
      exact sub_right_inj.1 h
      -- 🎉 no goals
    right
    -- ⊢ ↑θ + ↑ψ = ↑π
    rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub, sub_add_eq_add_sub, ← coe_add,
      add_halves, sub_sub, sub_eq_zero] at h
    exact h.symm
    -- 🎉 no goals
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    -- ⊢ ((∃ k, θ - ψ = 2 * π * ↑k) ∨ ∃ k, θ - (π - ψ) = 2 * π * ↑k) → sin θ = sin ψ
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    -- ⊢ sin θ = sin ψ
    rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left _ (two_ne_zero' ℝ),
      mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
      mul_div_cancel_left _ (two_ne_zero' ℝ), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
      mul_zero]
#align real.angle.sin_eq_iff_coe_eq_or_add_eq_pi Real.Angle.sin_eq_iff_coe_eq_or_add_eq_pi

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : Angle) = ψ := by
  cases' cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc hc; · exact hc
  -- ⊢ ↑θ = ↑ψ
                                                           -- 🎉 no goals
  cases' sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs hs; · exact hs
  -- ⊢ ↑θ = ↑ψ
                                                              -- 🎉 no goals
  rw [eq_neg_iff_add_eq_zero, hs] at hc
  -- ⊢ ↑θ = ↑ψ
  obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  -- ⊢ ↑θ = ↑ψ
  rw [← neg_one_mul, add_zero, ← sub_eq_zero, zsmul_eq_mul, ← mul_assoc, ← sub_mul, mul_eq_zero,
    eq_false (ne_of_gt pi_pos), or_false_iff, sub_neg_eq_add, ← Int.cast_zero, ← Int.cast_one,
    ← Int.int_cast_ofNat, ← Int.cast_mul, ← Int.cast_add, Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : ℤ) = 0 % (2 : ℤ) := congr_arg (· % (2 : ℤ)) hn
  -- ⊢ ↑θ = ↑ψ
  rw [add_comm, Int.add_mul_emod_self] at this
  -- ⊢ ↑θ = ↑ψ
  exact absurd this one_ne_zero
  -- 🎉 no goals
#align real.angle.cos_sin_inj Real.Angle.cos_sin_inj

/-- The sine of a `Real.Angle`. -/
def sin (θ : Angle) : ℝ :=
  sin_periodic.lift θ
#align real.angle.sin Real.Angle.sin

@[simp]
theorem sin_coe (x : ℝ) : sin (x : Angle) = Real.sin x :=
  rfl
#align real.angle.sin_coe Real.Angle.sin_coe

@[continuity]
theorem continuous_sin : Continuous sin :=
  Real.continuous_sin.quotient_liftOn' _
#align real.angle.continuous_sin Real.Angle.continuous_sin

/-- The cosine of a `Real.Angle`. -/
def cos (θ : Angle) : ℝ :=
  cos_periodic.lift θ
#align real.angle.cos Real.Angle.cos

@[simp]
theorem cos_coe (x : ℝ) : cos (x : Angle) = Real.cos x :=
  rfl
#align real.angle.cos_coe Real.Angle.cos_coe

@[continuity]
theorem continuous_cos : Continuous cos :=
  Real.continuous_cos.quotient_liftOn' _
#align real.angle.continuous_cos Real.Angle.continuous_cos

theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : ℝ} :
    cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos ↑x✝ = Real.cos ψ ↔ ↑x✝ = ↑ψ ∨ ↑x✝ = -↑ψ
  exact cos_eq_iff_coe_eq_or_eq_neg
  -- 🎉 no goals
#align real.angle.cos_eq_real_cos_iff_eq_or_eq_neg Real.Angle.cos_eq_real_cos_iff_eq_or_eq_neg

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction ψ using Real.Angle.induction_on
  -- ⊢ cos θ = cos ↑x✝ ↔ θ = ↑x✝ ∨ θ = -↑x✝
  exact cos_eq_real_cos_iff_eq_or_eq_neg
  -- 🎉 no goals
#align real.angle.cos_eq_iff_eq_or_eq_neg Real.Angle.cos_eq_iff_eq_or_eq_neg

theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : ℝ} :
    sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction θ using Real.Angle.induction_on
  -- ⊢ sin ↑x✝ = Real.sin ψ ↔ ↑x✝ = ↑ψ ∨ ↑x✝ + ↑ψ = ↑π
  exact sin_eq_iff_coe_eq_or_add_eq_pi
  -- 🎉 no goals
#align real.angle.sin_eq_real_sin_iff_eq_or_add_eq_pi Real.Angle.sin_eq_real_sin_iff_eq_or_add_eq_pi

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction ψ using Real.Angle.induction_on
  -- ⊢ sin θ = sin ↑x✝ ↔ θ = ↑x✝ ∨ θ + ↑x✝ = ↑π
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi
  -- 🎉 no goals
#align real.angle.sin_eq_iff_eq_or_add_eq_pi Real.Angle.sin_eq_iff_eq_or_add_eq_pi

@[simp]
theorem sin_zero : sin (0 : Angle) = 0 := by rw [← coe_zero, sin_coe, Real.sin_zero]
                                             -- 🎉 no goals
#align real.angle.sin_zero Real.Angle.sin_zero

-- Porting note: @[simp] can prove it
theorem sin_coe_pi : sin (π : Angle) = 0 := by rw [sin_coe, Real.sin_pi]
                                               -- 🎉 no goals
#align real.angle.sin_coe_pi Real.Angle.sin_coe_pi

theorem sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π := by
  nth_rw 1 [← sin_zero]
  -- ⊢ sin θ = sin 0 ↔ θ = 0 ∨ θ = ↑π
  rw [sin_eq_iff_eq_or_add_eq_pi]
  -- ⊢ θ = 0 ∨ θ + 0 = ↑π ↔ θ = 0 ∨ θ = ↑π
  simp
  -- 🎉 no goals
#align real.angle.sin_eq_zero_iff Real.Angle.sin_eq_zero_iff

theorem sin_ne_zero_iff {θ : Angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sin_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.sin_ne_zero_iff Real.Angle.sin_ne_zero_iff

@[simp]
theorem sin_neg (θ : Angle) : sin (-θ) = -sin θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ sin (-↑x✝) = -sin ↑x✝
  exact Real.sin_neg _
  -- 🎉 no goals
#align real.angle.sin_neg Real.Angle.sin_neg

theorem sin_antiperiodic : Function.Antiperiodic sin (π : Angle) := by
  intro θ
  -- ⊢ sin (θ + ↑π) = -sin θ
  induction θ using Real.Angle.induction_on
  -- ⊢ sin (↑x✝ + ↑π) = -sin ↑x✝
  exact Real.sin_antiperiodic _
  -- 🎉 no goals
#align real.angle.sin_antiperiodic Real.Angle.sin_antiperiodic

@[simp]
theorem sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ :=
  sin_antiperiodic θ
#align real.angle.sin_add_pi Real.Angle.sin_add_pi

@[simp]
theorem sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ :=
  sin_antiperiodic.sub_eq θ
#align real.angle.sin_sub_pi Real.Angle.sin_sub_pi

@[simp]
theorem cos_zero : cos (0 : Angle) = 1 := by rw [← coe_zero, cos_coe, Real.cos_zero]
                                             -- 🎉 no goals
#align real.angle.cos_zero Real.Angle.cos_zero

-- Porting note: @[simp] can prove it
theorem cos_coe_pi : cos (π : Angle) = -1 := by rw [cos_coe, Real.cos_pi]
                                                -- 🎉 no goals
#align real.angle.cos_coe_pi Real.Angle.cos_coe_pi

@[simp]
theorem cos_neg (θ : Angle) : cos (-θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos (-↑x✝) = cos ↑x✝
  exact Real.cos_neg _
  -- 🎉 no goals
#align real.angle.cos_neg Real.Angle.cos_neg

theorem cos_antiperiodic : Function.Antiperiodic cos (π : Angle) := by
  intro θ
  -- ⊢ cos (θ + ↑π) = -cos θ
  induction θ using Real.Angle.induction_on
  -- ⊢ cos (↑x✝ + ↑π) = -cos ↑x✝
  exact Real.cos_antiperiodic _
  -- 🎉 no goals
#align real.angle.cos_antiperiodic Real.Angle.cos_antiperiodic

@[simp]
theorem cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ :=
  cos_antiperiodic θ
#align real.angle.cos_add_pi Real.Angle.cos_add_pi

@[simp]
theorem cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ :=
  cos_antiperiodic.sub_eq θ
#align real.angle.cos_sub_pi Real.Angle.cos_sub_pi

theorem cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [← cos_pi_div_two, ← cos_coe, cos_eq_iff_eq_or_eq_neg, ← coe_neg, ← neg_div]
  -- 🎉 no goals
#align real.angle.cos_eq_zero_iff Real.Angle.cos_eq_zero_iff

theorem sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  -- ⊢ sin (↑x✝ + θ₂) = sin ↑x✝ * cos θ₂ + cos ↑x✝ * sin θ₂
  induction θ₂ using Real.Angle.induction_on
  -- ⊢ sin (↑x✝¹ + ↑x✝) = sin ↑x✝¹ * cos ↑x✝ + cos ↑x✝¹ * sin ↑x✝
  exact Real.sin_add _ _
  -- 🎉 no goals
#align real.angle.sin_add Real.Angle.sin_add

theorem cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ := by
  induction θ₂ using Real.Angle.induction_on
  -- ⊢ cos (θ₁ + ↑x✝) = cos θ₁ * cos ↑x✝ - sin θ₁ * sin ↑x✝
  induction θ₁ using Real.Angle.induction_on
  -- ⊢ cos (↑x✝ + ↑x✝¹) = cos ↑x✝ * cos ↑x✝¹ - sin ↑x✝ * sin ↑x✝¹
  exact Real.cos_add _ _
  -- 🎉 no goals
#align real.angle.cos_add Real.Angle.cos_add

@[simp]
theorem cos_sq_add_sin_sq (θ : Real.Angle) : cos θ ^ 2 + sin θ ^ 2 = 1 := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos ↑x✝ ^ 2 + sin ↑x✝ ^ 2 = 1
  exact Real.cos_sq_add_sin_sq _
  -- 🎉 no goals
#align real.angle.cos_sq_add_sin_sq Real.Angle.cos_sq_add_sin_sq

theorem sin_add_pi_div_two (θ : Angle) : sin (θ + ↑(π / 2)) = cos θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ sin (↑x✝ + ↑(π / 2)) = cos ↑x✝
  exact Real.sin_add_pi_div_two _
  -- 🎉 no goals
#align real.angle.sin_add_pi_div_two Real.Angle.sin_add_pi_div_two

theorem sin_sub_pi_div_two (θ : Angle) : sin (θ - ↑(π / 2)) = -cos θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ sin (↑x✝ - ↑(π / 2)) = -cos ↑x✝
  exact Real.sin_sub_pi_div_two _
  -- 🎉 no goals
#align real.angle.sin_sub_pi_div_two Real.Angle.sin_sub_pi_div_two

theorem sin_pi_div_two_sub (θ : Angle) : sin (↑(π / 2) - θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ sin (↑(π / 2) - ↑x✝) = cos ↑x✝
  exact Real.sin_pi_div_two_sub _
  -- 🎉 no goals
#align real.angle.sin_pi_div_two_sub Real.Angle.sin_pi_div_two_sub

theorem cos_add_pi_div_two (θ : Angle) : cos (θ + ↑(π / 2)) = -sin θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos (↑x✝ + ↑(π / 2)) = -sin ↑x✝
  exact Real.cos_add_pi_div_two _
  -- 🎉 no goals
#align real.angle.cos_add_pi_div_two Real.Angle.cos_add_pi_div_two

theorem cos_sub_pi_div_two (θ : Angle) : cos (θ - ↑(π / 2)) = sin θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos (↑x✝ - ↑(π / 2)) = sin ↑x✝
  exact Real.cos_sub_pi_div_two _
  -- 🎉 no goals
#align real.angle.cos_sub_pi_div_two Real.Angle.cos_sub_pi_div_two

theorem cos_pi_div_two_sub (θ : Angle) : cos (↑(π / 2) - θ) = sin θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ cos (↑(π / 2) - ↑x✝) = sin ↑x✝
  exact Real.cos_pi_div_two_sub _
  -- 🎉 no goals
#align real.angle.cos_pi_div_two_sub Real.Angle.cos_pi_div_two_sub

theorem abs_sin_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |sin θ| = |sin ψ| := by
  rw [two_nsmul_eq_iff] at h
  -- ⊢ |sin θ| = |sin ψ|
  rcases h with (rfl | rfl)
  -- ⊢ |sin θ| = |sin θ|
  · rfl
    -- 🎉 no goals
  · rw [sin_add_pi, abs_neg]
    -- 🎉 no goals
#align real.angle.abs_sin_eq_of_two_nsmul_eq Real.Angle.abs_sin_eq_of_two_nsmul_eq

theorem abs_sin_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |sin θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  -- ⊢ |sin θ| = |sin ψ|
  exact abs_sin_eq_of_two_nsmul_eq h
  -- 🎉 no goals
#align real.angle.abs_sin_eq_of_two_zsmul_eq Real.Angle.abs_sin_eq_of_two_zsmul_eq

theorem abs_cos_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |cos θ| = |cos ψ| := by
  rw [two_nsmul_eq_iff] at h
  -- ⊢ |cos θ| = |cos ψ|
  rcases h with (rfl | rfl)
  -- ⊢ |cos θ| = |cos θ|
  · rfl
    -- 🎉 no goals
  · rw [cos_add_pi, abs_neg]
    -- 🎉 no goals
#align real.angle.abs_cos_eq_of_two_nsmul_eq Real.Angle.abs_cos_eq_of_two_nsmul_eq

theorem abs_cos_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |cos θ| = |cos ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  -- ⊢ |cos θ| = |cos ψ|
  exact abs_cos_eq_of_two_nsmul_eq h
  -- 🎉 no goals
#align real.angle.abs_cos_eq_of_two_zsmul_eq Real.Angle.abs_cos_eq_of_two_zsmul_eq

@[simp]
theorem coe_toIcoMod (θ ψ : ℝ) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  -- ⊢ ∃ k, toIcoMod two_pi_pos ψ θ - θ = 2 * π * ↑k
  refine' ⟨-toIcoDiv two_pi_pos ψ θ, _⟩
  -- ⊢ toIcoMod two_pi_pos ψ θ - θ = 2 * π * ↑(-toIcoDiv two_pi_pos ψ θ)
  rw [toIcoMod_sub_self, zsmul_eq_mul, mul_comm]
  -- 🎉 no goals
#align real.angle.coe_to_Ico_mod Real.Angle.coe_toIcoMod

@[simp]
theorem coe_toIocMod (θ ψ : ℝ) : ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  -- ⊢ ∃ k, toIocMod two_pi_pos ψ θ - θ = 2 * π * ↑k
  refine' ⟨-toIocDiv two_pi_pos ψ θ, _⟩
  -- ⊢ toIocMod two_pi_pos ψ θ - θ = 2 * π * ↑(-toIocDiv two_pi_pos ψ θ)
  rw [toIocMod_sub_self, zsmul_eq_mul, mul_comm]
  -- 🎉 no goals
#align real.angle.coe_to_Ioc_mod Real.Angle.coe_toIocMod

/-- Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`. -/
def toReal (θ : Angle) : ℝ :=
  (toIocMod_periodic two_pi_pos (-π)).lift θ
#align real.angle.to_real Real.Angle.toReal

theorem toReal_coe (θ : ℝ) : (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ :=
  rfl
#align real.angle.to_real_coe Real.Angle.toReal_coe

theorem toReal_coe_eq_self_iff {θ : ℝ} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ ≤ π := by
  rw [toReal_coe, toIocMod_eq_self two_pi_pos]
  -- ⊢ θ ∈ Set.Ioc (-π) (-π + 2 * π) ↔ -π < θ ∧ θ ≤ π
  ring_nf
  -- ⊢ θ ∈ Set.Ioc (-π) π ↔ -π < θ ∧ θ ≤ π
  rfl
  -- 🎉 no goals
#align real.angle.to_real_coe_eq_self_iff Real.Angle.toReal_coe_eq_self_iff

theorem toReal_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : Angle).toReal = θ ↔ θ ∈ Set.Ioc (-π) π := by
  rw [toReal_coe_eq_self_iff, ← Set.mem_Ioc]
  -- 🎉 no goals
#align real.angle.to_real_coe_eq_self_iff_mem_Ioc Real.Angle.toReal_coe_eq_self_iff_mem_Ioc

theorem toReal_injective : Function.Injective toReal := by
  intro θ ψ h
  -- ⊢ θ = ψ
  induction θ using Real.Angle.induction_on
  -- ⊢ ↑x✝ = ψ
  induction ψ using Real.Angle.induction_on
  -- ⊢ ↑x✝¹ = ↑x✝
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h
#align real.angle.to_real_injective Real.Angle.toReal_injective

@[simp]
theorem toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  toReal_injective.eq_iff
#align real.angle.to_real_inj Real.Angle.toReal_inj

@[simp]
theorem coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ ↑(toReal ↑x✝) = ↑x✝
  exact coe_toIocMod _ _
  -- 🎉 no goals
#align real.angle.coe_to_real Real.Angle.coe_toReal

theorem neg_pi_lt_toReal (θ : Angle) : -π < θ.toReal := by
  induction θ using Real.Angle.induction_on
  -- ⊢ -π < toReal ↑x✝
  exact left_lt_toIocMod _ _ _
  -- 🎉 no goals
#align real.angle.neg_pi_lt_to_real Real.Angle.neg_pi_lt_toReal

theorem toReal_le_pi (θ : Angle) : θ.toReal ≤ π := by
  induction θ using Real.Angle.induction_on
  -- ⊢ toReal ↑x✝ ≤ π
  convert toIocMod_le_right two_pi_pos _ _
  -- ⊢ π = -π + 2 * π
  ring
  -- 🎉 no goals
#align real.angle.to_real_le_pi Real.Angle.toReal_le_pi

theorem abs_toReal_le_pi (θ : Angle) : |θ.toReal| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩
#align real.angle.abs_to_real_le_pi Real.Angle.abs_toReal_le_pi

theorem toReal_mem_Ioc (θ : Angle) : θ.toReal ∈ Set.Ioc (-π) π :=
  ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩
#align real.angle.to_real_mem_Ioc Real.Angle.toReal_mem_Ioc

@[simp]
theorem toIocMod_toReal (θ : Angle) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal := by
  induction θ using Real.Angle.induction_on
  -- ⊢ toIocMod two_pi_pos (-π) (toReal ↑x✝) = toReal ↑x✝
  rw [toReal_coe]
  -- ⊢ toIocMod two_pi_pos (-π) (toIocMod two_pi_pos (-π) x✝) = toIocMod two_pi_pos …
  exact toIocMod_toIocMod _ _ _ _
  -- 🎉 no goals
#align real.angle.to_Ioc_mod_to_real Real.Angle.toIocMod_toReal

@[simp]
theorem toReal_zero : (0 : Angle).toReal = 0 := by
  rw [← coe_zero, toReal_coe_eq_self_iff]
  -- ⊢ -π < 0 ∧ 0 ≤ π
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩
  -- 🎉 no goals
#align real.angle.to_real_zero Real.Angle.toReal_zero

@[simp]
theorem toReal_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0 := by
  nth_rw 1 [← toReal_zero]
  -- ⊢ toReal θ = toReal 0 ↔ θ = 0
  exact toReal_inj
  -- 🎉 no goals
#align real.angle.to_real_eq_zero_iff Real.Angle.toReal_eq_zero_iff

@[simp]
theorem toReal_pi : (π : Angle).toReal = π := by
  rw [toReal_coe_eq_self_iff]
  -- ⊢ -π < π ∧ π ≤ π
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩
  -- 🎉 no goals
#align real.angle.to_real_pi Real.Angle.toReal_pi

@[simp]
theorem toReal_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π := by rw [← toReal_inj, toReal_pi]
                                                                  -- 🎉 no goals
#align real.angle.to_real_eq_pi_iff Real.Angle.toReal_eq_pi_iff

theorem pi_ne_zero : (π : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi, toReal_zero]
  -- ⊢ π ≠ 0
  exact Real.pi_ne_zero
  -- 🎉 no goals
#align real.angle.pi_ne_zero Real.Angle.pi_ne_zero

@[simp]
theorem toReal_pi_div_two : ((π / 2 : ℝ) : Angle).toReal = π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]
                                 -- ⊢ -π < π / 2
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align real.angle.to_real_pi_div_two Real.Angle.toReal_pi_div_two

@[simp]
theorem toReal_eq_pi_div_two_iff {θ : Angle} : θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_pi_div_two]
  -- 🎉 no goals
#align real.angle.to_real_eq_pi_div_two_iff Real.Angle.toReal_eq_pi_div_two_iff

@[simp]
theorem toReal_neg_pi_div_two : ((-π / 2 : ℝ) : Angle).toReal = -π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]
                                 -- ⊢ -π < -π / 2
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
#align real.angle.to_real_neg_pi_div_two Real.Angle.toReal_neg_pi_div_two

@[simp]
theorem toReal_eq_neg_pi_div_two_iff {θ : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_neg_pi_div_two]
  -- 🎉 no goals
#align real.angle.to_real_eq_neg_pi_div_two_iff Real.Angle.toReal_eq_neg_pi_div_two_iff

theorem pi_div_two_ne_zero : ((π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi_div_two, toReal_zero]
  -- ⊢ π / 2 ≠ 0
  exact div_ne_zero Real.pi_ne_zero two_ne_zero
  -- 🎉 no goals
#align real.angle.pi_div_two_ne_zero Real.Angle.pi_div_two_ne_zero

theorem neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_neg_pi_div_two, toReal_zero]
  -- ⊢ -π / 2 ≠ 0
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero
  -- 🎉 no goals
#align real.angle.neg_pi_div_two_ne_zero Real.Angle.neg_pi_div_two_ne_zero

theorem abs_toReal_coe_eq_self_iff {θ : ℝ} : |(θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩
#align real.angle.abs_to_real_coe_eq_self_iff Real.Angle.abs_toReal_coe_eq_self_iff

theorem abs_toReal_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π := by
  refine' ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => _⟩
  -- ⊢ |toReal (-↑θ)| = θ
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  -- ⊢ |toReal (-↑θ)| = θ
                             -- 🎉 no goals
  rw [← coe_neg,
    toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi), (neg_nonpos.2 h.1).trans Real.pi_pos.le⟩,
    abs_neg, abs_eq_self.2 h.1]
#align real.angle.abs_to_real_neg_coe_eq_self_iff Real.Angle.abs_toReal_neg_coe_eq_self_iff

theorem abs_toReal_eq_pi_div_two_iff {θ : Angle} :
    |θ.toReal| = π / 2 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le), ← neg_div, toReal_eq_pi_div_two_iff,
    toReal_eq_neg_pi_div_two_iff]
#align real.angle.abs_to_real_eq_pi_div_two_iff Real.Angle.abs_toReal_eq_pi_div_two_iff

theorem nsmul_toReal_eq_mul {n : ℕ} (h : n ≠ 0) {θ : Angle} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / n) (π / n) := by
  nth_rw 1 [← coe_toReal θ]
  -- ⊢ toReal (n • ↑(toReal θ)) = ↑n * toReal θ ↔ toReal θ ∈ Set.Ioc (-π / ↑n) (π / …
  have h' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
  -- ⊢ toReal (n • ↑(toReal θ)) = ↑n * toReal θ ↔ toReal θ ∈ Set.Ioc (-π / ↑n) (π / …
  rw [← coe_nsmul, nsmul_eq_mul, toReal_coe_eq_self_iff, Set.mem_Ioc, div_lt_iff' h',
    le_div_iff' h']
#align real.angle.nsmul_to_real_eq_mul Real.Angle.nsmul_toReal_eq_mul

theorem two_nsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) := by
  exact_mod_cast nsmul_toReal_eq_mul two_ne_zero
  -- 🎉 no goals
#align real.angle.two_nsmul_to_real_eq_two_mul Real.Angle.two_nsmul_toReal_eq_two_mul

theorem two_zsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul]
  -- 🎉 no goals
#align real.angle.two_zsmul_to_real_eq_two_mul Real.Angle.two_zsmul_toReal_eq_two_mul

theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
    (θ : Angle).toReal = θ - 2 * k * π ↔ θ ∈ Set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) := by
  rw [← sub_zero (θ : Angle), ← zsmul_zero k, ← coe_two_pi, ← coe_zsmul, ← coe_sub, zsmul_eq_mul, ←
    mul_assoc, mul_comm (k : ℝ), toReal_coe_eq_self_iff, Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩
  -- 🎉 no goals
#align real.angle.to_real_coe_eq_self_sub_two_mul_int_mul_pi_iff Real.Angle.toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff

theorem toReal_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ - 2 * π ↔ θ ∈ Set.Ioc π (3 * π) := by
  convert @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
                                                                 -- 🎉 no goals
#align real.angle.to_real_coe_eq_self_sub_two_pi_iff Real.Angle.toReal_coe_eq_self_sub_two_pi_iff

theorem toReal_coe_eq_self_add_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ + 2 * π ↔ θ ∈ Set.Ioc (-3 * π) (-π) := by
  convert @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num
  -- ⊢ θ + 2 * π = θ - 2 * ↑(-1) * π
                                                                            -- 🎉 no goals
                                                                            -- 🎉 no goals
#align real.angle.to_real_coe_eq_self_add_two_pi_iff Real.Angle.toReal_coe_eq_self_add_two_pi_iff

theorem two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  nth_rw 1 [← coe_toReal θ]
  -- ⊢ toReal (2 • ↑(toReal θ)) = 2 * toReal θ - 2 * π ↔ π / 2 < toReal θ
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_sub_two_pi_iff, Set.mem_Ioc]
  -- ⊢ π < 2 * toReal θ ∧ 2 * toReal θ ≤ 3 * π ↔ π / 2 < toReal θ
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff' (zero_lt_two' ℝ)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩
#align real.angle.two_nsmul_to_real_eq_two_mul_sub_two_pi Real.Angle.two_nsmul_toReal_eq_two_mul_sub_two_pi

theorem two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_sub_two_pi]
  -- 🎉 no goals
#align real.angle.two_zsmul_to_real_eq_two_mul_sub_two_pi Real.Angle.two_zsmul_toReal_eq_two_mul_sub_two_pi

theorem two_nsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  -- ⊢ toReal (2 • ↑(toReal θ)) = 2 * toReal θ + 2 * π ↔ toReal θ ≤ -π / 2
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_add_two_pi_iff, Set.mem_Ioc]
  -- ⊢ -3 * π < 2 * toReal θ ∧ 2 * toReal θ ≤ -π ↔ toReal θ ≤ -π / 2
  refine'
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff' (zero_lt_two' ℝ)).1 h⟩⟩
#align real.angle.two_nsmul_to_real_eq_two_mul_add_two_pi Real.Angle.two_nsmul_toReal_eq_two_mul_add_two_pi

theorem two_zsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_add_two_pi]
  -- 🎉 no goals
#align real.angle.two_zsmul_to_real_eq_two_mul_add_two_pi Real.Angle.two_zsmul_toReal_eq_two_mul_add_two_pi

@[simp]
theorem sin_toReal (θ : Angle) : Real.sin θ.toReal = sin θ := by
  conv_rhs => rw [← coe_toReal θ, sin_coe]
  -- 🎉 no goals
#align real.angle.sin_to_real Real.Angle.sin_toReal

@[simp]
theorem cos_toReal (θ : Angle) : Real.cos θ.toReal = cos θ := by
  conv_rhs => rw [← coe_toReal θ, cos_coe]
  -- 🎉 no goals
#align real.angle.cos_to_real Real.Angle.cos_toReal

theorem cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : Angle} : 0 ≤ cos θ ↔ |θ.toReal| ≤ π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  -- ⊢ 0 ≤ cos ↑(toReal θ) ↔ |toReal θ| ≤ π / 2
  rw [abs_le, cos_coe]
  -- ⊢ 0 ≤ Real.cos (toReal θ) ↔ -(π / 2) ≤ toReal θ ∧ toReal θ ≤ π / 2
  refine' ⟨fun h => _, cos_nonneg_of_mem_Icc⟩
  -- ⊢ -(π / 2) ≤ toReal θ ∧ toReal θ ≤ π / 2
  by_contra hn
  -- ⊢ False
  rw [not_and_or, not_le, not_le] at hn
  -- ⊢ False
  refine' (not_lt.2 h) _
  -- ⊢ Real.cos (toReal θ) < 0
  rcases hn with (hn | hn)
  -- ⊢ Real.cos (toReal θ) < 0
  · rw [← Real.cos_neg]
    -- ⊢ Real.cos (-toReal θ) < 0
    refine' cos_neg_of_pi_div_two_lt_of_lt (by linarith) _
    -- ⊢ -toReal θ < π + π / 2
    linarith [neg_pi_lt_toReal θ]
    -- 🎉 no goals
  · refine' cos_neg_of_pi_div_two_lt_of_lt hn _
    -- ⊢ toReal θ < π + π / 2
    linarith [toReal_le_pi θ]
    -- 🎉 no goals
#align real.angle.cos_nonneg_iff_abs_to_real_le_pi_div_two Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two

theorem cos_pos_iff_abs_toReal_lt_pi_div_two {θ : Angle} : 0 < cos θ ↔ |θ.toReal| < π / 2 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, cos_nonneg_iff_abs_toReal_le_pi_div_two, ←
    and_congr_right]
  rintro -
  -- ⊢ |toReal θ| ≠ π / 2 ↔ 0 ≠ cos θ
  rw [Ne.def, Ne.def, not_iff_not, @eq_comm ℝ 0, abs_toReal_eq_pi_div_two_iff, cos_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.cos_pos_iff_abs_to_real_lt_pi_div_two Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two

theorem cos_neg_iff_pi_div_two_lt_abs_toReal {θ : Angle} : cos θ < 0 ↔ π / 2 < |θ.toReal| := by
  rw [← not_le, ← not_le, not_iff_not, cos_nonneg_iff_abs_toReal_le_pi_div_two]
  -- 🎉 no goals
#align real.angle.cos_neg_iff_pi_div_two_lt_abs_to_real Real.Angle.cos_neg_iff_pi_div_two_lt_abs_toReal

theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| := by
  rw [← eq_sub_iff_add_eq, ← two_nsmul_coe_div_two, ← nsmul_sub, two_nsmul_eq_iff] at h
  -- ⊢ |cos θ| = |sin ψ|
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]
  -- ⊢ |cos (↑(π / 2) - ψ)| = |sin ψ|
                                -- 🎉 no goals
                                -- 🎉 no goals
#align real.angle.abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi Real.Angle.abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi

theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  -- ⊢ |cos θ| = |sin ψ|
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h
  -- 🎉 no goals
#align real.angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi

/-- The tangent of a `Real.Angle`. -/
def tan (θ : Angle) : ℝ :=
  sin θ / cos θ
#align real.angle.tan Real.Angle.tan

theorem tan_eq_sin_div_cos (θ : Angle) : tan θ = sin θ / cos θ :=
  rfl
#align real.angle.tan_eq_sin_div_cos Real.Angle.tan_eq_sin_div_cos

@[simp]
theorem tan_coe (x : ℝ) : tan (x : Angle) = Real.tan x := by
  rw [tan, sin_coe, cos_coe, Real.tan_eq_sin_div_cos]
  -- 🎉 no goals
#align real.angle.tan_coe Real.Angle.tan_coe

@[simp]
theorem tan_zero : tan (0 : Angle) = 0 := by rw [← coe_zero, tan_coe, Real.tan_zero]
                                             -- 🎉 no goals
#align real.angle.tan_zero Real.Angle.tan_zero

-- Porting note: @[simp] can now prove it
theorem tan_coe_pi : tan (π : Angle) = 0 := by rw [tan_coe, Real.tan_pi]
                                               -- 🎉 no goals
#align real.angle.tan_coe_pi Real.Angle.tan_coe_pi

theorem tan_periodic : Function.Periodic tan (π : Angle) := by
  intro θ
  -- ⊢ tan (θ + ↑π) = tan θ
  induction θ using Real.Angle.induction_on
  -- ⊢ tan (↑x✝ + ↑π) = tan ↑x✝
  rw [← coe_add, tan_coe, tan_coe]
  -- ⊢ Real.tan (x✝ + π) = Real.tan x✝
  exact Real.tan_periodic _
  -- 🎉 no goals
#align real.angle.tan_periodic Real.Angle.tan_periodic

@[simp]
theorem tan_add_pi (θ : Angle) : tan (θ + π) = tan θ :=
  tan_periodic θ
#align real.angle.tan_add_pi Real.Angle.tan_add_pi

@[simp]
theorem tan_sub_pi (θ : Angle) : tan (θ - π) = tan θ :=
  tan_periodic.sub_eq θ
#align real.angle.tan_sub_pi Real.Angle.tan_sub_pi

@[simp]
theorem tan_toReal (θ : Angle) : Real.tan θ.toReal = tan θ := by
  conv_rhs => rw [← coe_toReal θ, tan_coe]
  -- 🎉 no goals
#align real.angle.tan_to_real Real.Angle.tan_toReal

theorem tan_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ := by
  rw [two_nsmul_eq_iff] at h
  -- ⊢ tan θ = tan ψ
  rcases h with (rfl | rfl)
  -- ⊢ tan θ = tan θ
  · rfl
    -- 🎉 no goals
  · exact tan_add_pi _
    -- 🎉 no goals
#align real.angle.tan_eq_of_two_nsmul_eq Real.Angle.tan_eq_of_two_nsmul_eq

theorem tan_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  -- ⊢ tan θ = tan ψ
  exact tan_eq_of_two_nsmul_eq h
  -- 🎉 no goals
#align real.angle.tan_eq_of_two_zsmul_eq Real.Angle.tan_eq_of_two_zsmul_eq

theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  -- ⊢ tan ψ = (tan ↑x✝)⁻¹
  induction ψ using Real.Angle.induction_on
  -- ⊢ tan ↑x✝ = (tan ↑x✝¹)⁻¹
  rw [← smul_add, ← coe_add, ← coe_nsmul, two_nsmul, ← two_mul, angle_eq_iff_two_pi_dvd_sub] at h
  -- ⊢ tan ↑x✝ = (tan ↑x✝¹)⁻¹
  rcases h with ⟨k, h⟩
  -- ⊢ tan ↑x✝ = (tan ↑x✝¹)⁻¹
  rw [sub_eq_iff_eq_add, ← mul_inv_cancel_left₀ two_ne_zero π, mul_assoc, ← mul_add,
    mul_right_inj' (two_ne_zero' ℝ), ← eq_sub_iff_add_eq', mul_inv_cancel_left₀ two_ne_zero π,
    inv_mul_eq_div, mul_comm] at h
  rw [tan_coe, tan_coe, ← tan_pi_div_two_sub, h, add_sub_assoc, add_comm]
  -- ⊢ Real.tan (π / 2 - x✝¹ + ↑k * π) = Real.tan (π / 2 - x✝¹)
  exact Real.tan_periodic.int_mul _ _
  -- 🎉 no goals
#align real.angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi Real.Angle.tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi

theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  -- ⊢ tan ψ = (tan θ)⁻¹
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h
  -- 🎉 no goals
#align real.angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi

/-- The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : Angle) : SignType :=
  SignType.sign (sin θ)
#align real.angle.sign Real.Angle.sign

@[simp]
theorem sign_zero : (0 : Angle).sign = 0 := by
  rw [sign, sin_zero, _root_.sign_zero]
  -- 🎉 no goals
#align real.angle.sign_zero Real.Angle.sign_zero

@[simp]
theorem sign_coe_pi : (π : Angle).sign = 0 := by rw [sign, sin_coe_pi, _root_.sign_zero]
                                                 -- 🎉 no goals
#align real.angle.sign_coe_pi Real.Angle.sign_coe_pi

@[simp]
theorem sign_neg (θ : Angle) : (-θ).sign = -θ.sign := by
  simp_rw [sign, sin_neg, Left.sign_neg]
  -- 🎉 no goals
#align real.angle.sign_neg Real.Angle.sign_neg

theorem sign_antiperiodic : Function.Antiperiodic sign (π : Angle) := fun θ => by
  rw [sign, sign, sin_add_pi, Left.sign_neg]
  -- 🎉 no goals
#align real.angle.sign_antiperiodic Real.Angle.sign_antiperiodic

@[simp]
theorem sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign :=
  sign_antiperiodic θ
#align real.angle.sign_add_pi Real.Angle.sign_add_pi

@[simp]
theorem sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign := by rw [add_comm, sign_add_pi]
                                                                         -- 🎉 no goals
#align real.angle.sign_pi_add Real.Angle.sign_pi_add

@[simp]
theorem sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign :=
  sign_antiperiodic.sub_eq θ
#align real.angle.sign_sub_pi Real.Angle.sign_sub_pi

@[simp]
theorem sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign := by
  simp [sign_antiperiodic.sub_eq']
  -- 🎉 no goals
#align real.angle.sign_pi_sub Real.Angle.sign_pi_sub

theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign, _root_.sign_eq_zero_iff, sin_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.sign_eq_zero_iff Real.Angle.sign_eq_zero_iff

theorem sign_ne_zero_iff {θ : Angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sign_eq_zero_iff]
  -- 🎉 no goals
#align real.angle.sign_ne_zero_iff Real.Angle.sign_ne_zero_iff

theorem toReal_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1 := by
  rw [sign, ← sin_toReal, sign_eq_neg_one_iff]
  -- ⊢ toReal θ < 0 ↔ Real.sin (toReal θ) < 0
  rcases lt_trichotomy θ.toReal 0 with (h | h | h)
  · exact ⟨fun _ => Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_toReal θ), fun _ => h⟩
    -- 🎉 no goals
  · simp [h]
    -- 🎉 no goals
  · exact
      ⟨fun hn => False.elim (h.asymm hn), fun hn =>
        False.elim (hn.not_le (sin_nonneg_of_nonneg_of_le_pi h.le (toReal_le_pi θ)))⟩
#align real.angle.to_real_neg_iff_sign_neg Real.Angle.toReal_neg_iff_sign_neg

theorem toReal_nonneg_iff_sign_nonneg {θ : Angle} : 0 ≤ θ.toReal ↔ 0 ≤ θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (h | h | h)
  · refine' ⟨fun hn => False.elim (h.not_le hn), fun hn => _⟩
    -- ⊢ 0 ≤ toReal θ
    rw [toReal_neg_iff_sign_neg.1 h] at hn
    -- ⊢ 0 ≤ toReal θ
    exact False.elim (hn.not_lt (by decide))
    -- 🎉 no goals
  · simp [h, sign, ← sin_toReal]
    -- 🎉 no goals
  · refine' ⟨fun _ => _, fun _ => h.le⟩
    -- ⊢ 0 ≤ sign θ
    rw [sign, ← sin_toReal, sign_nonneg_iff]
    -- ⊢ 0 ≤ Real.sin (toReal θ)
    exact sin_nonneg_of_nonneg_of_le_pi h.le (toReal_le_pi θ)
    -- 🎉 no goals
#align real.angle.to_real_nonneg_iff_sign_nonneg Real.Angle.toReal_nonneg_iff_sign_nonneg

@[simp]
theorem sign_toReal {θ : Angle} (h : θ ≠ π) : SignType.sign θ.toReal = θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
    -- 🎉 no goals
  · simp [sign, ht, ← sin_toReal]
    -- 🎉 no goals
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]
#align real.angle.sign_to_real Real.Angle.sign_toReal

theorem coe_abs_toReal_of_sign_nonneg {θ : Angle} (h : 0 ≤ θ.sign) : ↑|θ.toReal| = θ := by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h), coe_toReal]
  -- 🎉 no goals
#align real.angle.coe_abs_to_real_of_sign_nonneg Real.Angle.coe_abs_toReal_of_sign_nonneg

theorem neg_coe_abs_toReal_of_sign_nonpos {θ : Angle} (h : θ.sign ≤ 0) : -↑|θ.toReal| = θ := by
  rw [SignType.nonpos_iff] at h
  -- ⊢ -↑|toReal θ| = θ
  rcases h with (h | h)
  -- ⊢ -↑|toReal θ| = θ
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
    -- 🎉 no goals
  · rw [sign_eq_zero_iff] at h
    -- ⊢ -↑|toReal θ| = θ
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]
    -- ⊢ -↑|toReal 0| = 0
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align real.angle.neg_coe_abs_to_real_of_sign_nonpos Real.Angle.neg_coe_abs_toReal_of_sign_nonpos

theorem eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : Angle} :
    θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal| := by
  refine' ⟨_, fun h => _⟩;
  -- ⊢ θ = ψ → sign θ = sign ψ ∧ |toReal θ| = |toReal ψ|
  · rintro rfl
    -- ⊢ sign θ = sign θ ∧ |toReal θ| = |toReal θ|
    exact ⟨rfl, rfl⟩
    -- 🎉 no goals
  rcases h with ⟨hs, hr⟩
  -- ⊢ θ = ψ
  rw [abs_eq_abs] at hr
  -- ⊢ θ = ψ
  rcases hr with (hr | hr)
  -- ⊢ θ = ψ
  · exact toReal_injective hr
    -- 🎉 no goals
  · by_cases h : θ = π
    -- ⊢ θ = ψ
    · rw [h, toReal_pi, ← neg_eq_iff_eq_neg] at hr
      -- ⊢ θ = ψ
      exact False.elim ((neg_pi_lt_toReal ψ).ne hr)
      -- 🎉 no goals
    · by_cases h' : ψ = π
      -- ⊢ θ = ψ
      · rw [h', toReal_pi] at hr
        -- ⊢ θ = ψ
        exact False.elim ((neg_pi_lt_toReal θ).ne hr.symm)
        -- 🎉 no goals
      · rw [← sign_toReal h, ← sign_toReal h', hr, Left.sign_neg, SignType.neg_eq_self_iff,
          _root_.sign_eq_zero_iff, toReal_eq_zero_iff] at hs
        rw [hs, toReal_zero, neg_zero, toReal_eq_zero_iff] at hr
        -- ⊢ θ = ψ
        rw [hr, hs]
        -- 🎉 no goals
#align real.angle.eq_iff_sign_eq_and_abs_to_real_eq Real.Angle.eq_iff_sign_eq_and_abs_toReal_eq

theorem eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) :
    θ = ψ ↔ |θ.toReal| = |ψ.toReal| := by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ
                                          -- 🎉 no goals
#align real.angle.eq_iff_abs_to_real_eq_of_sign_eq Real.Angle.eq_iff_abs_toReal_eq_of_sign_eq

@[simp]
theorem sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1 := by
  rw [sign, sin_coe, sin_pi_div_two, sign_one]
  -- 🎉 no goals
#align real.angle.sign_coe_pi_div_two Real.Angle.sign_coe_pi_div_two

@[simp]
theorem sign_coe_neg_pi_div_two : (↑(-π / 2) : Angle).sign = -1 := by
  rw [sign, sin_coe, neg_div, Real.sin_neg, sin_pi_div_two, Left.sign_neg, sign_one]
  -- 🎉 no goals
#align real.angle.sign_coe_neg_pi_div_two Real.Angle.sign_coe_neg_pi_div_two

theorem sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    0 ≤ (θ : Angle).sign := by
  rw [sign, sign_nonneg_iff]
  -- ⊢ 0 ≤ sin ↑θ
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
  -- 🎉 no goals
#align real.angle.sign_coe_nonneg_of_nonneg_of_le_pi Real.Angle.sign_coe_nonneg_of_nonneg_of_le_pi

theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    (-θ : Angle).sign ≤ 0 := by
  rw [sign, sign_nonpos_iff, sin_neg, Left.neg_nonpos_iff]
  -- ⊢ 0 ≤ sin ↑θ
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi
  -- 🎉 no goals
#align real.angle.sign_neg_coe_nonpos_of_nonneg_of_le_pi Real.Angle.sign_neg_coe_nonpos_of_nonneg_of_le_pi

theorem sign_two_nsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℕ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  by_cases hpi : θ = π; · simp [hpi]
  -- ⊢ sign (2 • θ) = sign θ ↔ θ = ↑π ∨ |toReal θ| < π / 2
                          -- 🎉 no goals
  rw [or_iff_right hpi]
  -- ⊢ sign (2 • θ) = sign θ ↔ |toReal θ| < π / 2
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ |toReal θ| < π / 2
  · by_contra hle
    -- ⊢ False
    rw [not_lt, le_abs, le_neg] at hle
    -- ⊢ False
    have hpi' : θ.toReal ≠ π := by simpa using hpi
    -- ⊢ False
    rcases hle with (hle | hle) <;> rcases hle.eq_or_lt with (heq | hlt)
    -- ⊢ False
                                    -- ⊢ False
                                    -- ⊢ False
    · rw [← coe_toReal θ, ← heq] at h
      -- ⊢ False
      simp at h
      -- 🎉 no goals
    · rw [← sign_toReal hpi, sign_pos (pi_div_two_pos.trans hlt), ← sign_toReal,
        two_nsmul_toReal_eq_two_mul_sub_two_pi.2 hlt, _root_.sign_neg] at h
      · simp at h
        -- 🎉 no goals
      · rw [← mul_sub]
        -- ⊢ 2 * (toReal θ - π) < 0
        exact mul_neg_of_pos_of_neg two_pos (sub_neg.2 ((toReal_le_pi _).lt_of_ne hpi'))
        -- 🎉 no goals
      · intro he
        -- ⊢ False
        simp [he] at h
        -- 🎉 no goals
    · rw [← coe_toReal θ, heq] at h
      -- ⊢ False
      simp at h
      -- 🎉 no goals
    · rw [← sign_toReal hpi, _root_.sign_neg (hlt.trans (Left.neg_neg_iff.2 pi_div_two_pos)), ←
        sign_toReal] at h
      swap
      -- ⊢ 2 • θ ≠ ↑π
      · intro he
        -- ⊢ False
        simp [he] at h
        -- 🎉 no goals
      rw [← neg_div] at hlt
      -- ⊢ False
      rw [two_nsmul_toReal_eq_two_mul_add_two_pi.2 hlt.le, sign_pos] at h
      -- ⊢ False
      · simp at h
        -- 🎉 no goals
      · linarith [neg_pi_lt_toReal θ]
        -- 🎉 no goals
  · have hpi' : (2 : ℕ) • θ ≠ π := by
      rw [Ne.def, two_nsmul_eq_pi_iff, not_or]
      constructor
      · rintro rfl
        simp [pi_pos, div_pos, abs_of_pos] at h
      · rintro rfl
        rw [toReal_neg_pi_div_two] at h
        simp [pi_pos, div_pos, neg_div, abs_of_pos] at h
    rw [abs_lt, ← neg_div] at h
    -- ⊢ sign (2 • θ) = sign θ
    rw [← sign_toReal hpi, ← sign_toReal hpi', two_nsmul_toReal_eq_two_mul.2 ⟨h.1, h.2.le⟩,
      sign_mul, sign_pos (zero_lt_two' ℝ), one_mul]
#align real.angle.sign_two_nsmul_eq_sign_iff Real.Angle.sign_two_nsmul_eq_sign_iff

theorem sign_two_zsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℤ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  rw [two_zsmul, ← two_nsmul, sign_two_nsmul_eq_sign_iff]
  -- 🎉 no goals
#align real.angle.sign_two_zsmul_eq_sign_iff Real.Angle.sign_two_zsmul_eq_sign_iff

theorem continuousAt_sign {θ : Angle} (h0 : θ ≠ 0) (hpi : θ ≠ π) : ContinuousAt sign θ :=
  (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt
#align real.angle.continuous_at_sign Real.Angle.continuousAt_sign

theorem _root_.ContinuousOn.angle_sign_comp {α : Type*} [TopologicalSpace α] {f : α → Angle}
    {s : Set α} (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
    ContinuousOn (sign ∘ f) s := by
  refine' (ContinuousAt.continuousOn fun θ hθ => _).comp hf (Set.mapsTo_image f s)
  -- ⊢ ContinuousAt sign θ
  obtain ⟨z, hz, rfl⟩ := hθ
  -- ⊢ ContinuousAt sign (f z)
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2
  -- 🎉 no goals
#align continuous_on.angle_sign_comp ContinuousOn.angle_sign_comp

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
theorem sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α → Angle} {s : Set α}
    {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
    (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
  (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)
#align real.angle.sign_eq_of_continuous_on Real.Angle.sign_eq_of_continuousOn

end Angle

end Real
