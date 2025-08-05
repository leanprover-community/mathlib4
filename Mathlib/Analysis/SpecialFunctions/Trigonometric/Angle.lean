/-
Copyright (c) 2019 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.CharZero.Quotient
import Mathlib.Topology.Instances.Sign

/-!
# The type of angles

In this file we define `Real.Angle` to be the quotient group `ℝ/2πℤ` and prove a few simple lemmas
about trigonometric functions and angles.
-/


open Real

noncomputable section

namespace Real

/-- The type of angles -/
def Angle : Type :=
  AddCircle (2 * π)
-- The `NormedAddCommGroup, Inhabited` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

namespace Angle

instance : NormedAddCommGroup Angle :=
  inferInstanceAs (NormedAddCommGroup (AddCircle (2 * π)))

instance : Inhabited Angle :=
  inferInstanceAs (Inhabited (AddCircle (2 * π)))

/-- The canonical map from `ℝ` to the quotient `Angle`. -/
@[coe]
protected def coe (r : ℝ) : Angle := QuotientAddGroup.mk r

instance : Coe ℝ Angle := ⟨Angle.coe⟩

instance : CircularOrder Real.Angle :=
  QuotientAddGroup.circularOrder (hp' := ⟨by simp [pi_pos]⟩)


@[continuity]
theorem continuous_coe : Continuous ((↑) : ℝ → Angle) :=
  continuous_quotient_mk'

/-- Coercion `ℝ → Angle` as an additive homomorphism. -/
def coeHom : ℝ →+ Angle :=
  QuotientAddGroup.mk' _

@[simp]
theorem coe_coeHom : (coeHom : ℝ → Angle) = ((↑) : ℝ → Angle) :=
  rfl

/-- An induction principle to deduce results for `Angle` from those for `ℝ`, used with
`induction θ using Real.Angle.induction_on`. -/
@[elab_as_elim]
protected theorem induction_on {p : Angle → Prop} (θ : Angle) (h : ∀ x : ℝ, p x) : p θ :=
  Quotient.inductionOn' θ h

@[simp]
theorem coe_zero : ↑(0 : ℝ) = (0 : Angle) :=
  rfl

@[simp]
theorem coe_add (x y : ℝ) : ↑(x + y : ℝ) = (↑x + ↑y : Angle) :=
  rfl

@[simp]
theorem coe_neg (x : ℝ) : ↑(-x : ℝ) = -(↑x : Angle) :=
  rfl

@[simp]
theorem coe_sub (x y : ℝ) : ↑(x - y : ℝ) = (↑x - ↑y : Angle) :=
  rfl

theorem coe_nsmul (n : ℕ) (x : ℝ) : ↑(n • x : ℝ) = n • (↑x : Angle) :=
  rfl

theorem coe_zsmul (z : ℤ) (x : ℝ) : ↑(z • x : ℝ) = z • (↑x : Angle) :=
  rfl

theorem coe_eq_zero_iff {x : ℝ} : (x : Angle) = 0 ↔ ∃ n : ℤ, n • (2 * π) = x :=
  AddCircle.coe_eq_zero_iff (2 * π)

@[simp, norm_cast]
theorem natCast_mul_eq_nsmul (x : ℝ) (n : ℕ) : ↑((n : ℝ) * x) = n • (↑x : Angle) := by
  simpa only [nsmul_eq_mul] using coeHom.map_nsmul x n

@[simp, norm_cast]
theorem intCast_mul_eq_zsmul (x : ℝ) (n : ℤ) : ↑((n : ℝ) * x : ℝ) = n • (↑x : Angle) := by
  simpa only [zsmul_eq_mul] using coeHom.map_zsmul x n

theorem angle_eq_iff_two_pi_dvd_sub {ψ θ : ℝ} : (θ : Angle) = ψ ↔ ∃ k : ℤ, θ - ψ = 2 * π * k := by
  simp only [eq_comm]
  rw [Angle.coe, Angle.coe, QuotientAddGroup.eq]
  simp only [AddSubgroup.zmultiples_eq_closure,
    AddSubgroup.mem_closure_singleton, zsmul_eq_mul', (sub_eq_neg_add _ _).symm, eq_comm]

@[simp]
theorem coe_two_pi : ↑(2 * π : ℝ) = (0 : Angle) :=
  angle_eq_iff_two_pi_dvd_sub.2 ⟨1, by rw [sub_zero, Int.cast_one, mul_one]⟩

@[simp]
theorem neg_coe_pi : -(π : Angle) = π := by
  rw [← coe_neg, angle_eq_iff_two_pi_dvd_sub]
  use -1
  simp [two_mul, sub_eq_add_neg]

@[simp]
theorem two_nsmul_coe_div_two (θ : ℝ) : (2 : ℕ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_nsmul, two_nsmul, add_halves]

@[simp]
theorem two_zsmul_coe_div_two (θ : ℝ) : (2 : ℤ) • (↑(θ / 2) : Angle) = θ := by
  rw [← coe_zsmul, two_zsmul, add_halves]

theorem two_nsmul_neg_pi_div_two : (2 : ℕ) • (↑(-π / 2) : Angle) = π := by
  rw [two_nsmul_coe_div_two, coe_neg, neg_coe_pi]

theorem two_zsmul_neg_pi_div_two : (2 : ℤ) • (↑(-π / 2) : Angle) = π := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_neg_pi_div_two]

theorem sub_coe_pi_eq_add_coe_pi (θ : Angle) : θ - π = θ + π := by
  rw [sub_eq_add_neg, neg_coe_pi]

@[simp]
theorem two_nsmul_coe_pi : (2 : ℕ) • (π : Angle) = 0 := by simp [← natCast_mul_eq_nsmul]

@[simp]
theorem two_zsmul_coe_pi : (2 : ℤ) • (π : Angle) = 0 := by simp [← intCast_mul_eq_zsmul]

@[simp]
theorem coe_pi_add_coe_pi : (π : Real.Angle) + π = 0 := by rw [← two_nsmul, two_nsmul_coe_pi]

theorem zsmul_eq_iff {ψ θ : Angle} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (2 * π / z : ℝ) :=
  QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff hz

theorem nsmul_eq_iff {ψ θ : Angle} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (2 * π / n : ℝ) :=
  QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hz

theorem two_zsmul_eq_iff {ψ θ : Angle} : (2 : ℤ) • ψ = (2 : ℤ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  have : Int.natAbs 2 = 2 := rfl
  rw [zsmul_eq_iff two_ne_zero, this, Fin.exists_fin_two, Fin.val_zero,
    Fin.val_one, zero_smul, add_zero, one_smul, Int.cast_two,
    mul_div_cancel_left₀ (_ : ℝ) two_ne_zero]

theorem two_nsmul_eq_iff {ψ θ : Angle} : (2 : ℕ) • ψ = (2 : ℕ) • θ ↔ ψ = θ ∨ ψ = θ + ↑π := by
  simp_rw [← natCast_zsmul, Nat.cast_ofNat, two_zsmul_eq_iff]

theorem two_nsmul_eq_zero_iff {θ : Angle} : (2 : ℕ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  convert two_nsmul_eq_iff <;> simp

theorem two_nsmul_ne_zero_iff {θ : Angle} : (2 : ℕ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_nsmul_eq_zero_iff]

theorem two_zsmul_eq_zero_iff {θ : Angle} : (2 : ℤ) • θ = 0 ↔ θ = 0 ∨ θ = π := by
  simp_rw [two_zsmul, ← two_nsmul, two_nsmul_eq_zero_iff]

theorem two_zsmul_ne_zero_iff {θ : Angle} : (2 : ℤ) • θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← two_zsmul_eq_zero_iff]

theorem eq_neg_self_iff {θ : Angle} : θ = -θ ↔ θ = 0 ∨ θ = π := by
  rw [← add_eq_zero_iff_eq_neg, ← two_nsmul, two_nsmul_eq_zero_iff]

theorem ne_neg_self_iff {θ : Angle} : θ ≠ -θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← eq_neg_self_iff.not]

theorem neg_eq_self_iff {θ : Angle} : -θ = θ ↔ θ = 0 ∨ θ = π := by rw [eq_comm, eq_neg_self_iff]

theorem neg_ne_self_iff {θ : Angle} : -θ ≠ θ ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← neg_eq_self_iff.not]

theorem two_nsmul_eq_pi_iff {θ : Angle} : (2 : ℕ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  have h : (π : Angle) = ((2 : ℕ) • (π / 2 : ℝ):) := by rw [two_nsmul, add_halves]
  nth_rw 1 [h]
  rw [coe_nsmul, two_nsmul_eq_iff]
  -- Porting note: `congr` didn't simplify the goal of iff of `Or`s
  convert Iff.rfl
  rw [add_comm, ← coe_add, ← sub_eq_zero, ← coe_sub, neg_div, ← neg_sub, sub_neg_eq_add, add_assoc,
    add_halves, ← two_mul, coe_neg, coe_two_pi, neg_zero]

theorem two_zsmul_eq_pi_iff {θ : Angle} : (2 : ℤ) • θ = π ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_eq_pi_iff]

theorem cos_eq_iff_coe_eq_or_eq_neg {θ ψ : ℝ} :
    cos θ = cos ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) = -ψ := by
  constructor
  · intro Hcos
    rw [← sub_eq_zero, cos_sub_cos, mul_eq_zero, mul_eq_zero, neg_eq_zero,
      eq_false (two_ne_zero' ℝ), false_or, sin_eq_zero_iff, sin_eq_zero_iff] at Hcos
    rcases Hcos with (⟨n, hn⟩ | ⟨n, hn⟩)
    · right
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), ← sub_eq_iff_eq_add] at hn
      rw [← hn, coe_sub, eq_neg_iff_add_eq_zero, sub_add_cancel, mul_assoc, intCast_mul_eq_zsmul,
        mul_comm, coe_two_pi, zsmul_zero]
    · left
      rw [eq_div_iff_mul_eq (two_ne_zero' ℝ), eq_sub_iff_add_eq] at hn
      rw [← hn, coe_add, mul_assoc, intCast_mul_eq_zsmul, mul_comm, coe_two_pi, zsmul_zero,
        zero_add]
  · rw [angle_eq_iff_two_pi_dvd_sub, ← coe_neg, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, cos_sub_cos, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' ℝ),
        mul_comm π _, sin_int_mul_pi, mul_zero]
    rw [← sub_eq_zero, cos_sub_cos, ← sub_neg_eq_add, H, mul_assoc 2 π k,
      mul_div_cancel_left₀ _ (two_ne_zero' ℝ), mul_comm π _, sin_int_mul_pi, mul_zero,
      zero_mul]

theorem sin_eq_iff_coe_eq_or_add_eq_pi {θ ψ : ℝ} :
    sin θ = sin ψ ↔ (θ : Angle) = ψ ∨ (θ : Angle) + ψ = π := by
  constructor
  · intro Hsin
    rw [← cos_pi_div_two_sub, ← cos_pi_div_two_sub] at Hsin
    rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hsin with h | h
    · left
      rw [coe_sub, coe_sub] at h
      exact sub_right_inj.1 h
    right
    rw [coe_sub, coe_sub, eq_neg_iff_add_eq_zero, add_sub, sub_add_eq_add_sub, ← coe_add,
      add_halves, sub_sub, sub_eq_zero] at h
    exact h.symm
  · rw [angle_eq_iff_two_pi_dvd_sub, ← eq_sub_iff_add_eq, ← coe_sub, angle_eq_iff_two_pi_dvd_sub]
    rintro (⟨k, H⟩ | ⟨k, H⟩)
    · rw [← sub_eq_zero, sin_sub_sin, H, mul_assoc 2 π k, mul_div_cancel_left₀ _ (two_ne_zero' ℝ),
        mul_comm π _, sin_int_mul_pi, mul_zero, zero_mul]
    have H' : θ + ψ = 2 * k * π + π := by
      rwa [← sub_add, sub_add_eq_add_sub, sub_eq_iff_eq_add, mul_assoc, mul_comm π _, ←
        mul_assoc] at H
    rw [← sub_eq_zero, sin_sub_sin, H', add_div, mul_assoc 2 _ π,
      mul_div_cancel_left₀ _ (two_ne_zero' ℝ), cos_add_pi_div_two, sin_int_mul_pi, neg_zero,
      mul_zero]

theorem cos_sin_inj {θ ψ : ℝ} (Hcos : cos θ = cos ψ) (Hsin : sin θ = sin ψ) : (θ : Angle) = ψ := by
  rcases cos_eq_iff_coe_eq_or_eq_neg.mp Hcos with hc | hc; · exact hc
  rcases sin_eq_iff_coe_eq_or_add_eq_pi.mp Hsin with hs | hs; · exact hs
  rw [eq_neg_iff_add_eq_zero, hs] at hc
  obtain ⟨n, hn⟩ : ∃ n, n • _ = _ := QuotientAddGroup.leftRel_apply.mp (Quotient.exact' hc)
  rw [← neg_one_mul, add_zero, ← sub_eq_zero, zsmul_eq_mul, ← mul_assoc, ← sub_mul, mul_eq_zero,
    eq_false (ne_of_gt pi_pos), or_false, sub_neg_eq_add, ← Int.cast_zero, ← Int.cast_one,
    ← Int.cast_ofNat, ← Int.cast_mul, ← Int.cast_add, Int.cast_inj] at hn
  have : (n * 2 + 1) % (2 : ℤ) = 0 % (2 : ℤ) := congr_arg (· % (2 : ℤ)) hn
  rw [add_comm, Int.add_mul_emod_self_right] at this
  exact absurd this one_ne_zero

/-- The sine of a `Real.Angle`. -/
def sin (θ : Angle) : ℝ :=
  sin_periodic.lift θ

@[simp]
theorem sin_coe (x : ℝ) : sin (x : Angle) = Real.sin x :=
  rfl

@[continuity]
theorem continuous_sin : Continuous sin :=
  Real.continuous_sin.quotient_liftOn' _

/-- The cosine of a `Real.Angle`. -/
def cos (θ : Angle) : ℝ :=
  cos_periodic.lift θ

@[simp]
theorem cos_coe (x : ℝ) : cos (x : Angle) = Real.cos x :=
  rfl

@[continuity]
theorem continuous_cos : Continuous cos :=
  Real.continuous_cos.quotient_liftOn' _

theorem cos_eq_real_cos_iff_eq_or_eq_neg {θ : Angle} {ψ : ℝ} :
    cos θ = Real.cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction θ using Real.Angle.induction_on
  exact cos_eq_iff_coe_eq_or_eq_neg

theorem cos_eq_iff_eq_or_eq_neg {θ ψ : Angle} : cos θ = cos ψ ↔ θ = ψ ∨ θ = -ψ := by
  induction ψ using Real.Angle.induction_on
  exact cos_eq_real_cos_iff_eq_or_eq_neg

theorem sin_eq_real_sin_iff_eq_or_add_eq_pi {θ : Angle} {ψ : ℝ} :
    sin θ = Real.sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction θ using Real.Angle.induction_on
  exact sin_eq_iff_coe_eq_or_add_eq_pi

theorem sin_eq_iff_eq_or_add_eq_pi {θ ψ : Angle} : sin θ = sin ψ ↔ θ = ψ ∨ θ + ψ = π := by
  induction ψ using Real.Angle.induction_on
  exact sin_eq_real_sin_iff_eq_or_add_eq_pi

@[simp]
theorem sin_zero : sin (0 : Angle) = 0 := by rw [← coe_zero, sin_coe, Real.sin_zero]

theorem sin_coe_pi : sin (π : Angle) = 0 := by rw [sin_coe, Real.sin_pi]

theorem sin_eq_zero_iff {θ : Angle} : sin θ = 0 ↔ θ = 0 ∨ θ = π := by
  nth_rw 1 [← sin_zero]
  rw [sin_eq_iff_eq_or_add_eq_pi]
  simp

theorem sin_ne_zero_iff {θ : Angle} : sin θ ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sin_eq_zero_iff]

@[simp]
theorem sin_neg (θ : Angle) : sin (-θ) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_neg _

theorem sin_antiperiodic : Function.Antiperiodic sin (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.sin_antiperiodic _

@[simp]
theorem sin_add_pi (θ : Angle) : sin (θ + π) = -sin θ :=
  sin_antiperiodic θ

@[simp]
theorem sin_sub_pi (θ : Angle) : sin (θ - π) = -sin θ :=
  sin_antiperiodic.sub_eq θ

@[simp]
theorem cos_zero : cos (0 : Angle) = 1 := by rw [← coe_zero, cos_coe, Real.cos_zero]

theorem cos_coe_pi : cos (π : Angle) = -1 := by rw [cos_coe, Real.cos_pi]

@[simp]
theorem cos_neg (θ : Angle) : cos (-θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_neg _

theorem cos_antiperiodic : Function.Antiperiodic cos (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  exact Real.cos_antiperiodic _

@[simp]
theorem cos_add_pi (θ : Angle) : cos (θ + π) = -cos θ :=
  cos_antiperiodic θ

@[simp]
theorem cos_sub_pi (θ : Angle) : cos (θ - π) = -cos θ :=
  cos_antiperiodic.sub_eq θ

theorem cos_eq_zero_iff {θ : Angle} : cos θ = 0 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [← cos_pi_div_two, ← cos_coe, cos_eq_iff_eq_or_eq_neg, ← coe_neg, ← neg_div]

theorem sin_add (θ₁ θ₂ : Real.Angle) : sin (θ₁ + θ₂) = sin θ₁ * cos θ₂ + cos θ₁ * sin θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact Real.sin_add _ _

theorem cos_add (θ₁ θ₂ : Real.Angle) : cos (θ₁ + θ₂) = cos θ₁ * cos θ₂ - sin θ₁ * sin θ₂ := by
  induction θ₂ using Real.Angle.induction_on
  induction θ₁ using Real.Angle.induction_on
  exact Real.cos_add _ _

@[simp]
theorem cos_sq_add_sin_sq (θ : Real.Angle) : cos θ ^ 2 + sin θ ^ 2 = 1 := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sq_add_sin_sq _

theorem sin_add_pi_div_two (θ : Angle) : sin (θ + ↑(π / 2)) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_add_pi_div_two _

theorem sin_sub_pi_div_two (θ : Angle) : sin (θ - ↑(π / 2)) = -cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_sub_pi_div_two _

theorem sin_pi_div_two_sub (θ : Angle) : sin (↑(π / 2) - θ) = cos θ := by
  induction θ using Real.Angle.induction_on
  exact Real.sin_pi_div_two_sub _

theorem cos_add_pi_div_two (θ : Angle) : cos (θ + ↑(π / 2)) = -sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_add_pi_div_two _

theorem cos_sub_pi_div_two (θ : Angle) : cos (θ - ↑(π / 2)) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_sub_pi_div_two _

theorem cos_pi_div_two_sub (θ : Angle) : cos (↑(π / 2) - θ) = sin θ := by
  induction θ using Real.Angle.induction_on
  exact Real.cos_pi_div_two_sub _

theorem abs_sin_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |sin θ| = |sin ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [sin_add_pi, abs_neg]

theorem abs_sin_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |sin θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_sin_eq_of_two_nsmul_eq h

theorem abs_cos_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) :
    |cos θ| = |cos ψ| := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · rw [cos_add_pi, abs_neg]

theorem abs_cos_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) :
    |cos θ| = |cos ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_of_two_nsmul_eq h

@[simp]
theorem coe_toIcoMod (θ ψ : ℝ) : ↑(toIcoMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIcoDiv two_pi_pos ψ θ, ?_⟩
  rw [toIcoMod_sub_self, zsmul_eq_mul, mul_comm]

@[simp]
theorem coe_toIocMod (θ ψ : ℝ) : ↑(toIocMod two_pi_pos ψ θ) = (θ : Angle) := by
  rw [angle_eq_iff_two_pi_dvd_sub]
  refine ⟨-toIocDiv two_pi_pos ψ θ, ?_⟩
  rw [toIocMod_sub_self, zsmul_eq_mul, mul_comm]

/-- Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`. -/
def toReal (θ : Angle) : ℝ :=
  (toIocMod_periodic two_pi_pos (-π)).lift θ

theorem toReal_coe (θ : ℝ) : (θ : Angle).toReal = toIocMod two_pi_pos (-π) θ :=
  rfl

theorem toReal_coe_eq_self_iff {θ : ℝ} : (θ : Angle).toReal = θ ↔ -π < θ ∧ θ ≤ π := by
  rw [toReal_coe, toIocMod_eq_self two_pi_pos]
  ring_nf
  rfl

theorem toReal_coe_eq_self_iff_mem_Ioc {θ : ℝ} : (θ : Angle).toReal = θ ↔ θ ∈ Set.Ioc (-π) π := by
  rw [toReal_coe_eq_self_iff, ← Set.mem_Ioc]

theorem toReal_injective : Function.Injective toReal := by
  intro θ ψ h
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  simpa [toReal_coe, toIocMod_eq_toIocMod, zsmul_eq_mul, mul_comm _ (2 * π), ←
    angle_eq_iff_two_pi_dvd_sub, eq_comm] using h

@[simp]
theorem toReal_inj {θ ψ : Angle} : θ.toReal = ψ.toReal ↔ θ = ψ :=
  toReal_injective.eq_iff

@[simp]
theorem coe_toReal (θ : Angle) : (θ.toReal : Angle) = θ := by
  induction θ using Real.Angle.induction_on
  exact coe_toIocMod _ _

theorem neg_pi_lt_toReal (θ : Angle) : -π < θ.toReal := by
  induction θ using Real.Angle.induction_on
  exact left_lt_toIocMod _ _ _

theorem toReal_le_pi (θ : Angle) : θ.toReal ≤ π := by
  induction θ using Real.Angle.induction_on
  convert toIocMod_le_right two_pi_pos _ _
  ring

theorem abs_toReal_le_pi (θ : Angle) : |θ.toReal| ≤ π :=
  abs_le.2 ⟨(neg_pi_lt_toReal _).le, toReal_le_pi _⟩

theorem toReal_mem_Ioc (θ : Angle) : θ.toReal ∈ Set.Ioc (-π) π :=
  ⟨neg_pi_lt_toReal _, toReal_le_pi _⟩

@[simp]
theorem toIocMod_toReal (θ : Angle) : toIocMod two_pi_pos (-π) θ.toReal = θ.toReal := by
  induction θ using Real.Angle.induction_on
  rw [toReal_coe]
  exact toIocMod_toIocMod _ _ _ _

@[simp]
theorem toReal_zero : (0 : Angle).toReal = 0 := by
  rw [← coe_zero, toReal_coe_eq_self_iff]
  exact ⟨Left.neg_neg_iff.2 Real.pi_pos, Real.pi_pos.le⟩

@[simp]
theorem toReal_eq_zero_iff {θ : Angle} : θ.toReal = 0 ↔ θ = 0 := by
  nth_rw 1 [← toReal_zero]
  exact toReal_inj

@[simp]
theorem toReal_pi : (π : Angle).toReal = π := by
  rw [toReal_coe_eq_self_iff]
  exact ⟨Left.neg_lt_self Real.pi_pos, le_refl _⟩

@[simp]
theorem toReal_eq_pi_iff {θ : Angle} : θ.toReal = π ↔ θ = π := by rw [← toReal_inj, toReal_pi]

theorem pi_ne_zero : (π : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi, toReal_zero]
  exact Real.pi_ne_zero

@[simp]
theorem toReal_pi_div_two : ((π / 2 : ℝ) : Angle).toReal = π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]

@[simp]
theorem toReal_eq_pi_div_two_iff {θ : Angle} : θ.toReal = π / 2 ↔ θ = (π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_pi_div_two]

@[simp]
theorem toReal_neg_pi_div_two : ((-π / 2 : ℝ) : Angle).toReal = -π / 2 :=
  toReal_coe_eq_self_iff.2 <| by constructor <;> linarith [pi_pos]

@[simp]
theorem toReal_eq_neg_pi_div_two_iff {θ : Angle} : θ.toReal = -π / 2 ↔ θ = (-π / 2 : ℝ) := by
  rw [← toReal_inj, toReal_neg_pi_div_two]

theorem pi_div_two_ne_zero : ((π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_pi_div_two, toReal_zero]
  exact div_ne_zero Real.pi_ne_zero two_ne_zero

theorem neg_pi_div_two_ne_zero : ((-π / 2 : ℝ) : Angle) ≠ 0 := by
  rw [← toReal_injective.ne_iff, toReal_neg_pi_div_two, toReal_zero]
  exact div_ne_zero (neg_ne_zero.2 Real.pi_ne_zero) two_ne_zero

theorem abs_toReal_coe_eq_self_iff {θ : ℝ} : |(θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π :=
  ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h =>
    (toReal_coe_eq_self_iff.2 ⟨(Left.neg_neg_iff.2 Real.pi_pos).trans_le h.1, h.2⟩).symm ▸
      abs_eq_self.2 h.1⟩

theorem abs_toReal_neg_coe_eq_self_iff {θ : ℝ} : |(-θ : Angle).toReal| = θ ↔ 0 ≤ θ ∧ θ ≤ π := by
  refine ⟨fun h => h ▸ ⟨abs_nonneg _, abs_toReal_le_pi _⟩, fun h => ?_⟩
  by_cases hnegpi : θ = π; · simp [hnegpi, Real.pi_pos.le]
  rw [← coe_neg,
    toReal_coe_eq_self_iff.2
      ⟨neg_lt_neg (lt_of_le_of_ne h.2 hnegpi), (neg_nonpos.2 h.1).trans Real.pi_pos.le⟩,
    abs_neg, abs_eq_self.2 h.1]

theorem abs_toReal_eq_pi_div_two_iff {θ : Angle} :
    |θ.toReal| = π / 2 ↔ θ = (π / 2 : ℝ) ∨ θ = (-π / 2 : ℝ) := by
  rw [abs_eq (div_nonneg Real.pi_pos.le two_pos.le), ← neg_div, toReal_eq_pi_div_two_iff,
    toReal_eq_neg_pi_div_two_iff]

theorem nsmul_toReal_eq_mul {n : ℕ} (h : n ≠ 0) {θ : Angle} :
    (n • θ).toReal = n * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / n) (π / n) := by
  nth_rw 1 [← coe_toReal θ]
  have h' : 0 < (n : ℝ) := mod_cast Nat.pos_of_ne_zero h
  rw [← coe_nsmul, nsmul_eq_mul, toReal_coe_eq_self_iff, Set.mem_Ioc, div_lt_iff₀' h',
    le_div_iff₀' h']

theorem two_nsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) :=
  mod_cast nsmul_toReal_eq_mul two_ne_zero

theorem two_zsmul_toReal_eq_two_mul {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal ↔ θ.toReal ∈ Set.Ioc (-π / 2) (π / 2) := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul]

theorem toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff {θ : ℝ} {k : ℤ} :
    (θ : Angle).toReal = θ - 2 * k * π ↔ θ ∈ Set.Ioc ((2 * k - 1 : ℝ) * π) ((2 * k + 1) * π) := by
  rw [← sub_zero (θ : Angle), ← zsmul_zero k, ← coe_two_pi, ← coe_zsmul, ← coe_sub, zsmul_eq_mul, ←
    mul_assoc, mul_comm (k : ℝ), toReal_coe_eq_self_iff, Set.mem_Ioc]
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun h => ⟨by linarith, by linarith⟩⟩

theorem toReal_coe_eq_self_sub_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ - 2 * π ↔ θ ∈ Set.Ioc π (3 * π) := by
  convert @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ 1 <;> norm_num

theorem toReal_coe_eq_self_add_two_pi_iff {θ : ℝ} :
    (θ : Angle).toReal = θ + 2 * π ↔ θ ∈ Set.Ioc (-3 * π) (-π) := by
  convert @toReal_coe_eq_self_sub_two_mul_int_mul_pi_iff θ (-1) using 2 <;> norm_num

theorem two_nsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_sub_two_pi_iff, Set.mem_Ioc]
  exact
    ⟨fun h => by linarith, fun h =>
      ⟨(div_lt_iff₀' (zero_lt_two' ℝ)).1 h, by linarith [pi_pos, toReal_le_pi θ]⟩⟩

theorem two_zsmul_toReal_eq_two_mul_sub_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal - 2 * π ↔ π / 2 < θ.toReal := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_sub_two_pi]

theorem two_nsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℕ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  rw [← coe_nsmul, two_nsmul, ← two_mul, toReal_coe_eq_self_add_two_pi_iff, Set.mem_Ioc]
  refine
    ⟨fun h => by linarith, fun h =>
      ⟨by linarith [pi_pos, neg_pi_lt_toReal θ], (le_div_iff₀' (zero_lt_two' ℝ)).1 h⟩⟩

theorem two_zsmul_toReal_eq_two_mul_add_two_pi {θ : Angle} :
    ((2 : ℤ) • θ).toReal = 2 * θ.toReal + 2 * π ↔ θ.toReal ≤ -π / 2 := by
  rw [two_zsmul, ← two_nsmul, two_nsmul_toReal_eq_two_mul_add_two_pi]

@[simp]
theorem sin_toReal (θ : Angle) : Real.sin θ.toReal = sin θ := by
  conv_rhs => rw [← coe_toReal θ, sin_coe]

@[simp]
theorem cos_toReal (θ : Angle) : Real.cos θ.toReal = cos θ := by
  conv_rhs => rw [← coe_toReal θ, cos_coe]

theorem cos_nonneg_iff_abs_toReal_le_pi_div_two {θ : Angle} : 0 ≤ cos θ ↔ |θ.toReal| ≤ π / 2 := by
  nth_rw 1 [← coe_toReal θ]
  rw [abs_le, cos_coe]
  refine ⟨fun h => ?_, cos_nonneg_of_mem_Icc⟩
  by_contra hn
  rw [not_and_or, not_le, not_le] at hn
  refine (not_lt.2 h) ?_
  rcases hn with (hn | hn)
  · rw [← Real.cos_neg]
    refine cos_neg_of_pi_div_two_lt_of_lt (by linarith) ?_
    linarith [neg_pi_lt_toReal θ]
  · refine cos_neg_of_pi_div_two_lt_of_lt hn ?_
    linarith [toReal_le_pi θ]

theorem cos_pos_iff_abs_toReal_lt_pi_div_two {θ : Angle} : 0 < cos θ ↔ |θ.toReal| < π / 2 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, cos_nonneg_iff_abs_toReal_le_pi_div_two, ←
    and_congr_right]
  rintro -
  rw [Ne, Ne, not_iff_not, @eq_comm ℝ 0, abs_toReal_eq_pi_div_two_iff, cos_eq_zero_iff]

theorem cos_neg_iff_pi_div_two_lt_abs_toReal {θ : Angle} : cos θ < 0 ↔ π / 2 < |θ.toReal| := by
  rw [← not_le, ← not_le, not_iff_not, cos_nonneg_iff_abs_toReal_le_pi_div_two]

theorem abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : |cos θ| = |sin ψ| := by
  rw [← eq_sub_iff_add_eq, ← two_nsmul_coe_div_two, ← nsmul_sub, two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl) <;> simp [cos_pi_div_two_sub]

theorem abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : |cos θ| = |sin ψ| := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact abs_cos_eq_abs_sin_of_two_nsmul_add_two_nsmul_eq_pi h

/-- The tangent of a `Real.Angle`. -/
def tan (θ : Angle) : ℝ :=
  sin θ / cos θ

theorem tan_eq_sin_div_cos (θ : Angle) : tan θ = sin θ / cos θ :=
  rfl

@[simp]
theorem tan_coe (x : ℝ) : tan (x : Angle) = Real.tan x := by
  rw [tan, sin_coe, cos_coe, Real.tan_eq_sin_div_cos]

@[simp]
theorem tan_zero : tan (0 : Angle) = 0 := by rw [← coe_zero, tan_coe, Real.tan_zero]

theorem tan_coe_pi : tan (π : Angle) = 0 := by rw [tan_coe, Real.tan_pi]

theorem tan_periodic : Function.Periodic tan (π : Angle) := by
  intro θ
  induction θ using Real.Angle.induction_on
  rw [← coe_add, tan_coe, tan_coe]
  exact Real.tan_periodic _

@[simp]
theorem tan_add_pi (θ : Angle) : tan (θ + π) = tan θ :=
  tan_periodic θ

@[simp]
theorem tan_sub_pi (θ : Angle) : tan (θ - π) = tan θ :=
  tan_periodic.sub_eq θ

@[simp]
theorem tan_toReal (θ : Angle) : Real.tan θ.toReal = tan θ := by
  conv_rhs => rw [← coe_toReal θ, tan_coe]

theorem tan_eq_of_two_nsmul_eq {θ ψ : Angle} (h : (2 : ℕ) • θ = (2 : ℕ) • ψ) : tan θ = tan ψ := by
  rw [two_nsmul_eq_iff] at h
  rcases h with (rfl | rfl)
  · rfl
  · exact tan_add_pi _

theorem tan_eq_of_two_zsmul_eq {θ ψ : Angle} (h : (2 : ℤ) • θ = (2 : ℤ) • ψ) : tan θ = tan ψ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_of_two_nsmul_eq h

theorem tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℕ) • θ + (2 : ℕ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  rw [← smul_add, ← coe_add, ← coe_nsmul, two_nsmul, ← two_mul, angle_eq_iff_two_pi_dvd_sub] at h
  rcases h with ⟨k, h⟩
  rw [sub_eq_iff_eq_add, ← mul_inv_cancel_left₀ two_ne_zero π, mul_assoc, ← mul_add,
    mul_right_inj' (two_ne_zero' ℝ), ← eq_sub_iff_add_eq', mul_inv_cancel_left₀ two_ne_zero π,
    inv_mul_eq_div, mul_comm] at h
  rw [tan_coe, tan_coe, ← tan_pi_div_two_sub, h, add_sub_assoc, add_comm]
  exact Real.tan_periodic.int_mul _ _

theorem tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi {θ ψ : Angle}
    (h : (2 : ℤ) • θ + (2 : ℤ) • ψ = π) : tan ψ = (tan θ)⁻¹ := by
  simp_rw [two_zsmul, ← two_nsmul] at h
  exact tan_eq_inv_of_two_nsmul_add_two_nsmul_eq_pi h

/-- The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly
between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the
sign of the sine of the angle. -/
def sign (θ : Angle) : SignType :=
  SignType.sign (sin θ)

@[simp]
theorem sign_zero : (0 : Angle).sign = 0 := by
  rw [sign, sin_zero, _root_.sign_zero]

@[simp]
theorem sign_coe_pi : (π : Angle).sign = 0 := by rw [sign, sin_coe_pi, _root_.sign_zero]

@[simp]
theorem sign_neg (θ : Angle) : (-θ).sign = -θ.sign := by
  simp_rw [sign, sin_neg, Left.sign_neg]

theorem sign_antiperiodic : Function.Antiperiodic sign (π : Angle) := fun θ => by
  rw [sign, sign, sin_add_pi, Left.sign_neg]

@[simp]
theorem sign_add_pi (θ : Angle) : (θ + π).sign = -θ.sign :=
  sign_antiperiodic θ

@[simp]
theorem sign_pi_add (θ : Angle) : ((π : Angle) + θ).sign = -θ.sign := by rw [add_comm, sign_add_pi]

@[simp]
theorem sign_sub_pi (θ : Angle) : (θ - π).sign = -θ.sign :=
  sign_antiperiodic.sub_eq θ

@[simp]
theorem sign_pi_sub (θ : Angle) : ((π : Angle) - θ).sign = θ.sign := by
  simp [sign_antiperiodic.sub_eq']

theorem sign_eq_zero_iff {θ : Angle} : θ.sign = 0 ↔ θ = 0 ∨ θ = π := by
  rw [sign, _root_.sign_eq_zero_iff, sin_eq_zero_iff]

theorem sign_ne_zero_iff {θ : Angle} : θ.sign ≠ 0 ↔ θ ≠ 0 ∧ θ ≠ π := by
  rw [← not_or, ← sign_eq_zero_iff]

theorem toReal_neg_iff_sign_neg {θ : Angle} : θ.toReal < 0 ↔ θ.sign = -1 := by
  rw [sign, ← sin_toReal, sign_eq_neg_one_iff]
  rcases lt_trichotomy θ.toReal 0 with (h | h | h)
  · exact ⟨fun _ => Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_toReal θ), fun _ => h⟩
  · simp [h]
  · exact
      ⟨fun hn => False.elim (h.asymm hn), fun hn =>
        False.elim (hn.not_ge (sin_nonneg_of_nonneg_of_le_pi h.le (toReal_le_pi θ)))⟩

theorem toReal_nonneg_iff_sign_nonneg {θ : Angle} : 0 ≤ θ.toReal ↔ 0 ≤ θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (h | h | h)
  · refine ⟨fun hn => False.elim (h.not_ge hn), fun hn => ?_⟩
    rw [toReal_neg_iff_sign_neg.1 h] at hn
    exact False.elim (hn.not_gt (by decide))
  · simp [h, sign, ← sin_toReal]
  · refine ⟨fun _ => ?_, fun _ => h.le⟩
    rw [sign, ← sin_toReal, sign_nonneg_iff]
    exact sin_nonneg_of_nonneg_of_le_pi h.le (toReal_le_pi θ)

@[simp]
theorem sign_toReal {θ : Angle} (h : θ ≠ π) : SignType.sign θ.toReal = θ.sign := by
  rcases lt_trichotomy θ.toReal 0 with (ht | ht | ht)
  · simp [ht, toReal_neg_iff_sign_neg.1 ht]
  · simp [sign, ht, ← sin_toReal]
  · rw [sign, ← sin_toReal, sign_pos ht,
      sign_pos
        (sin_pos_of_pos_of_lt_pi ht ((toReal_le_pi θ).lt_of_ne (toReal_eq_pi_iff.not.2 h)))]

theorem coe_abs_toReal_of_sign_nonneg {θ : Angle} (h : 0 ≤ θ.sign) : ↑|θ.toReal| = θ := by
  rw [abs_eq_self.2 (toReal_nonneg_iff_sign_nonneg.2 h), coe_toReal]

theorem neg_coe_abs_toReal_of_sign_nonpos {θ : Angle} (h : θ.sign ≤ 0) : -↑|θ.toReal| = θ := by
  rw [SignType.nonpos_iff] at h
  rcases h with (h | h)
  · rw [abs_of_neg (toReal_neg_iff_sign_neg.2 h), coe_neg, neg_neg, coe_toReal]
  · rw [sign_eq_zero_iff] at h
    rcases h with (rfl | rfl) <;> simp [abs_of_pos Real.pi_pos]

theorem eq_iff_sign_eq_and_abs_toReal_eq {θ ψ : Angle} :
    θ = ψ ↔ θ.sign = ψ.sign ∧ |θ.toReal| = |ψ.toReal| := by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl
    exact ⟨rfl, rfl⟩
  rcases h with ⟨hs, hr⟩
  rw [abs_eq_abs] at hr
  rcases hr with (hr | hr)
  · exact toReal_injective hr
  · by_cases h : θ = π
    · rw [h, toReal_pi, ← neg_eq_iff_eq_neg] at hr
      exact False.elim ((neg_pi_lt_toReal ψ).ne hr)
    · by_cases h' : ψ = π
      · rw [h', toReal_pi] at hr
        exact False.elim ((neg_pi_lt_toReal θ).ne hr.symm)
      · rw [← sign_toReal h, ← sign_toReal h', hr, Left.sign_neg, SignType.neg_eq_self_iff,
          _root_.sign_eq_zero_iff, toReal_eq_zero_iff] at hs
        rw [hs, toReal_zero, neg_zero, toReal_eq_zero_iff] at hr
        rw [hr, hs]

theorem eq_iff_abs_toReal_eq_of_sign_eq {θ ψ : Angle} (h : θ.sign = ψ.sign) :
    θ = ψ ↔ |θ.toReal| = |ψ.toReal| := by simpa [h] using @eq_iff_sign_eq_and_abs_toReal_eq θ ψ

@[simp]
theorem sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1 := by
  rw [sign, sin_coe, sin_pi_div_two, sign_one]

@[simp]
theorem sign_coe_neg_pi_div_two : (↑(-π / 2) : Angle).sign = -1 := by
  rw [sign, sin_coe, neg_div, Real.sin_neg, sin_pi_div_two, Left.sign_neg, sign_one]

theorem sign_coe_nonneg_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    0 ≤ (θ : Angle).sign := by
  rw [sign, sign_nonneg_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

theorem sign_neg_coe_nonpos_of_nonneg_of_le_pi {θ : ℝ} (h0 : 0 ≤ θ) (hpi : θ ≤ π) :
    (-θ : Angle).sign ≤ 0 := by
  rw [sign, sign_nonpos_iff, sin_neg, Left.neg_nonpos_iff]
  exact sin_nonneg_of_nonneg_of_le_pi h0 hpi

theorem sign_two_nsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℕ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  by_cases hpi : θ = π; · simp [hpi]
  rw [or_iff_right hpi]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hle
    rw [not_lt, le_abs, le_neg] at hle
    have hpi' : θ.toReal ≠ π := by simpa using hpi
    rcases hle with (hle | hle) <;> rcases hle.eq_or_lt with (heq | hlt)
    · rw [← coe_toReal θ, ← heq] at h
      simp at h
    · rw [← sign_toReal hpi, sign_pos (pi_div_two_pos.trans hlt), ← sign_toReal,
        two_nsmul_toReal_eq_two_mul_sub_two_pi.2 hlt, _root_.sign_neg] at h
      · simp at h
      · rw [← mul_sub]
        exact mul_neg_of_pos_of_neg two_pos (sub_neg.2 ((toReal_le_pi _).lt_of_ne hpi'))
      · intro he
        simp [he] at h
    · rw [← coe_toReal θ, heq] at h
      simp at h
    · rw [← sign_toReal hpi, _root_.sign_neg (hlt.trans (Left.neg_neg_iff.2 pi_div_two_pos)), ←
        sign_toReal] at h
      swap
      · intro he
        simp [he] at h
      rw [← neg_div] at hlt
      rw [two_nsmul_toReal_eq_two_mul_add_two_pi.2 hlt.le, sign_pos] at h
      · simp at h
      · linarith [neg_pi_lt_toReal θ]
  · have hpi' : (2 : ℕ) • θ ≠ π := by
      rw [Ne, two_nsmul_eq_pi_iff, not_or]
      constructor
      · rintro rfl
        simp [pi_pos, abs_of_pos] at h
      · rintro rfl
        rw [toReal_neg_pi_div_two] at h
        simp [pi_pos, neg_div, abs_of_pos] at h
    rw [abs_lt, ← neg_div] at h
    rw [← sign_toReal hpi, ← sign_toReal hpi', two_nsmul_toReal_eq_two_mul.2 ⟨h.1, h.2.le⟩,
      sign_mul, sign_pos (zero_lt_two' ℝ), one_mul]

theorem sign_two_zsmul_eq_sign_iff {θ : Angle} :
    ((2 : ℤ) • θ).sign = θ.sign ↔ θ = π ∨ |θ.toReal| < π / 2 := by
  rw [two_zsmul, ← two_nsmul, sign_two_nsmul_eq_sign_iff]

theorem continuousAt_sign {θ : Angle} (h0 : θ ≠ 0) (hpi : θ ≠ π) : ContinuousAt sign θ :=
  (continuousAt_sign_of_ne_zero (sin_ne_zero_iff.2 ⟨h0, hpi⟩)).comp continuous_sin.continuousAt

theorem _root_.ContinuousOn.angle_sign_comp {α : Type*} [TopologicalSpace α] {f : α → Angle}
    {s : Set α} (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π) :
    ContinuousOn (sign ∘ f) s := by
  refine (continuousOn_of_forall_continuousAt fun θ hθ => ?_).comp hf (Set.mapsTo_image f s)
  obtain ⟨z, hz, rfl⟩ := hθ
  exact continuousAt_sign (hs _ hz).1 (hs _ hz).2

/-- Suppose a function to angles is continuous on a connected set and never takes the values `0`
or `π` on that set. Then the values of the function on that set all have the same sign. -/
theorem sign_eq_of_continuousOn {α : Type*} [TopologicalSpace α] {f : α → Angle} {s : Set α}
    {x y : α} (hc : IsConnected s) (hf : ContinuousOn f s) (hs : ∀ z ∈ s, f z ≠ 0 ∧ f z ≠ π)
    (hx : x ∈ s) (hy : y ∈ s) : (f y).sign = (f x).sign :=
  (hc.image _ (hf.angle_sign_comp hs)).isPreconnected.subsingleton (Set.mem_image_of_mem _ hy)
    (Set.mem_image_of_mem _ hx)

end Angle

end Real
