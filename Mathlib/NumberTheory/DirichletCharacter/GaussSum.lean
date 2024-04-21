/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.GaussSum

/-!
# Gauss sums for Dirichlet characters
-/
variable {N : ℕ+} {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

open AddChar

lemma gaussSum_aux_of_mulShift (χ : DirichletCharacter R N) {d : ℕ}
    (hd : d ∣ N) (he : e.mulShift d = 1) {u : (ZMod N)ˣ} (hu : ZMod.unitsMap hd u = 1) :
    χ u * gaussSum χ e = gaussSum χ e := by
  suffices e.mulShift u = e by conv_lhs => rw [← this, gaussSum_mulShift]
  rw [(by ring : u.val = (u - 1) + 1), ← mulShift_mul, mulShift_one, mul_left_eq_self]
  rsuffices ⟨a, ha⟩ : (d : ℤ) ∣ (u.val.val - 1 : ℤ)
  · have : u.val - 1 = ↑(u.val.val - 1 : ℤ) := by simp only [ZMod.natCast_val, Int.cast_sub,
      ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_one]
    rw [this, ha]
    ext1 y
    simpa only [Int.cast_mul, Int.cast_natCast, mulShift_apply, mul_assoc, one_apply]
      using DFunLike.ext_iff.mp he (a * y)
  rw [← Units.eq_iff, Units.val_one, ZMod.unitsMap_def, Units.coe_map] at hu
  have : ZMod.castHom hd (ZMod d) u.val = ((u.val.val : ℤ) : ZMod d) := by simp
  rwa [MonoidHom.coe_coe, this, ← Int.cast_one, eq_comm,
    ZMod.intCast_eq_intCast_iff_dvd_sub] at hu

/-- If `gaussSum χ e ≠ 0`, and `d` is such that `e.mulShift d = 1`, then `χ` must factor through
`d`. (This will be used to show that Gauss sums vanish when `χ` is primitive and `e` is not.)-/
lemma factorsThrough_of_gaussSum_ne_zero [IsDomain R] {χ : DirichletCharacter R N} {d : ℕ}
    (hd : d ∣ N) (he : e.mulShift d = 1) (h_ne : gaussSum χ e ≠ 0) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker, ← Units.eq_iff, MulChar.coe_toUnitHom]
  simpa only [Units.val_one, ne_eq, h_ne, not_false_eq_true, mul_eq_right₀] using
    gaussSum_aux_of_mulShift e χ hd he hu

/-- If `χ` is primitive, but `e` is not, then `gaussSum χ e = 0`. -/
lemma gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive [IsDomain R]
    {χ : DirichletCharacter R N} (hχ : χ.isPrimitive) (he : ¬e.IsPrimitive) :
    gaussSum χ e = 0 := by
  contrapose! hχ
  rcases e.exists_divisor_of_not_isPrimitive he with ⟨d, hd₁, hd₂, hed⟩
  have : χ.conductor ≤ d := Nat.sInf_le <| factorsThrough_of_gaussSum_ne_zero e hd₁ hed hχ
  exact (this.trans_lt hd₂).ne

/-- If `χ` is a primitive character, then the function `a ↦ gaussSum χ (e.mulShift a)`, for any
fixed additive character `e`, is a constant multiple of `χ⁻¹`. -/
lemma gaussSum_mulShift_of_isPrimitive [IsDomain R] {χ : DirichletCharacter R N}
    (hχ : χ.isPrimitive) (a : ZMod N) :
    gaussSum χ (e.mulShift a) = χ⁻¹ a * gaussSum χ e := by
  by_cases ha : IsUnit a
  · conv_rhs => rw [← gaussSum_mulShift χ e ha.unit]
    have : IsUnit (χ a) := by rw [← ha.unit_spec, ← MulChar.coe_toUnitHom]; apply Units.isUnit
    rw [IsUnit.unit_spec, MulChar.inv_apply_eq_inv, Ring.inverse_mul_cancel_left _ _ this]
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    apply gaussSum_eq_zero_of_isPrimitive_of_not_isPrimitive _ hχ
    -- this is just showing `e.mulShift a` is not primitive if `a` is non-unit -- separate?
    simp only [IsPrimitive, not_forall]
    obtain ⟨d, ⟨b, hb⟩, u, hu, rfl⟩ := a.eq_unit_mul_divisor
    have hd' : d ≠ 1 := by contrapose! ha; rwa [ha, Nat.cast_one, mul_one]
    refine ⟨b, ?_, ?_⟩
    · have hb_ne : b ≠ 0 := (N.ne_zero <| mul_zero d ▸ · ▸ hb)
      have hb_lt : b < N := by
        refine lt_of_le_of_ne (Nat.le_of_dvd N.pos ⟨d, mul_comm b d ▸ hb⟩) ?_
        contrapose! hd'
        simpa only [ne_eq, PNat.ne_zero, not_false_eq_true, right_eq_mul₀] using (hd' ▸ hb :)
      rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
      exact fun h ↦ not_lt_of_le (Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hb_ne) h) hb_lt
    · rw [isNontrivial_iff_ne_trivial, mulShift_mulShift, mul_assoc, ← Nat.cast_mul,
        ← hb, ZMod.natCast_self, mul_zero, mulShift_zero, not_ne_iff]
