/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.QuadraticField.Basic
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Units of quadratic fields

Let `K` be a quadratic field. We compute the unit rank and the roots of unity of `K`. When `K` is
complex, we determine its units completely. When `K` is real, we define the fundamental unit of
`K` with respect to a real embedding `φ` and show that, up to sign, every unit is a power of it.

## Main definitions

* `NumberField.QuadraticField.fundamentalUnit`: the fundamental unit of a real quadratic field
  with respect to a real embedding `φ`, that is the generator of the units modulo torsion that is
  greater than `1` under `φ`.

## Main results

* `NumberField.QuadraticField.rank_eq_one` and `NumberField.QuadraticField.rank_eq_zero`: the
  unit rank of a real, resp. complex, quadratic field is `1`, resp. `0`.

Complex quadratic fields:

* `NumberField.QuadraticField.torsion_eq_top`: every unit is a root of unity.
* `NumberField.QuadraticField.torsionOrder_eq_four`,
  `NumberField.QuadraticField.torsionOrder_eq_six` and
  `NumberField.QuadraticField.torsionOrder_eq_two_of_isTotallyComplex`: the number of roots of
  unity is `4` if the discriminant is `-4`, `6` if it is `-3`, and `2` otherwise.
* `NumberField.QuadraticField.isUnit_iff_eq_one_or_neg_one`: if the discriminant is neither `-3`
  nor `-4`, the only units are `1` and `-1`.

Real quadratic fields:

* `NumberField.QuadraticField.torsion_eq_one_or_neg_one`: the roots of unity are `1` and `-1`.
* `NumberField.QuadraticField.exists_eq_zpow_or_eq_neg_zpow`: every unit is, up to sign, a power
  of the fundamental unit.
* `NumberField.QuadraticField.eq_fundamentalUnit_iff`: the fundamental unit is the only generator
  of the units modulo torsion that is greater than `1` under `φ`.
* `NumberField.QuadraticField.conj_fundamentalUnit`: the conjugate of the fundamental unit with
  respect to `φ` is the fundamental unit with respect to `φ ∘ conj`.
* `NumberField.QuadraticField.regulator_eq_log_fundamentalUnit`: the regulator is the logarithm
  of the fundamental unit.
-/

public section

open Algebra NumberField NumberField.Units QuadraticAlgebra

namespace NumberField.QuadraticField

variable (K : Type*) [Field K] [CharZero K] [IsQuadraticExtension ℚ K]

/-- The unit rank of a real quadratic field is `1`. -/
theorem rank_eq_one [IsTotallyReal K] : rank K = 1 := by
  rw [rank, card_infinitePlace_eq_two]

/-- The unit rank of a complex quadratic field is `0`. -/
theorem rank_eq_zero [IsTotallyComplex K] : rank K = 0 := by
  rw [rank, card_infinitePlace_eq_one]

section complex

/-- A complex quadratic field of discriminant `-4` has `4` roots of unity. -/
theorem torsionOrder_eq_four (h : discr K = -4) : torsionOrder K = 4 := by
  have := isCyclotomicExtension_four_of_discr K h
  simp +decide [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 4)]

/-- A complex quadratic field of discriminant `-3` has `6` roots of unity. -/
theorem torsionOrder_eq_six (h : discr K = -3) : torsionOrder K = 6 := by
  have := isCyclotomicExtension_six_of_discr K h
  simp +decide [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 6)]

variable [IsTotallyComplex K] {K}

/-- In a complex quadratic field of discriminant other than `-3` and `-4`, the only units are `1`
and `-1`. -/
theorem isUnit_iff_eq_one_or_neg_one (h₃ : discr K ≠ -3) (h₄ : discr K ≠ -4) {x : 𝓞 K} :
    IsUnit x ↔ x = 1 ∨ x = -1 := by
  rw [← isUnit_map_iff (nonempty_algEquiv_quadraticAlgebra_int K).some,
    QuadraticAlgebra.Int.isUnit_iff_eq_one_or_neg_one (isFundamentalDiscr_discr K)
      (discr_neg K) h₃ h₄,
    ← AlgEquiv.eq_symm_apply, ← AlgEquiv.eq_symm_apply, map_neg, map_one]

/-- A complex quadratic field of discriminant other than `-3` and `-4` has `2` roots of unity. -/
theorem torsionOrder_eq_two_of_isTotallyComplex (h₃ : discr K ≠ -3) (h₄ : discr K ≠ -4) :
    torsionOrder K = 2 := by
  rw [torsionOrder, Nat.card_eq_two_iff]
  refine ⟨1, ⟨-1, neg_one_mem_torsion⟩, by simp [OneMemClass.one_def, ← Subtype.coe_ne_coe], ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun ⟨x, _⟩ ↦ ?_
  simpa [Subtype.ext_iff] using (isUnit_iff_eq_one_or_neg_one h₃ h₄).mp x.isUnit

/-- All the units of a complex quadratic field are roots of unity. -/
theorem torsion_eq_top : torsion K = ⊤ := by
  have : IsEmpty (Fin (rank K)) := rank_eq_zero K ▸ Fin.isEmpty'
  simp [← closure_fundSystem_sup_torsion_eq_top, Set.range_eq_empty]

end complex

noncomputable section real

variable [IsTotallyReal K]

instance : Infinite (𝓞 K)ˣ := infinite_of_rank_pos K <| by simp [rank_eq_one]

variable {K} in
/-- The only roots of unity of a real quadratic field are `1` and `-1`. -/
theorem torsion_eq_one_or_neg_one (x : torsion K) :
    (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  apply torsion_eq_one_or_neg_one_of_nrRealPlaces_pos
  simp [nrRealPlaces_eq_two]

/-- A real quadratic field has `2` roots of unity. -/
theorem torsionOrder_eq_two_of_isTotallyReal : torsionOrder K = 2 := by
  apply torsionOrder_eq_two_of_nrRealPlaces_pos
  simp [nrRealPlaces_eq_two]

/-- An arbitrary generator of the group of units of a real quadratic field modulo torsion. -/
private def fundamentalUnit'' : (𝓞 K)ˣ := fundSystem K ⟨0, by simp [rank_eq_one K]⟩

private theorem zpowers_fundamentalUnit''_sup_torsion_eq_top :
    Subgroup.zpowers (fundamentalUnit'' K) ⊔ torsion K = ⊤ := by
  let : Unique (Fin (rank K)) := (finCongr (rank_eq_one K)).unique
  rw [← closure_fundSystem_sup_torsion_eq_top, Set.range_unique, ← Subgroup.zpowers_eq_closure,
    fundamentalUnit'', Unique.default_eq]

variable {K} (φ : K →+* ℝ)

/-- A generator of the group of units of a real quadratic field modulo torsion
that is positive under the real embedding `φ`. -/
private def fundamentalUnit' : (𝓞 K)ˣ :=
  if 0 < φ (fundamentalUnit'' K) then fundamentalUnit'' K else - fundamentalUnit'' K

private theorem zpowers_fundamentalUnit'_sup_torsion_eq_top :
    Subgroup.zpowers (fundamentalUnit' φ) ⊔ torsion K = ⊤ := by
  rw [fundamentalUnit', ← zpowers_fundamentalUnit''_sup_torsion_eq_top K]
  split_ifs
  · rfl
  · simp_rw [sup_eq_sup_iff_right, Subgroup.zpowers_le, Subgroup.mem_sup']
    exact ⟨⟨⟨fundamentalUnit'' K, Subgroup.mem_zpowers _⟩, ⟨-1, neg_one_mem_torsion⟩, by simp⟩,
      ⟨⟨-fundamentalUnit'' K, Subgroup.mem_zpowers _⟩, ⟨-1, neg_one_mem_torsion⟩, by simp⟩⟩

private theorem fundamentalUnit'_ne_one : fundamentalUnit' φ ≠ 1 := by
  by_contra h
  have htop : Finite (⊤ : Subgroup (𝓞 K)ˣ) := by
    simp only [← zpowers_fundamentalUnit'_sup_torsion_eq_top φ, h,
      Subgroup.zpowers_one_eq_bot, bot_le, sup_of_le_right]
    infer_instance
  exact htop.not_infinite <| Subgroup.topEquiv.infinite_iff.mpr inferInstance

private theorem pos_fundamentalUnit' : 0 < φ (fundamentalUnit' φ) := by
  rw [fundamentalUnit']
  split_ifs with h
  · exact h
  · rw [Units.val_neg, map_neg, map_neg, Left.neg_pos_iff]
    exact (Ne.le_iff_lt (by simp)).mp (not_lt.mp h)

/-- The fundamental unit of a real quadratic field with respect to the real embedding `φ`. -/
def fundamentalUnit : (𝓞 K)ˣ :=
  if 1 < φ (fundamentalUnit' φ) then fundamentalUnit' φ else (fundamentalUnit' φ)⁻¹

/-- The units of a real quadratic field are generated by `-1` and the fundamental unit. -/
theorem zpowers_fundamentalUnit_sup_torsion_eq_top :
    Subgroup.zpowers (fundamentalUnit φ) ⊔ torsion K = ⊤ := by
  rw [fundamentalUnit, ← zpowers_fundamentalUnit'_sup_torsion_eq_top φ]
  split_ifs
  · rfl
  · simp_rw [sup_eq_sup_iff_right, Subgroup.zpowers_le, Subgroup.mem_sup']
    exact ⟨⟨⟨(fundamentalUnit' φ) ^ (-1 : ℤ), Subgroup.zpow_mem_zpowers _ _⟩, 1, by simp⟩,
      ⟨⟨(fundamentalUnit' φ)⁻¹ ^ (-1 : ℤ), Subgroup.zpow_mem_zpowers _ _⟩, 1, by simp⟩⟩

/-- The fundamental unit is greater than `1` under the real embedding `φ`. -/
theorem one_lt_fundamentalUnit : 1 < φ (fundamentalUnit φ) := by
  rw [fundamentalUnit]
  split_ifs with h
  · exact h
  · rw [map_units_inv, map_inv₀, one_lt_inv_iff₀]
    refine ⟨pos_fundamentalUnit' φ, (Ne.le_iff_lt ?_).mp (not_lt.mp h)⟩
    simpa [map_ne_one_iff _ φ.injective] using fundamentalUnit'_ne_one φ

/-- The fundamental unit has infinite order. -/
theorem not_isOfFinOrder_fundamentalUnit : ¬IsOfFinOrder (fundamentalUnit φ) := by
  by_contra h
  have htop : Finite (⊤ : Subgroup (𝓞 K)ˣ) := by
    rw [← zpowers_fundamentalUnit_sup_torsion_eq_top φ,
      sup_eq_right.mpr (by rwa [Subgroup.zpowers_le])]
    infer_instance
  exact htop.not_infinite <| Subgroup.topEquiv.infinite_iff.mpr inferInstance

/-- The fundamental unit is not a root of unity. -/
theorem fundamentalUnit_notMem_torsion : fundamentalUnit φ ∉ torsion K :=
  fun h ↦ not_isOfFinOrder_fundamentalUnit φ <| (CommGroup.mem_torsion (fundamentalUnit φ)).mp h

/-- Every unit of a real quadratic field is, up to sign, a power of the fundamental unit. -/
theorem exists_eq_zpow_or_eq_neg_zpow (x : (𝓞 K)ˣ) :
    ∃ n : ℤ, x = fundamentalUnit φ ^ n ∨ x = -fundamentalUnit φ ^ n := by
  rsuffices ⟨⟨_, ⟨n, rfl⟩⟩, s, rfl⟩ :
    ∃ (y : Subgroup.zpowers (fundamentalUnit φ)) (z : torsion K), y * z.val = x
  · refine ⟨n, ?_⟩
    obtain (hs | hs) := torsion_eq_one_or_neg_one s <;> simp [hs]
  rw [← Subgroup.mem_sup', zpowers_fundamentalUnit_sup_torsion_eq_top]
  exact Subgroup.mem_top x

/-- A unit that is nonnegative under `φ` is a power of the fundamental unit. -/
theorem exists_eq_zpow_of_nonneg {x : (𝓞 K)ˣ} (hx : 0 ≤ φ x) :
    ∃ n : ℤ, x = fundamentalUnit φ ^ n := by
  obtain ⟨n, h⟩ := exists_eq_zpow_or_eq_neg_zpow φ x
  refine ⟨n, h.resolve_right fun h ↦ ?_⟩
  rw [h, Units.val_neg, map_neg, map_neg, Left.nonneg_neg_iff, coe_zpow, map_zpow₀] at hx
  linarith [zpow_pos (zero_lt_one.trans (one_lt_fundamentalUnit φ)) n]

/-- A unit that is nonpositive under `φ` is the negative of a power of the fundamental unit. -/
theorem exists_eq_neg_zpow_of_nonpos {x : (𝓞 K)ˣ} (hx : φ x ≤ 0) :
    ∃ n : ℤ, x = -fundamentalUnit φ ^ n := by
  obtain ⟨n, h⟩ := exists_eq_zpow_or_eq_neg_zpow φ x
  refine ⟨n, h.resolve_left fun h ↦ ?_⟩
  rw [h, coe_zpow, map_zpow₀] at hx
  linarith [zpow_pos (zero_lt_one.trans (one_lt_fundamentalUnit φ)) n]

/-- The fundamental unit is the only generator of the units modulo torsion that is greater than `1`
under the real embedding `φ`. -/
theorem eq_fundamentalUnit_iff (u : (𝓞 K)ˣ) :
    u = fundamentalUnit φ ↔ Subgroup.zpowers u ⊔ torsion K = ⊤ ∧ 1 < φ u := by
  refine ⟨fun h ↦ ?_, fun hu ↦ ?_⟩
  · exact h ▸ ⟨zpowers_fundamentalUnit_sup_torsion_eq_top φ, one_lt_fundamentalUnit φ⟩
  · obtain ⟨n, hn⟩ := exists_eq_zpow_of_nonneg φ (zero_le_one.trans hu.2.le)
    suffices n = 1 ∨ n = -1 by
      rwa [this.resolve_right fun h ↦ (not_le.mpr hu.2) ?_, zpow_one] at hn
      rw [hn, coe_zpow, map_zpow₀, h, zpow_neg_one, inv_le_one_iff₀]
      exact Or.inr (one_lt_fundamentalUnit φ).le
    have h := hu.1.trans (zpowers_fundamentalUnit_sup_torsion_eq_top φ).symm
    simp_rw [sup_eq_sup_iff_right, Subgroup.zpowers_le, Subgroup.mem_sup'] at h
    obtain ⟨⟨_, ⟨m, rfl⟩⟩, z, hu'⟩ := h.2
    dsimp only at hu'
    have : z = 1 := by
      rw [Subtype.ext_iff, OneMemClass.one_def]
      refine (torsion_eq_one_or_neg_one z).resolve_right fun hz ↦
        not_le.mpr (zero_lt_one.trans (one_lt_fundamentalUnit φ)) ?_
      simpa [← hu', hz, coe_zpow] using zpow_nonneg (by linarith) _
    rw [← zpow_one (fundamentalUnit φ), hn, this, OneMemClass.coe_one, mul_one, ← zpow_mul,
      (injective_zpow_iff_not_isOfFinOrder.mpr (not_isOfFinOrder_fundamentalUnit φ)).eq_iff] at hu'
    exact Int.eq_one_or_neg_one_of_mul_eq_one hu'

open IsQuadraticExtension in
attribute [local instance] Units.mulDistribMulActionRight in
/-- The conjugate of the fundamental unit with respect to `φ` is the fundamental unit with respect
to `φ ∘ conj`. -/
theorem conj_fundamentalUnit :
    conj ℚ K • (fundamentalUnit φ : 𝓞 K) = fundamentalUnit (φ.comp (conj ℚ K : K →+* K)) := by
  rw [← Units.coe_smul, ← Units.ext_iff, eq_fundamentalUnit_iff]
  refine ⟨?_, ?_⟩
  · have h₁ {u : (𝓞 K)ˣ} : conj ℚ K • u =
      (Units.mapEquiv (MulSemiringAction.toRingEquiv _ (𝓞 K) (conj ℚ K)).toMulEquiv :
        (𝓞 K)ˣ →* (𝓞 K)ˣ) u := rfl
    have h₂ : Subgroup.map
        (Units.mapEquiv (MulSemiringAction.toRingEquiv _ (𝓞 K) (conj ℚ K)).toMulEquiv :
          (𝓞 K)ˣ →* (𝓞 K)ˣ) (torsion K) = torsion K := by
      rw [torsion_eq_zpowers_neg_one_of_nrRealPlaces_pos (by simp [nrRealPlaces_eq_two]),
        MonoidHom.map_zpowers, ← h₁]
      congr
      simp [Units.ext_iff]
    rw [h₁, ← MonoidHom.map_zpowers, ← h₂, ← MulEquiv.mapSubgroup_apply,
      ← MulEquiv.mapSubgroup_apply, ← OrderIso.map_sup, zpowers_fundamentalUnit_sup_torsion_eq_top,
      OrderIso.map_top]
  · rw [Units.coe_smul, algebraMap.smul', AlgEquiv.smul_def, RingHom.comp_apply,
      RingHom.coe_coe, conj_conj]
    exact one_lt_fundamentalUnit φ

open IsQuadraticExtension in
/-- The fundamental unit with respect to `φ ∘ conj` is the norm of the fundamental unit with respect
to `φ` divided by it. -/
theorem fundamentalUnit_comp_conj :
    (fundamentalUnit (φ.comp (conj ℚ K : K →+* K)) : K) =
      Algebra.norm ℚ (fundamentalUnit φ : K) * (fundamentalUnit φ : K)⁻¹ := by
  rw [← eq_ratCast (algebraMap ℚ K), ← mul_conj, ← conj_fundamentalUnit, algebraMap.smul',
    AlgEquiv.smul_def]
  field_simp

open IsQuadraticExtension in
private theorem regulator_eq'' (w : InfinitePlace K) :
    regulator K = |Real.log (w (fundamentalUnit'' K))| := by
  classical
  let : Inhabited {w' : InfinitePlace K // w' ≠ conj ℚ K • w} :=
    ⟨w, (conj_smul_infinitePlace_ne_self w).symm⟩
  have : Subsingleton {w' : InfinitePlace K // w' ≠ conj ℚ K • w} := by
    simp [← Fintype.card_le_one_iff_subsingleton, card_infinitePlace_eq_two]
  let : Unique ({w' : InfinitePlace K // w' ≠ conj ℚ K • w}) := Unique.mk' _
  let : Unique (Fin (rank K)) := (finCongr (rank_eq_one K)).unique
  rw [regulator_eq_det K (conj ℚ K • w) (Equiv.ofUnique _ _)]
  simp only [ne_eq, IsTotallyReal.mult_eq, Nat.cast_one, Equiv.ofUnique_apply, Pi.default_def,
    one_mul, Matrix.det_unique, Matrix.of_apply]
  rw [fundamentalUnit'', Unique.default_eq ⟨w, (conj_smul_infinitePlace_ne_self w).symm⟩,
    Unique.default_eq]

private theorem regulator_eq' :
    regulator K = |Real.log (φ (fundamentalUnit' φ))| := by
  simp only [regulator_eq'' (InfinitePlace.mk (Complex.ofRealHom.comp φ)), InfinitePlace.apply,
    RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real,
    Real.norm_eq_abs, Real.log_abs, fundamentalUnit']
  split_ifs <;> simp

/-- The regulator of a real quadratic field is the logarithm of its fundamental unit. -/
theorem regulator_eq_log_fundamentalUnit :
    regulator K = Real.log (φ (fundamentalUnit φ)) := by
  rw [regulator_eq' φ, fundamentalUnit]
  split_ifs with h
  · rw [abs_of_nonneg (Real.log_nonneg h.le)]
  · rw [abs_of_nonpos, map_units_inv, map_inv₀, Real.log_inv]
    exact Real.log_nonpos (pos_fundamentalUnit' φ).le (by rwa [not_lt] at h)

end real

end NumberField.QuadraticField
