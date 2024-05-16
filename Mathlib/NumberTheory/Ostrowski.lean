import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.Seminorm

noncomputable section
open Int

variable {f g : MulRingNorm ℚ}

/-- Values of a multiplicative norm of the rationals are determined by the values on the
integers. -/
lemma NormRat_eq_on_Int_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ (∀ n : ℤ , f n = g n) := by
  refine' ⟨_, fun a n => a n⟩
  intro h z
  obtain ⟨n,rfl | rfl ⟩ := eq_nat_or_neg z
  · exact h n
  · simp only [cast_neg, cast_ofNat, map_neg_eq_map]
    exact h n

/-- Values of a multiplicative norm of the rationals are determined by the values on the natural
numbers. -/
lemma NormRat_eq_iff_eq_on_Nat : (∀ n : ℕ , f n = g n) ↔ f = g := by
  refine' ⟨_, fun h n => congrFun (congrArg DFunLike.coe h) ↑n⟩
  intro h
  ext z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, NormRat_eq_on_Int_iff_eq_on_Nat.mp h]

/-- The equivalence class of a multiplicative norm on the rationals is determined by its values on
the natural numbers. -/
lemma NormRat_equiv_iff_equiv_on_Nat : (∃ c : ℝ, 0 < c ∧ (∀ n : ℕ , (f n)^c = g n)) ↔
    f.equiv g := by
    refine ⟨?_, fun ⟨c, hc, h⟩ ↦ ⟨c, ⟨hc, fun n ↦ by rw [← h]⟩⟩⟩
    intro ⟨c, hc, h⟩
    use c
    refine ⟨hc, ?_⟩
    ext x
    rw [← Rat.num_div_den x, map_div₀, map_div₀, Real.div_rpow (apply_nonneg f _)
      (apply_nonneg f _), h x.den, ← MulRingNorm.apply_natAbs_eq,← MulRingNorm.apply_natAbs_eq,
      h (natAbs x.num)]
