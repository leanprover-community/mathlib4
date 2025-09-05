import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.ConjRootClass

open NumberField

open NumberField IntermediateField

theorem NumberField.natAbs_discr_eq_absNorm_diffenrentIdeal_mul_natAbs_discr_pow (E F : Type*)
    [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] :
    (discr F).natAbs = Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 F)) *
      (discr E).natAbs ^ Module.finrank E F := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 F))
  rwa [absNorm_differentIdeal (K := F), map_mul, Ideal.absNorm_algebraMap E F,
    absNorm_differentIdeal (K := E)] at this




-- theorem NumberField.discr_pow_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
--     [NumberField F] [Algebra E F] : discr E ^ Module.finrank E F ∣ discr F := by
--   have := congr_arg Ideal.absNorm
--     (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 F))
--   rw [absNorm_differentIdeal (K := F), map_mul, Ideal.absNorm_algebraMap E F,
--     absNorm_differentIdeal (K := E)] at this
--   rw [← Int.dvd_natAbs, this, Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow,
--     ← mul_assoc, mul_comm _ (discr E ^ _), mul_assoc]
--   exact Int.dvd_mul_right _ _

theorem NumberField.discr_dvd_discr (E F : Type*) [Field E] [Field F] [NumberField E]
    [NumberField F] [Algebra E F] : discr E ∣ discr F := by
  suffices discr E ^ Module.finrank E F ∣ discr F from
    dvd_trans (dvd_pow_self _ (Nat.ne_zero_of_lt Module.finrank_pos)) this
  rw [← Int.dvd_natAbs, natAbs_discr_eq_absNorm_diffenrentIdeal_mul_natAbs_discr_pow E F,
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (discr E ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

theorem NumberField.LinearDisjoint_of_isGalois_isCoprime_discr {E : Type*} [Field E] [NumberField E]
    (F₁ F₂ : IntermediateField ℚ E) [IsGalois ℚ F₁] (h : IsCoprime (discr F₁) (discr F₂)) :
    F₁.LinearDisjoint F₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  suffices IsUnit (discr ↥(F₁ ⊓ F₂)) by
    contrapose! this
    have : 1 < Module.finrank ℚ ↥(F₁ ⊓ F₂) := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, ?_⟩
      · exact Module.finrank_pos.ne'
      · rwa [ne_eq, ← IntermediateField.finrank_eq_one_iff] at this
    have := abs_discr_gt_two this
    rw [Int.isUnit_iff_abs_eq]
    linarith
  let _ : Algebra ↥(F₁ ⊓ F₂) F₁ := RingHom.toAlgebra (inclusion inf_le_left).toRingHom
  let _ : Algebra ↥(F₁ ⊓ F₂) F₂ := RingHom.toAlgebra (inclusion inf_le_right).toRingHom
  exact h.isUnit_of_dvd' (NumberField.discr_dvd_discr _ _) (NumberField.discr_dvd_discr _ _)

example {E : Type*} [Field E] [NumberField E] (F₁ F₂ : IntermediateField ℚ E) (p : ℕ)
    (hp : p.Prime) :
    p ∣ (discr ↥(F₁ ⊔ F₂)).natAbs ↔ (p ∣ (discr F₁).natAbs ∨ p ∣ (discr F₂).natAbs) := by
  let _ : Algebra F₁ ↥(F₁ ⊔ F₂) := RingHom.toAlgebra (inclusion le_sup_left).toRingHom
  let _ : Algebra F₂ ↥(F₁ ⊔ F₂) := RingHom.toAlgebra (inclusion le_sup_right).toRingHom
  constructor
  · intro h
    refine Decidable.or_iff_not_imp_left.mpr fun h₁ ↦ ?_
    have h₂ := natAbs_discr_eq_absNorm_diffenrentIdeal_mul_natAbs_discr_pow F₁ ↥(F₁ ⊔ F₂)
    have h₃ : p ∣ Ideal.absNorm (differentIdeal (𝓞 F₁) (𝓞 ↥(F₁ ⊔ F₂))) := sorry

    sorry
  · rintro (h | h)
    · exact Nat.dvd_trans h <| Int.natAbs_dvd_natAbs.mpr (discr_dvd_discr _ _)
    · exact Nat.dvd_trans h <| Int.natAbs_dvd_natAbs.mpr (discr_dvd_discr _ _)

example {F : Type*} [Field F] [NumberField F] (α : F)
