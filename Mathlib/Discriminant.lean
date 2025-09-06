import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.Minpoly.ConjRootClass

theorem Ideal.absNorm_algebraMap (A K L B : Type*) [CommRing A] [IsDedekindDomain A]
    [Module.Free ℤ A] [CommRing B] [IsDedekindDomain B] [Module.Free ℤ B] [Algebra A B] [Field K]
    [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    (I : Ideal A) : absNorm (I.map (algebraMap A B)) = absNorm I ^ Module.finrank K L := sorry

open NumberField

open NumberField IntermediateField

theorem NumberField.natAbs_discr_eq_absNorm_diffenrentIdeal_mul_natAbs_discr_pow (E F : Type*)
    [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F] :
    (discr F).natAbs = Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 F)) *
      (discr E).natAbs ^ Module.finrank E F := by
  have := congr_arg Ideal.absNorm
    (differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 F))
  rwa [absNorm_differentIdeal (K := F), map_mul, Ideal.absNorm_algebraMap (𝓞 E) E F (𝓞 F),
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

theorem NumberField.LinearDisjoint.of_isGalois_isCoprime_discr {E : Type*} [Field E] [CharZero E]
    (F₁ F₂ : IntermediateField ℚ E) [NumberField F₁] [NumberField F₂] [IsGalois ℚ F₁]
    (h : IsCoprime (discr F₁) (discr F₂)) :
    F₁.LinearDisjoint F₂ := by
  apply IntermediateField.LinearDisjoint.of_inf_eq_bot
  have : NumberField ↥(F₁ ⊓ F₂) := sorry
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

theorem step0 {E : Type*} [Field E] [CharZero E] (F₁ F₂ : IntermediateField ℚ E) [NumberField F₁]
    [NumberField F₂] (h : IsCoprime (discr F₁) (discr F₂)) (K : IntermediateField ℚ E)
    [NumberField K] [IsGalois ℚ K] (hK₁ : F₁ ≤ K)
    (hK₂ : ∀ p : ℕ, p.Prime → (p ∣ (discr K).natAbs ↔ p ∣ (discr F₁).natAbs)) :
    F₁.LinearDisjoint F₂ := by
  refine .of_le_left ?_ hK₁
  refine NumberField.LinearDisjoint.of_isGalois_isCoprime_discr K F₂ ?_
  rw [Int.isCoprime_iff_nat_coprime] at h ⊢
  apply Nat.coprime_of_dvd
  intro p hp
  specialize hK₂ p hp
  rw [hK₂]
  intro h'
  have := Nat.Coprime.of_dvd_left h' h
  rwa [hp.coprime_iff_not_dvd] at this

theorem step1 {E : Type*} [Field E] [CharZero E] (F₁ F₂ : IntermediateField ℚ E) [NumberField F₁]
    [NumberField F₂] [NumberField ↥(F₁ ⊔ F₂)] (p : ℕ) (hp : p.Prime) :
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

theorem step2 {A : Type*} [Field A] [IsAlgClosed A] [CharZero A] (α : A) (hα : IsAlgebraic ℚ α)
    [NumberField (adjoin ℚ {α})] (β : A) (hβ : IsConjRoot ℚ α β) (p : ℕ)
    [NumberField (adjoin ℚ {α, β})] (hp : p.Prime) :
    p ∣ (discr (adjoin ℚ {α, β})).natAbs ↔ p ∣ (discr (adjoin ℚ {α})).natAbs := by
  have : NumberField (adjoin ℚ {β}) := sorry
  have : NumberField ↥((adjoin ℚ {α}) ⊔ (adjoin ℚ {β})) := sorry
  have main := step1 (adjoin ℚ {α}) (adjoin ℚ {β}) p hp
  have : discr (adjoin ℚ {α}) = discr (adjoin ℚ {β}) := by
    apply discr_eq_discr_of_algEquiv
    refine minpoly.algEquiv hα hβ
  rw [← this, or_self] at main
  rw [← main]
  have : discr ↥(adjoin ℚ {α, β}) = discr (↥(adjoin ℚ {α} ⊔ adjoin ℚ {β})) := by
    congr!
    all_goals rw [← adjoin_union, Set.singleton_union]
  rw [this]

theorem step3 {A : Type*} [Field A] [IsAlgClosed A] [CharZero A] (α : A) (hα : IsAlgebraic ℚ α)
    [NumberField (adjoin ℚ {α})] (S : Finset A) [NumberField (adjoin ℚ (S : Set A))]
    (hS₁ : S.Nonempty) (hS₂ : ∀ β ∈ S, IsConjRoot ℚ α β) (p : ℕ) (hp : p.Prime) :
    p ∣ (discr (adjoin ℚ (S : Set A))).natAbs ↔ p ∣ (discr (adjoin ℚ {α})).natAbs := by
  induction hS₁ using Finset.Nonempty.cons_induction with
  | singleton => sorry
  | cons => sorry

#exit


theorem step3 {A : Type*} [Field A] [IsAlgClosed A] [CharZero A] (α : A) (hα : IsAlgebraic ℚ α)
    [NumberField (adjoin ℚ {α})] (S : Finset A) (hS : ∀ β ∈ S, IsConjRoot ℚ α β)
    [NumberField (adjoin ℚ S)] (p : ℕ) (hp : p.Prime) :
  sorry
