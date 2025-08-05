/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Cotangent

/-!

# Equivalent conditions for DVR

In `IsDiscreteValuationRing.TFAE`, we show that the following are equivalent for a
noetherian local domain that is not a field `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version without `¬ IsField R`.
-/


variable (R : Type*) [CommRing R]

open scoped Multiplicative

open IsLocalRing Module

theorem exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = maximalIdeal R ^ n := by
  by_cases h : IsField R
  · let _ := h.toField
    exact ⟨0, by simp [(eq_bot_or_eq_top I).resolve_left hI]⟩
  classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI' : I = ⊤
  · use 0; rw [pow_zero, hI', Ideal.one_eq_top]
  have H : ∀ r : R, ¬IsUnit r ↔ x ∣ r := fun r =>
    (SetLike.ext_iff.mp hx r).trans Ideal.mem_span_singleton
  have : x ≠ 0 := by
    rintro rfl
    apply Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) h
    simp [hx]
  have hx' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x this hx
  have H' : ∀ r : R, r ≠ 0 → r ∈ nonunits R → ∃ n : ℕ, Associated (x ^ n) r := by
    intro r hr₁ hr₂
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (WfDvdMonoid.not_unit_iff_exists_factors_eq r hr₁).mp hr₂
    have : ∀ b ∈ f, Associated x b := by
      intro b hb
      exact Irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1)
    clear hr₁ hr₂ hf₁
    induction' f using Multiset.induction with fa fs fh
    · exact (hf₂ rfl).elim
    rcases eq_or_ne fs ∅ with (rfl | hf')
    · use 1
      rw [pow_one, Multiset.prod_cons, Multiset.empty_eq_zero, Multiset.prod_zero, mul_one]
      exact this _ (Multiset.mem_cons_self _ _)
    · obtain ⟨n, hn⟩ := fh hf' fun b hb => this _ (Multiset.mem_cons_of_mem hb)
      use n + 1
      rw [pow_add, Multiset.prod_cons, mul_comm, pow_one]
      exact Associated.mul_mul (this _ (Multiset.mem_cons_self _ _)) hn
  have : ∃ n : ℕ, x ^ n ∈ I := by
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0 := by
      by_contra! h; apply hI; rw [eq_bot_iff]; exact h
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximalIdeal hI' hr₁)
    use n
    rwa [← I.unit_mul_mem_iff_mem u.isUnit, mul_comm]
  use Nat.find this
  apply le_antisymm
  · change ∀ s ∈ I, s ∈ _
    by_contra! hI''
    obtain ⟨s, hs₁, hs₂⟩ := hI''
    apply hs₂
    by_cases hs₃ : s = 0; · rw [hs₃]; exact zero_mem _
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximalIdeal hI' hs₁)
    rw [mul_comm, Ideal.unit_mul_mem_iff_mem _ u.isUnit] at hs₁ ⊢
    apply Ideal.pow_le_pow_right (Nat.find_min' this hs₁)
    apply Ideal.pow_mem_pow
    exact (H _).mpr (dvd_refl _)
  · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Nat.find_spec this

theorem maximalIdeal_isPrincipal_of_isDedekindDomain [IsLocalRing R] [IsDomain R]
    [IsDedekindDomain R] : (maximalIdeal R).IsPrincipal := by
  classical
  by_cases ne_bot : maximalIdeal R = ⊥
  · rw [ne_bot]; infer_instance
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ maximalIdeal R, a ≠ (0 : R) := by
    by_contra! h'; apply ne_bot; rwa [eq_bot_iff]
  have hle : Ideal.span {a} ≤ maximalIdeal R := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  have : (Ideal.span {a}).radical = maximalIdeal R := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hle, inferInstance⟩
    · refine
        le_sInf fun I hI =>
          (eq_maximalIdeal <| hI.2.isMaximal (fun e => ha₂ ?_)).ge
      rw [← Ideal.span_singleton_eq_bot, eq_bot_iff, ← e]; exact hI.1
  have : ∃ n, maximalIdeal R ^ n ≤ Ideal.span {a} := by
    rw [← this]; apply Ideal.exists_radical_pow_le_of_fg; exact IsNoetherian.noetherian _
  rcases hn : Nat.find this with - | n
  · have := Nat.find_spec this
    rw [hn, pow_zero, Ideal.one_eq_top] at this
    exact (Ideal.IsMaximal.ne_top inferInstance (eq_top_iff.mpr <| this.trans hle)).elim
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximalIdeal R ^ n, b ∉ Ideal.span {a} := by
    by_contra! h'; rw [Nat.find_eq_iff] at hn; exact hn.2 n n.lt_succ_self fun x hx => h' x hx
  have hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m := by
    intro m hm; rw [← Ideal.mem_span_singleton']; apply Nat.find_spec this
    rw [hn, pow_succ]; exact Ideal.mul_mem_mul hb₁ hm
  have hb₄ : b ≠ 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel₀ _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine ⟨_, ⟨a, ha₁, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribMulAction.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      by_contra h; apply hx
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/--
Let `(R, m, k)` be a noetherian local domain (possibly a field).
The following are equivalent:
0. `R` is a PID
1. `R` is a valuation ring
2. `R` is a dedekind domain
3. `R` is integrally closed with at most one non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² ≤ 1`
6. Every nonzero ideal is a power of `m`.

Also see `IsDiscreteValuationRing.TFAE` for a version assuming `¬ IsField R`.
-/
theorem tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] :
    List.TFAE
      [IsPrincipalIdealRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R,
        (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) ≤ 1,
        ∀ I ≠ ⊥, ∃ n : ℕ, I = maximalIdeal R ^ n] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 1 := fun _ ↦ ((IsBezout.TFAE (R := R)).out 0 1).mp ‹_›
  tfae_have 1 → 4
  | H => ⟨inferInstance, fun P hP hP' ↦ eq_maximalIdeal (hP'.isMaximal hP)⟩
  tfae_have 4 → 3 :=
    fun ⟨h₁, h₂⟩ ↦ { h₁ with maximalOfPrime := (h₂ _ · · ▸ maximalIdeal.isMaximal R) }
  tfae_have 3 → 5 := fun h ↦ maximalIdeal_isPrincipal_of_isDedekindDomain R
  tfae_have 6 ↔ 5 := finrank_cotangentSpace_le_one_iff
  tfae_have 5 → 7 := exists_maximalIdeal_pow_eq_of_principal R
  tfae_have 7 → 2 := by
    rw [ValuationRing.iff_ideal_total]
    intro H
    constructor
    intro I J
    by_cases hI : I = ⊥; · subst hI; left; exact bot_le
    by_cases hJ : J = ⊥; · subst hJ; right; exact bot_le
    obtain ⟨n, rfl⟩ := H I hI
    obtain ⟨m, rfl⟩ := H J hJ
    exact (le_total m n).imp Ideal.pow_le_pow_right Ideal.pow_le_pow_right
  tfae_finish

/--
The following are equivalent for a
noetherian local domain that is not a field `(R, m, k)`:
0. `R` is a discrete valuation ring
1. `R` is a valuation ring
2. `R` is a dedekind domain
3. `R` is integrally closed with a unique non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² = 1`
6. Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version without `¬ IsField R`.
-/
theorem IsDiscreteValuationRing.TFAE [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h : ¬IsField R) :
    List.TFAE
      [IsDiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) = 1,
        ∀ (I) (_ : I ≠ ⊥), ∃ n : ℕ, I = maximalIdeal R ^ n] := by
  have : finrank (ResidueField R) (CotangentSpace R) = 1 ↔
      finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    simp [Nat.le_one_iff_eq_zero_or_eq_one, finrank_cotangentSpace_eq_zero_iff, h]
  rw [this]
  have : maximalIdeal R ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp h
  convert tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R
  · exact ⟨fun _ ↦ inferInstance, fun h ↦ { h with not_a_field' := this }⟩
  · exact ⟨fun h P h₁ h₂ ↦ h.unique ⟨h₁, h₂⟩ ⟨this, inferInstance⟩,
      fun H ↦ ⟨_, ⟨this, inferInstance⟩, fun P hP ↦ H P hP.1 hP.2⟩⟩

variable {R}

lemma IsLocalRing.finrank_CotangentSpace_eq_one_iff [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] : finrank (ResidueField R) (CotangentSpace R) = 1 ↔ IsDiscreteValuationRing R := by
  by_cases hR : IsField R
  · letI := hR.toField
    simp only [finrank_cotangentSpace_eq_zero, zero_ne_one, false_iff]
    exact fun h ↦ h.3 maximalIdeal_eq_bot
  · exact (IsDiscreteValuationRing.TFAE R hR).out 5 0

variable (R)

lemma IsLocalRing.finrank_CotangentSpace_eq_one [IsDomain R] [IsDiscreteValuationRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 1 :=
  finrank_CotangentSpace_eq_one_iff.mpr ‹_›

instance (priority := 100) IsDedekindDomain.isPrincipalIdealRing
    [IsLocalRing R] [IsDedekindDomain R] : IsPrincipalIdealRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 2 0).mp ‹_›
