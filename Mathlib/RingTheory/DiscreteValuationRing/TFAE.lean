/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Nakayama

#align_import ring_theory.discrete_valuation_ring.tfae from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!

# Equivalent conditions for DVR

In `DiscreteValuationRing.TFAE`, we show that the following are equivalent for a
noetherian local domain `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

-/


variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

open scoped DiscreteValuation

open LocalRing

open scoped BigOperators

theorem exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [LocalRing R] [IsDomain R]
    (h : ¬IsField R) (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = maximalIdeal R ^ n := by
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
  have hx' := DiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x this hx
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
    apply Ideal.pow_le_pow (Nat.find_min' this hs₁)
    apply Ideal.pow_mem_pow
    exact (H _).mpr (dvd_refl _)
  · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Nat.find_spec this
#align exists_maximal_ideal_pow_eq_of_principal exists_maximalIdeal_pow_eq_of_principal

theorem maximalIdeal_isPrincipal_of_isDedekindDomain [LocalRing R] [IsDomain R]
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
    · refine'
        le_sInf fun I hI =>
          (eq_maximalIdeal <| hI.2.isMaximal (fun e => ha₂ _)).ge
      rw [← Ideal.span_singleton_eq_bot, eq_bot_iff, ← e]; exact hI.1
  have : ∃ n, maximalIdeal R ^ n ≤ Ideal.span {a} := by
    rw [← this]; apply Ideal.exists_radical_pow_le_of_fg; exact IsNoetherian.noetherian _
  cases' hn : Nat.find this with n
  · have := Nat.find_spec this
    rw [hn, pow_zero, Ideal.one_eq_top] at this
    exact (Ideal.IsMaximal.ne_top inferInstance (eq_top_iff.mpr <| this.trans hle)).elim
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximalIdeal R ^ n, ¬b ∈ Ideal.span {a} := by
    by_contra! h'; rw [Nat.find_eq_iff] at hn; exact hn.2 n n.lt_succ_self fun x hx => h' x hx
  have hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m := by
    intro m hm; rw [← Ideal.mem_span_singleton']; apply Nat.find_spec this
    rw [hn, pow_succ']; exact Ideal.mul_mem_mul hb₁ hm
  have hb₄ : b ≠ 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine' (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, _⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine' ⟨_, ⟨a, ha₁, rfl⟩, _⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribMulAction.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      by_contra h; apply hx
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine' ⟨⟨y, _⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]
#align maximal_ideal_is_principal_of_is_dedekind_domain maximalIdeal_isPrincipal_of_isDedekindDomain

theorem DiscreteValuationRing.TFAE [IsNoetherianRing R] [LocalRing R] [IsDomain R]
    (h : ¬IsField R) :
    List.TFAE
      [DiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        FiniteDimensional.finrank (ResidueField R) (CotangentSpace R) = 1,
        ∀ (I) (_ : I ≠ ⊥), ∃ n : ℕ, I = maximalIdeal R ^ n] := by
  have ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) h
  classical
  rw [finrank_eq_one_iff']
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 2 → 1
  · intro
    haveI := IsBezout.toGCDDomain R
    haveI : UniqueFactorizationMonoid R := ufm_of_gcd_of_wfDvdMonoid
    apply DiscreteValuationRing.of_ufd_of_unique_irreducible
    · obtain ⟨x, hx₁, hx₂⟩ := Ring.exists_not_isUnit_of_not_isField h
      obtain ⟨p, hp₁, -⟩ := WfDvdMonoid.exists_irreducible_factor hx₂ hx₁
      exact ⟨p, hp₁⟩
    · exact ValuationRing.unique_irreducible
  tfae_have 1 → 4
  · intro H
    exact ⟨inferInstance, ((DiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp H).2⟩
  tfae_have 4 → 3
  · rintro ⟨h₁, h₂⟩;
    exact { h₁ with
      maximalOfPrime := fun hI hI' => ExistsUnique.unique h₂ ⟨ne_bot, inferInstance⟩ ⟨hI, hI'⟩ ▸
        maximalIdeal.isMaximal R, }
  tfae_have 3 → 5
  · intro h; exact maximalIdeal_isPrincipal_of_isDedekindDomain R
  tfae_have 5 → 6
  · rintro ⟨x, hx⟩
    have : x ∈ maximalIdeal R := by rw [hx]; exact Submodule.subset_span (Set.mem_singleton x)
    let x' : maximalIdeal R := ⟨x, this⟩
    use Submodule.Quotient.mk x'
    constructor
    swap
    · intro e
      rw [Submodule.Quotient.mk_eq_zero] at e
      apply Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) h
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
      · exact ⟨{x}, (Finset.coe_singleton x).symm ▸ hx.symm⟩
      · conv_lhs => rw [hx]
        rw [Submodule.mem_smul_top_iff] at e
        rwa [Submodule.span_le, Set.singleton_subset_iff]
      · rw [LocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
    · refine' fun w => Quotient.inductionOn' w fun y => _
      obtain ⟨y, hy⟩ := y
      rw [hx, Submodule.mem_span_singleton] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  tfae_have 6 → 5
  · rintro ⟨x, hx, hx'⟩
    induction x using Quotient.inductionOn' with | h x => ?_
    use x
    apply le_antisymm
    swap; · rw [Submodule.span_le, Set.singleton_subset_iff]; exact x.prop
    have h₁ :
      (Ideal.span {(x : R)} : Ideal R) ⊔ maximalIdeal R ≤
        Ideal.span {(x : R)} ⊔ maximalIdeal R • maximalIdeal R := by
      refine' sup_le le_sup_left _
      rintro m hm
      obtain ⟨c, hc⟩ := hx' (Submodule.Quotient.mk ⟨m, hm⟩)
      induction c using Quotient.inductionOn' with | h c => ?_
      rw [← sub_sub_cancel (c * x) m]
      apply sub_mem _ _
      · refine' Ideal.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩)
      · have := (Submodule.Quotient.eq _).mp hc
        rw [Submodule.mem_smul_top_iff] at this
        exact Ideal.mem_sup_right this
    have h₂ : maximalIdeal R ≤ (⊥ : Ideal R).jacobson := by
      rw [LocalRing.jacobson_eq_maximalIdeal]
      exact bot_ne_top
    have :=
      Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson (IsNoetherian.noetherian _) h₂ h₁
    rw [Submodule.bot_smul, sup_bot_eq] at this
    rw [← sup_eq_left, eq_comm]
    exact le_sup_left.antisymm (h₁.trans <| le_of_eq this)
  tfae_have 5 → 7
  · exact exists_maximalIdeal_pow_eq_of_principal R h
  tfae_have 7 → 2
  · rw [ValuationRing.iff_ideal_total]
    intro H
    constructor
    intro I J
    -- `by_cases` should invoke `classical` by itself if it can't find a `Decidable` instance,
    -- however the `tfae` hypotheses trigger a looping instance search.
    -- See also:
    -- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60by_cases.60.20trying.20to.20find.20a.20weird.20instance
    -- As a workaround, add the desired instance ourselves.
    let _ := Classical.decEq (Ideal R)
    by_cases hI : I = ⊥; · subst hI; left; exact bot_le
    by_cases hJ : J = ⊥; · subst hJ; right; exact bot_le
    obtain ⟨n, rfl⟩ := H I hI
    obtain ⟨m, rfl⟩ := H J hJ
    cases' le_total m n with h' h'
    · left; exact Ideal.pow_le_pow h'
    · right; exact Ideal.pow_le_pow h'
  tfae_finish
#align discrete_valuation_ring.tfae DiscreteValuationRing.TFAE
