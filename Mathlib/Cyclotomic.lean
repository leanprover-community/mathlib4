import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Misc

namespace IsCyclotomicExtension.Rat

open Ideal NumberField

section general

variable (n : ℕ) [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  (p k m : ℕ) [hp : Fact (p.Prime)] (P : Ideal (𝓞 K)) [P.IsMaximal]
  [P.LiesOver (Ideal.span {(p : ℤ)})]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

open NumberField RingOfIntegers Ideal IntermediateField

set_option maxHeartbeats 250000 in
theorem IsCyclotomicExtension.Rat.inertiaDeg_ramificationIdx (hn : n = p ^ (k + 1) * m)
    (hm : ¬ p ∣ m) :
    inertiaDeg 𝒑 P = orderOf (p : ZMod m) ∧
      ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by
  classical
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  let ζ := zeta n ℚ K
  have hζ := zeta_spec n ℚ K
  -- Root of unity of order `m`
  let ζₘ := ζ ^ (p ^ (k + 1))
  have hζₘ := hζ.pow (NeZero.pos _) hn
  -- Root of unity of order `p ^ (k + 1)`
  let ζₚ := ζ ^ m
  have hζₚ := hζ.pow (NeZero.pos _) (mul_comm _ m ▸ hn)
  let Fₘ := ℚ⟮ζₘ⟯
  have : IsCyclotomicExtension {m} ℚ Fₘ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₘ).mpr rfl
  let Fₚ := ℚ⟮ζₚ⟯
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ Fₚ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₚ).mpr rfl
  -- The prime ideal of `ℚ⟮ζₘ⟯` below `P`
  let Pₘ := comap (algebraMap (𝓞 Fₘ) (𝓞 K)) P
  have : Pₘ.IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal _
  -- The prime ideal of `ℚ⟮ζₚ⟯` below `P`
  let Pₚ := comap (algebraMap (𝓞 Fₚ) (𝓞 K)) P
  have : Pₚ.IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal _
  have h₁ := ramificationIdx_algebra_tower (p := 𝒑) (P := Pₚ) (Q := P)
    (by
      refine map_ne_bot_of_ne_bot ?_
      apply Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (not_isField Fₚ))
    (by
      apply map_ne_bot_of_ne_bot
      simpa using hp.out.ne_zero)
    (by
      apply Ideal.map_comap_le)
  have h₂ := inertiaDeg_algebra_tower 𝒑 Pₘ P
  have h₃ : (𝒑.primesOver (𝓞 K)).ncard = (𝒑.primesOver (𝓞 Fₘ)).ncard *
      (Pₘ.primesOver (𝓞 K)).ncard := by
    rw [ncard_primesOver_eq_sum_ncard_primesOver ℤ (𝓞 Fₘ)]
    conv_lhs =>
      enter [2, P]
      rw [ncard_primesOver_eq_ncard_primesOver ℚ Fₘ K 𝒑 P.val Pₘ]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
    (by simpa using hp.out.ne_zero) (𝓞 K) ℚ K
  rw [finrank n K, hn, Nat.totient_mul, Nat.totient_prime_pow, add_tsub_cancel_right] at h_main
  · rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P ℚ K] at h_main
    rw [inertiaDegIn_eq_inertiaDeg 𝒑 P ℚ K] at h_main
    rw [h₁, h₂, h₃] at h_main
    rw [ramificationIdx_eq_of_prime_pow p k] at h_main
    rw [← finrank m Fₘ] at h_main
    rw [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
      (by simpa using hp.out.ne_zero) (𝓞 Fₘ)
      ℚ Fₘ] at h_main
    rw [ramificationIdxIn_eq_ramificationIdx 𝒑 Pₘ ℚ Fₘ] at h_main
    rw [inertiaDegIn_eq_inertiaDeg 𝒑 Pₘ ℚ Fₘ] at h_main
    rw [ramificationIdx_of_not_dvd m, one_mul] at h_main
    · ring_nf at h_main
      simp_rw [mul_assoc] at h_main
      rw [Nat.mul_right_inj] at h_main
      · rw [mul_comm (𝒑.inertiaDeg Pₘ)] at h_main
        simp_rw [← mul_assoc] at h_main
        rw [Nat.mul_left_inj] at h_main
        · suffices (Pₘ.primesOver (𝓞 K)).ncard * ramificationIdx (algebraMap (𝓞 Fₚ) (𝓞 K)) Pₚ P *
              Pₘ.inertiaDeg P = 1 by
            rw [h₁, h₂]
            rw [Nat.eq_one_of_mul_eq_one_left this]
            rw [Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right this)]
            rw [mul_one, mul_one, inertiaDeg_of_not_dvd m, ramificationIdx_eq_of_prime_pow p k]
            · exact Nat.pair_eq_pair.mp rfl
            · exact hm
          rwa [mul_assoc _ (p ^ k), mul_comm (Pₘ.primesOver (𝓞 K)).ncard, mul_assoc, mul_assoc,
            Nat.mul_eq_left, ← mul_assoc] at h_main
          · exact Nat.mul_ne_zero_iff.mpr ⟨NeZero.ne _, Nat.sub_ne_zero_iff_lt.mpr hp.out.one_lt⟩
        · exact inertiaDeg_ne_zero _ _
      · apply primesOver_ncard_ne_zero
    · exact hm
  · exact hp.out
  · exact Nat.zero_lt_succ k
  · refine Nat.Coprime.pow_left (k + 1) ?_
    exact not_not.mp <| (Nat.Prime.dvd_iff_not_coprime hp.out).not.mp hm



end general

end IsCyclotomicExtension.Rat





theorem IsCyclotomicExtension_single_iff_single_two_mul_of_odd (n : ℕ) (hn : Odd n)
    (A B : Type*) [CommRing A] [CommRing B] [Nontrivial B] [NoZeroDivisors B] [Algebra A B]
    (hB : ringChar B ≠ 2) :
    IsCyclotomicExtension {n} A B ↔ IsCyclotomicExtension {2 * n} A B := by
  have : NeZero n := by
    refine ⟨?_⟩
    exact Nat.ne_of_odd_add hn
  have h : orderOf (-1 : B) = 2 := by
    rw [orderOf_neg_one, if_neg hB]
  rw [IsCyclotomicExtension.iff_singleton, IsCyclotomicExtension.iff_singleton]
  congr! 1
  · refine ⟨?_, ?_⟩
    · intro ⟨ζ, hζ⟩
      refine ⟨-ζ, ?_⟩
      convert IsPrimitiveRoot.orderOf (-ζ)
      rw [neg_eq_neg_one_mul, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
      · rw [h, hζ.eq_orderOf]
      · rw [h, ← hζ.eq_orderOf]
        exact Nat.coprime_two_left.mpr hn
    · intro ⟨ζ, hζ⟩
      exact ⟨ζ ^ 2, hζ.pow (NeZero.pos _) rfl⟩
  · suffices Algebra.adjoin A {b : B | b ^ n = 1} = Algebra.adjoin A {b : B | b ^ (2 * n) = 1} by
      rw [SetLike.ext_iff] at this
      exact forall_congr' this
    apply le_antisymm
    · apply Algebra.adjoin_mono
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, hb, one_pow]
    · apply Algebra.adjoin_le
      intro b hb
      rw [Set.mem_setOf_eq, mul_comm, pow_mul, sq_eq_one_iff] at hb
      obtain hb | hb := hb
      · apply Algebra.subset_adjoin
        exact hb
      · simp only [SetLike.mem_coe]
        rw [show b = - - b by exact Eq.symm (InvolutiveNeg.neg_neg b)]
        apply Subalgebra.neg_mem
        apply Algebra.subset_adjoin
        rw [Set.mem_setOf_eq, neg_pow, Odd.neg_one_pow hn, neg_mul, one_mul, hb, neg_neg]



-- Golf `IsCyclotomicExtension.of_union_of_dvd` using this
theorem IsCyclotomicExtension.exists_prim_root_of_dvd {n : ℕ} [NeZero n] {S : Set ℕ} (A B : Type*)
    [CommRing A] [CommRing B] [Algebra A B] (h : ∃ s ∈ S, s ≠ 0 ∧ n ∣ s)
    [H : IsCyclotomicExtension S A B] :
    ∃ (r : B), IsPrimitiveRoot r n := by
  obtain ⟨m, hm, hm', ⟨x, rfl⟩⟩ := h
  obtain ⟨ζ, hζ⟩ := H.exists_isPrimitiveRoot hm hm'
  refine ⟨ζ ^ x, ?_⟩
  have h_xnz : x ≠ 0 := Nat.ne_zero_of_mul_ne_zero_right hm'
  have := hζ.pow_of_dvd h_xnz (dvd_mul_left x n)
  rwa [mul_div_cancel_right₀ _ h_xnz] at this

open NumberField Units

theorem NumberField.Units.mem_torsion' (K : Type*) [Field K] [NumberField K]
    {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ IsOfFinOrder x := CommGroup.mem_torsion _ _

theorem NumberField.dvd_torsionOrder_of_isPrimitiveRoot {n : ℕ} [NeZero n] {K : Type*} [Field K]
    [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    n ∣ torsionOrder K := by
  rw [torsionOrder, Fintype.card_eq_nat_card]
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  have hζ' := CommGroup.mem_torsion_of_isPrimitiveRoot n hζ
  convert orderOf_dvd_natCard (⟨_, hζ'⟩ : torsion K)
  rw [Subgroup.orderOf_mk]
  exact hζ.eq_orderOf

theorem NumberField.Units.torsionOrder_eq_of_isCyclotomicExtension (n : ℕ) [NeZero n] {K : Type*}
    [Field K] [NumberField K] [hK : IsCyclotomicExtension {n} ℚ K] :
    torsionOrder K = if Even n then n else 2 * n := by
  have hζ := hK.zeta_spec
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
    rw [torsionOrder, Fintype.card_eq_nat_card]
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have h := IsPrimitiveRoot.pow_mul_pow_lcm hζ hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  have : NeZero (n.lcm (torsionOrder K)) :=
    NeZero.of_pos <| Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  have : IsCyclotomicExtension {n.lcm (torsionOrder K)} ℚ K := by
    have := hK.union_of_isPrimitiveRoot _ _ _ h
    rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
    exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  have hmain := (IsCyclotomicExtension.Rat.finrank n K).symm.trans <|
    (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  obtain hn | hn := Nat.even_or_odd n
  · rw [if_pos hn]
    apply dvd_antisymm
    · have := Nat.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hn hmain
      rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
    · exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) hmain).resolve_left ?_
    · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
      exact NumberField.dvd_torsionOrder_of_isPrimitiveRoot hζ
    · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
      intro h
      exact Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)
