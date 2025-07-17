import Mathlib

open Nat Int

def bonza : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | ∀ a b : ℕ, 0 < a → 0 < b → (f a : ℤ) ∣ (b : ℤ) ^ a - (f b : ℤ) ^ (f a)}

def g : ℕ → ℕ := fun x ↦
  if ¬ 2 ∣ x then 1
  else if x = 2 then 4
  else 2 ^ (padicValNat 2 x + 2)

#check Int.sq_mod_four_eq_one_of_odd

lemma LTE {a b : ℕ} (h1b : 1 < b) (hb : ¬2 ∣ b) (ha : a ≠ 0) (Evena : Even a) :
    (padicValNat 2 a + 2) ≤ padicValNat 2 (b ^ a - 1) := by
  have dvd : 2 ∣ b - 1 := by
    simp at hb
    exact dvd_iff_mod_eq_zero.mpr (sub_mod_eq_zero_of_mod_eq hb)
  have := padicValNat.pow_two_sub_pow h1b dvd hb ha Evena
  simp at this
  have : padicValNat 2 (b ^ a - 1)
    = padicValNat 2 (b + 1) + padicValNat 2 (b - 1) + padicValNat 2 a - 1 := by omega
  rw [this]
  have Oddb : Odd b := by
    rcases dvd with ⟨m, hm⟩
    use m
    omega
  have : padicValNat 2 (b + 1) + padicValNat 2 (b - 1) ≥ 3 := by
    rw [← padicValNat.mul (by omega) (by omega)]
    have : (b + 1) * (b - 1) ≠ 0 := by
      simpa using by omega
    have dvd : 2 ^ 3 ∣ (b + 1) * (b - 1) := by
      have : (b + 1) * (b - 1) = b ^ 2 - 1 := by simp [Nat.pow_two_sub_pow_two b 1]
      simp [this]
      exact Nat.sq_mod_eight_eq_one_of_odd Oddb
    exact (padicValNat_dvd_iff_le (hp := fact_prime_two) this).mp dvd
  omega

lemma exist : g ∈ bonza := fun a b ha hb ↦ by
  by_cases ch1 : ¬ 2 ∣ a
  · simp [g, ch1]
  by_cases ch2 : a = 2
  · sorry
    -- simp [g, ch2]
    -- split_ifs with hb1 hb2
    -- · exact dvd_self_sub_of_emod_eq (sq_mod_four_eq_one_of_odd (by simpa using Nat.odd_iff.mpr hb1))
    -- · simp [hb2]
    -- · simp at hb1
    --   refine dvd_sub ?_ ?_
    --   · have : 2 ∣ (b : ℤ) := ofNat_dvd_natCast.mpr (dvd_of_mod_eq_zero hb1)
    --     have : 2 ^ 2 ∣ (b : ℤ) ^ 2 := pow_dvd_pow_of_dvd this 2
    --     simpa
    --   · refine Dvd.dvd.pow ?_ (by norm_num)
    --     use 2 ^ padicValNat 2 b
    --     ring
  · simp [g, ch1, ch2]
    split_ifs with hb1 hb2
    · by_cases lt : b = 1
      . simp [lt]
      have : (padicValNat 2 a + 2) ≤ padicValInt 2 (b ^ a - 1) := by
        have : ¬2 ∣ b := by
          exact Nat.two_dvd_ne_zero.mpr hb1
        simp at ch1
        have := LTE (by omega) (Nat.two_dvd_ne_zero.mpr hb1) (by omega) (Nat.even_iff.mpr ch1)
        have : padicValNat 2 (b ^ a - 1) = padicValInt 2 (b ^ a - 1) := by
          rw [← padicValInt.of_nat, LucasLehmer.Int.natCast_pow_pred b a hb]
        rwa [← this]
      have dvd1 : (2 : ℤ) ^ (padicValNat 2 a + 2) ∣ 2 ^ padicValInt 2 (b ^ a - 1) :=
        pow_dvd_pow 2 this
      have dvd2 : (2 : ℤ) ^ padicValInt 2 ((b : ℤ) ^ a - 1) ∣ (b : ℤ) ^ a - 1 :=
        padicValInt_dvd ((b : ℤ) ^ a - 1) (hp := fact_prime_two)
      exact Int.dvd_trans dvd1 dvd2
    · simp [hb2]
      refine dvd_sub ?_ ?_
      · have : padicValNat 2 a + 2 ≤ a := by

          sorry
        exact pow_dvd_pow 2 this
      sorry
    · refine dvd_sub ?_ ?_
      ·
        sorry
      ·
        sorry
  -- rw [g]
  -- split_ifs with ha1 ha2
  -- · rw [g]
  --   split_ifs with hb1 hb2
  --   · simp [ha2, hb2]
  --   · simp [ha2]
  --     · have : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
  --       rw [this]
  --       exact pow_dvd_pow_of_dvd (Int.ofNat_dvd_right.mpr hb1) 2
  --     ·
  --   · have : Odd (b : ℤ) := by
  --       rwa [Int.odd_iff, ← Int.two_dvd_ne_zero, ofNat_dvd_natCast]
  --     rw [Nat.cast_ofNat, ha2, Nat.cast_one, one_pow]
  --
  -- · rw [g]
  --   split_ifs with hb1 hb2
  --   · simp [hb2]
  --     refine dvd_sub ?_ ?_
  --     · rcases ha1 with ⟨k, hk⟩
  --       refine pow_dvd_pow 2 ?_
  --       rw [hk, padicValNat.mul (by norm_num) (by omega)]
  --       simp only [one_lt_ofNat, padicValNat.self]
  --       have : padicValNat 2 k < k := by
  --         calc
  --         _ ≤ Nat.log 2 k := padicValNat_le_nat_log k
  --         _ < _ := log_lt_self 2 (by omega)
  --       omega

  --     have : Fact (Nat.Prime 2) := by exact fact_prime_two

  --     have : 4 ^ 2 ^ (padicValNat 2 a + 2) ≠ 0 := by simp
  --     have tt :padicValNat 2 a + 2 ≤ padicValNat 2 (4 ^ 2 ^ (padicValNat 2 a + 2)) := by sorry
  --     have := (padicValNat_dvd_iff_le (p := 2) (n := padicValNat 2 a + 2) this).mpr tt
  --     -- apply?




  --     sorry
  --   · simp
  --     sorry
  --   · sorry
  --     -- by_cases hb3 : b = 1
  --     -- · simp [hb3]
  --     -- · have hyx : b > 1 := by omega
  --     --   have hxy : 2 ∣ b - 1 := by
  --     --     simp at hb1
  --     --     exact (modEq_iff_dvd' hb).mp (id (Eq.symm hb1))
  --     --   have neq : a ≠ 0 := by omega
  --     --   have := padicValNat.pow_two_sub_pow hyx hxy hb1 neq ((even_iff_exists_two_nsmul a).mpr ha1)
  --     --   simp
  --     --   have : 2 ^ (a.factorization 2 + 2) ∣ b ^ a - 1 := by
  --     --     have : (a.factorization 2 + 2) ≤ Nat.factorization (b ^ a - 1) 2 := by
  --     --       have : Nat.factorization (b ^ a - 1) 2 = padicValNat 2 (b ^ a - 1) := by
  --     --         rfl
  --     --       rw [this]
      --       have : padicValNat 2 (b - 1) ≥ 1 := by
      --         sorry

      --       sorry
      --     refine (Prime.pow_dvd_iff_le_factorization ?_ ?_).mpr this
      --     exact Nat.prime_two
      --     have : b ^ a > 1 := by
      --       exact one_lt_pow neq hyx
      --     exact Nat.sub_ne_zero_iff_lt.mpr this
      --   rcases this with ⟨l, hl⟩
      --   use l
      --   have := one_le_pow a b hb
      --   have : b ^ a = 1 + 2 ^ (a.factorization 2 + 2) * l := by
      --     omega
      --   have eq : (b : ℤ) ^ a = ((b ^ a : ℕ) : ℤ) := by
      --     simp
      --   simp [eq, this]
      -- simp
      -- refine pow_dvd_of_le_emultiplicity ?_
      -- have Odd_b : Odd b := by
      --   rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff] at hb1
      -- have dvd : 2 ∣ (b : ℤ) - 1 := by
      --   refine Int.dvd_self_sub_of_emod_eq ?_
      --   rwa [← Int.odd_iff, odd_coe_nat]
      -- have ndvd : ¬2 ∣ (b : ℤ) := by
      --   simpa [← Int.odd_iff, odd_coe_nat]
      -- have := Int.two_pow_sub_pow dvd ndvd ((even_iff_exists_two_nsmul a).mpr ha1)
      --
      -- simp at this
      -- have : emultiplicity 2 ((b : ℤ) - 1) ≥ 1 := by
      --   refine le_emultiplicity_of_pow_dvd ?_
      --   simpa

  --     -- sorry
  -- · simp

-- theorem my_favorite_theorem : IsLeast {c : ℝ | ∀ f : ℕ → ℕ, (∀ a b, 0 < a → 0 < b →
--     f a ∣ b ^ a - (f b) ^ (f a)) → ∀ n, 0 < n → f n ≤ c * n} 4 := by

--   sorry
