/-
  # Sophie Germain's Theorem (Classical Version)

  If p is a Sophie Germain prime (i.e. p and 2p+1 are both prime, with p odd),
  then the Fermat equation  x^p + y^p = z^p  has no integer solutions
  where none of x, y, z is divisible by p.

  ## Proof outline
  1. Define Sophie Germain primes and establish basic mod-q properties (q = 2p+1).
  2. Introduce the "Sophie Germain sum" S(x,y,p) = Σ (-y)^{p-1-k} x^k and show
     that (x+y) · S = x^p + y^p, with (x+y) and S coprime when p∤x.
  3. By coprimality, each factor is itself a perfect p-th power.
  4. Combine mod-q constraints to derive a contradiction: p would need to be
     congruent to -1, 0, or 1 mod q, which is impossible for p ≥ 3.
-/
import Mathlib

open Finset BigOperators Int

noncomputable section

/-! ============================================================================
    PART I: PREREQUISITES — Modular Arithmetic & GCD Helpers
    ============================================================================ -/

/-! ### Summing congruences over a finset -/

private theorem Int.ModEq.finset_sum {ι : Type*} {n : ℤ} {s : Finset ι} {f g : ι → ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD n]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD n] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, Finset.sum_insert hna]
    exact (h _ (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Bridging ℕ-divisibility (natAbs) and ℤ-divisibility -/

private lemma natCast_dvd_of_dvd_natAbs {k : ℕ} {z : ℤ} (h : k ∣ z.natAbs) :
    (↑k : ℤ) ∣ z := by
  rcases Int.natAbs_eq z with heq | heq
  · rw [heq]; exact_mod_cast h
  · rw [heq]; exact dvd_neg.mpr (by exact_mod_cast h)

private lemma dvd_natAbs_of_natCast_dvd {k : ℕ} {z : ℤ} (h : (↑k : ℤ) ∣ z) :
    k ∣ z.natAbs := by
  obtain ⟨c, hc⟩ := h
  rw [hc, Int.natAbs_mul, Int.natAbs_natCast]; exact dvd_mul_right k c.natAbs

private lemma int_gcd_dvd_left (a b : ℤ) : (↑(Int.gcd a b) : ℤ) ∣ a :=
  natCast_dvd_of_dvd_natAbs (Nat.gcd_dvd_left a.natAbs b.natAbs)

private lemma int_gcd_dvd_right (a b : ℤ) : (↑(Int.gcd a b) : ℤ) ∣ b :=
  natCast_dvd_of_dvd_natAbs (Nat.gcd_dvd_right a.natAbs b.natAbs)

private lemma int_dvd_gcd {m n : ℤ} {k : ℕ} (hm : (↑k : ℤ) ∣ m) (hn : (↑k : ℤ) ∣ n) :
    k ∣ Int.gcd m n :=
  Nat.dvd_gcd (dvd_natAbs_of_natCast_dvd hm) (dvd_natAbs_of_natCast_dvd hn)

/-! ### Coprime power extraction

  If a·b = c^n with gcd(a,b) = 1, then a is a perfect n-th power (up to sign).
  We prove this first over ℕ by induction on the prime factorization, then lift
  to ℤ. -/

private lemma Nat.eq_pow_of_coprime_mul_pow :
    ∀ (a : ℕ), ∀ {b c n : ℕ},
      Nat.Coprime a b → a * b = c ^ n → ∃ d : ℕ, a = d ^ n := by
  intro a
  induction a using Nat.recOnPrimeCoprime with
  | zero =>
    intro b c n _ heq; simp only [zero_mul] at heq
    exact ⟨0, by
      by_cases hn : n = 0
      · exact absurd heq (by simp [hn])
      · exact (zero_pow hn).symm⟩
  | prime_pow p k hp =>
    intro b c n hcop heq
    by_cases hk : k = 0; · exact ⟨1, by subst hk; simp⟩
    by_cases hn : n = 0
    · exfalso; simp only [hn, pow_zero] at heq
      have h1 := Nat.one_lt_pow hk hp.one_lt
      have h2 : p ^ k ≤ 1 := Nat.le_of_dvd one_pos ⟨b, heq.symm⟩
      omega
    by_cases hb : b = 0
    · exfalso; rw [hb, Nat.coprime_zero_right] at hcop
      have := Nat.one_lt_pow hk hp.one_lt; omega
    by_cases hc : c = 0
    · simp only [hc, zero_pow hn, mul_eq_zero] at heq
      exact absurd (heq.resolve_left (pow_ne_zero k hp.ne_zero)) hb
    -- The p-adic valuation of p^k · b equals k (since p ∤ b by coprimality).
    -- The p-adic valuation of c^n equals n · v_p(c). So n ∣ k.
    have hpndb : ¬ p ∣ b := by
      intro hpb; have h1 := Nat.dvd_gcd (dvd_pow_self p hk) hpb; rw [hcop] at h1
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.one_lt; omega)
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have hvl : padicValNat p (p ^ k * b) = k := by
      rw [padicValNat.mul (pow_ne_zero k hp.ne_zero) hb]
      rw [show padicValNat p (p ^ k) = k from by
            rw [padicValNat.pow k hp.ne_zero, padicValNat.self hp.one_lt, mul_one]]
      rw [padicValNat.eq_zero_of_not_dvd hpndb, add_zero]
    have hvr : padicValNat p (c ^ n) = n * padicValNat p c :=
      padicValNat.pow n hc
    have hndvdk : n ∣ k := ⟨padicValNat p c,
       by have := congr_arg (padicValNat p) heq; rwa [hvl, hvr] at this⟩
    exact ⟨p ^ (k / n), by rw [← pow_mul, Nat.div_mul_cancel hndvdk]⟩
  | coprime a₁ a₂ _ _ hcop₁₂ ih₁ ih₂ =>
    -- If a = a₁·a₂ with gcd(a₁,a₂)=1, apply induction to each factor.
    intro b c n hcop heq
    have hcop_a₁_b := Nat.Coprime.coprime_dvd_left (dvd_mul_right a₁ a₂) hcop
    have hcop_a₂_b := Nat.Coprime.coprime_dvd_left (dvd_mul_left a₂ a₁) hcop
    obtain ⟨d₁, hd₁⟩ := ih₁ (hcop₁₂.mul_right hcop_a₁_b)
      (by convert heq using 1; ring)
    obtain ⟨d₂, hd₂⟩ := ih₂ (hcop₁₂.symm.mul_right hcop_a₂_b)
      (by convert heq using 1; ring)
    exact ⟨d₁ * d₂, by rw [mul_pow, ← hd₁, ← hd₂]⟩

/-- Over ℤ: if gcd(a,b)=1 and a·b = c^n, then a = ±(d^n) for some d. -/
theorem eq_pow_or_neg_of_coprime_mul_pow {a b c : ℤ} {n : ℕ}
    (hcop : IsCoprime a b) (heq : a * b = c ^ n) :
    ∃ α : ℤ, a = α ^ n ∨ a = -(α ^ n) := by
  have hcop_nat : Nat.Coprime a.natAbs b.natAbs :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop
  have heq_nat : a.natAbs * b.natAbs = c.natAbs ^ n := by
    have h := congr_arg Int.natAbs heq; rwa [Int.natAbs_mul, Int.natAbs_pow] at h
  obtain ⟨d, hd⟩ := Nat.eq_pow_of_coprime_mul_pow a.natAbs hcop_nat heq_nat
  refine ⟨(d : ℤ), ?_⟩
  have hnat : (a.natAbs : ℤ) = (↑d : ℤ) ^ n := by exact_mod_cast hd
  rcases Int.natAbs_eq a with hab | hab <;> [left; right] <;> omega

/-! ### GCD normalization

  Dividing x, y, z by gcd(gcd(x,y), z) produces a triple with setwise gcd 1. -/

lemma Int.gcd_div_gcd_eq_one (x y z : ℤ) (h : z ≠ 0) :
    let d : ℤ := ↑(Int.gcd (↑(Int.gcd x y)) z)
    Int.gcd (↑(Int.gcd (x / d) (y / d))) (z / d) = 1 := by
  set g : ℕ := Int.gcd (↑(Int.gcd x y)) z
  set G : ℤ := ↑g
  have hg_pos : 0 < g := by
    rw [Nat.pos_iff_ne_zero]; intro heq; exact h (Int.gcd_eq_zero_iff.mp heq).2
  have hG_ne : G ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hG_dvd_x : G ∣ x := dvd_trans (int_gcd_dvd_left _ _) (int_gcd_dvd_left _ _)
  have hG_dvd_y : G ∣ y := dvd_trans (int_gcd_dvd_left _ _) (int_gcd_dvd_right _ _)
  have hG_dvd_z : G ∣ z := int_gcd_dvd_right _ _
  -- If the quotient gcd ≠ 1, some prime r divides all of x/G, y/G, z/G,
  -- so r·G divides each of x, y, z, contradicting the definition of G.
  by_contra hne
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
  have hr_dvd_xG : (↑r : ℤ) ∣ x / G := natCast_dvd_of_dvd_natAbs
    (dvd_trans (dvd_trans hr_dvd (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_left _ _))
  have hr_dvd_yG : (↑r : ℤ) ∣ y / G := natCast_dvd_of_dvd_natAbs
    (dvd_trans (dvd_trans hr_dvd (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _))
  have hr_dvd_zG : (↑r : ℤ) ∣ z / G := natCast_dvd_of_dvd_natAbs
    (dvd_trans hr_dvd (Nat.gcd_dvd_right _ _))
  have hrG_dvd (w : ℤ) (hw : G ∣ w) (hdvd : (↑r : ℤ) ∣ w / G) : ↑r * G ∣ w := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by rw [← Int.ediv_mul_cancel hw, hk]; ring⟩
  have hrg_dvd_g : r * g ∣ g := by
    apply int_dvd_gcd
    · have : r * g ∣ Int.gcd x y :=
        int_dvd_gcd (by push_cast; exact hrG_dvd x hG_dvd_x hr_dvd_xG)
                    (by push_cast; exact hrG_dvd y hG_dvd_y hr_dvd_yG)
      exact_mod_cast this
    · push_cast; exact hrG_dvd z hG_dvd_z hr_dvd_zG
  have : r * g ≤ g := Nat.le_of_dvd hg_pos hrg_dvd_g
  nlinarith [hr_prime.two_le]

/-! ### Pairwise coprimality from setwise coprimality in a Fermat equation

  If x^p + y^p = z^p with gcd(gcd(x,y),z)=1, then x,y,z are pairwise coprime.
  Any common prime factor of two variables divides the third (by the equation),
  contradicting the setwise gcd assumption. -/

lemma pairwise_coprime_of_fermat_eq {x y z : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hfermat : x ^ p + y ^ p = z ^ p)
    (hsetwise : Int.gcd (↑(Int.gcd x y)) z = 1) :
    IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  -- A prime dividing two of {x,y,z} must divide the third, by the Fermat equation.
  have absorb_xy : ∀ (r : ℤ), Prime r → r ∣ x → r ∣ y → r ∣ z := by
    intro r hr hrx hry
    have : r ∣ x ^ p + y ^ p := dvd_add (dvd_pow hrx hp_ne) (dvd_pow hry hp_ne)
    rw [hfermat] at this; exact hr.dvd_of_dvd_pow this
  have absorb_yz : ∀ (r : ℤ), Prime r → r ∣ y → r ∣ z → r ∣ x := by
    intro r hr hry hrz
    have : r ∣ z ^ p - y ^ p := dvd_sub (dvd_pow hrz hp_ne) (dvd_pow hry hp_ne)
    rw [show z ^ p - y ^ p = x ^ p from by linarith] at this; exact hr.dvd_of_dvd_pow this
  have absorb_xz : ∀ (r : ℤ), Prime r → r ∣ x → r ∣ z → r ∣ y := by
    intro r hr hrx hrz
    have : r ∣ z ^ p - x ^ p := dvd_sub (dvd_pow hrz hp_ne) (dvd_pow hrx hp_ne)
    rw [show z ^ p - x ^ p = y ^ p from by linarith] at this; exact hr.dvd_of_dvd_pow this
  -- But then it divides all three, contradicting gcd = 1.
  have hset : ∀ (r : ℤ), Prime r → r ∣ x → r ∣ y → r ∣ z → False := by
    intro r hr hrx hry hrz
    have h1 : r.natAbs ∣ Int.gcd x y :=
      int_dvd_gcd (Int.natAbs_dvd.mpr hrx) (Int.natAbs_dvd.mpr hry)
    have h2 : r.natAbs ∣ Int.gcd (↑(Int.gcd x y)) z :=
      int_dvd_gcd (by exact_mod_cast h1) (Int.natAbs_dvd.mpr hrz)
    rw [hsetwise] at h2
    have habs1 : r.natAbs = 1 := Nat.dvd_one.mp h2
    exact hr.not_unit (Int.isUnit_iff.mpr (by
      rcases Int.natAbs_eq r with h | h <;> [left; right] <;> omega))
  -- Generic coprimality argument: if any common prime leads to contradiction, coprime.
  have coprime_from_absorb : ∀ (a b c : ℤ),
      (∀ r : ℤ, Prime r → r ∣ a → r ∣ b → r ∣ c) →
      (∀ r : ℤ, Prime r → r ∣ a → r ∣ b → r ∣ c → False) →
      IsCoprime a b := by
    intro a b c hab hcontra
    rw [Int.isCoprime_iff_gcd_eq_one]; by_contra hne
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
    have hra : (↑r : ℤ) ∣ a := natCast_dvd_of_dvd_natAbs
      (dvd_trans hr_dvd (Nat.gcd_dvd_left _ _))
    have hrb : (↑r : ℤ) ∣ b := natCast_dvd_of_dvd_natAbs
      (dvd_trans hr_dvd (Nat.gcd_dvd_right _ _))
    have hr_int : Prime (↑r : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simp [hr_prime])
    exact hcontra ↑r hr_int hra hrb (hab ↑r hr_int hra hrb)
  exact ⟨coprime_from_absorb x y z absorb_xy (fun r hr a b c => hset r hr a b c),
         coprime_from_absorb y z x absorb_yz (fun r hr a b c => hset r hr c a b),
         coprime_from_absorb x z y absorb_xz (fun r hr a b c => hset r hr a c b)⟩

/-! Divisibility utility (currently unused; retained for potential downstream use). -/

lemma not_dvd_of_not_dvd_div {a d m : ℤ} (hd : d ∣ a) (hm : ¬ m ∣ a) :
    ¬ m ∣ (a / d) := by
  intro ⟨k, hk⟩
  exact hm ⟨k * d, by rw [← Int.ediv_mul_cancel hd, hk, mul_assoc]⟩

/-! ============================================================================
    PART II: SOPHIE GERMAIN PRIMES
    ============================================================================ -/

/-! ### Definition and basic API -/

/-- A Sophie Germain prime is an odd prime p such that 2p+1 is also prime. -/
def SophieGermainPrime (p : ℕ) : Prop :=
  Odd p ∧ Nat.Prime p ∧ Nat.Prime (2 * p + 1)

namespace SophieGermainPrime
variable {p : ℕ}

theorem odd (hSG : SophieGermainPrime p) : Odd p := hSG.1
theorem prime (hSG : SophieGermainPrime p) : Nat.Prime p := hSG.2.1
theorem prime_twop_succ (hSG : SophieGermainPrime p) : Nat.Prime (2 * p + 1) := hSG.2.2
theorem pos (hSG : SophieGermainPrime p) : 0 < p := hSG.prime.pos
theorem ne_zero (hSG : SophieGermainPrime p) : p ≠ 0 := hSG.prime.ne_zero
theorem ge_three (hSG : SophieGermainPrime p) : 3 ≤ p := by
  obtain ⟨k, hk⟩ := hSG.odd; have := hSG.prime.two_le; omega

/-! ### Mod-q properties (q = 2p+1)

  By Fermat's little theorem, m^{q-1} = m^{2p} ≡ 1 (mod q) when q ∤ m.
  Since m^{2p} = (m^p)², we get m^p ≡ ±1 (mod q). -/

theorem pow_congr_one_or_neg_one (hSG : SophieGermainPrime p) {m : ℤ}
    (hndvd : ¬ ((2 * (p : ℤ) + 1) ∣ m)) :
    m ^ p ≡ 1 [ZMOD (2 * (p : ℤ) + 1)] ∨ m ^ p ≡ -1 [ZMOD (2 * (p : ℤ) + 1)] := by
  set q := 2 * p + 1
  have hq_prime := hSG.prime_twop_succ
  have hq_cast : (↑q : ℤ) = 2 * (↑p : ℤ) + 1 := by omega
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  have hm_ne : (m : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; rwa [hq_cast]
  -- Fermat's little theorem: m^{q-1} ≡ 1, and q-1 = 2p
  have hflt := ZMod.pow_card_sub_one_eq_one hm_ne
  have hqs : q - 1 = 2 * p := by omega
  rw [hqs] at hflt
  -- (m^p)² = 1, so (m^p - 1)(m^p + 1) = 0 in ZMod q
  have hsq : ((m : ZMod q) ^ p) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact hflt
  have hfact : ((m : ZMod q) ^ p - 1) * ((m : ZMod q) ^ p + 1) = 0 := by
    have h : ((m : ZMod q) ^ p - 1) * ((m : ZMod q) ^ p + 1) =
             ((m : ZMod q) ^ p) ^ 2 - 1 ^ 2 := by ring
    rw [h, hsq]; norm_num
  -- Since q is prime, ZMod q is a domain, so one factor is zero.
  rcases mul_eq_zero.mp hfact with h | h
  · left
    have hmp : (m : ZMod q) ^ p = 1 := sub_eq_zero.mp h
    have hconv : (↑(m ^ p) : ZMod q) = (↑(1 : ℤ) : ZMod q) := by push_cast; exact hmp
    rw [← hq_cast]; exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hconv
  · right
    have hmp : (m : ZMod q) ^ p = -1 := add_eq_zero_iff_eq_neg.mp h
    have hconv : (↑(m ^ p) : ZMod q) = (↑(-1 : ℤ) : ZMod q) := by push_cast; exact hmp
    rw [← hq_cast]; exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hconv

/-! ### Small residues cannot equal p mod q

  Since p ≥ 3 and q = 2p+1 ≥ 7, the values -1, 0, 1 are too far from p
  for the difference to be divisible by q. -/

theorem p_not_congr_neg_one (hSG : SophieGermainPrime p) :
    ¬ ((-1 : ℤ) ≡ (p : ℤ) [ZMOD (2 * (p : ℤ) + 1)]) := by
  intro h; rw [Int.modEq_iff_dvd] at h
  have heq : (↑p : ℤ) - -1 = ↑p + 1 := by ring
  rw [heq] at h
  have h3 : (3 : ℤ) ≤ ↑p := by exact_mod_cast hSG.ge_three
  exact absurd (Int.le_of_dvd (by linarith) h) (by linarith)

theorem p_not_congr_zero (hSG : SophieGermainPrime p) :
    ¬ ((0 : ℤ) ≡ (p : ℤ) [ZMOD (2 * (p : ℤ) + 1)]) := by
  intro h; rw [Int.modEq_iff_dvd] at h
  have heq : (↑p : ℤ) - 0 = ↑p := by ring
  rw [heq] at h
  have h3 : (3 : ℤ) ≤ ↑p := by exact_mod_cast hSG.ge_three
  exact absurd (Int.le_of_dvd (by linarith) h) (by linarith)

theorem p_not_congr_one (hSG : SophieGermainPrime p) :
    ¬ ((1 : ℤ) ≡ (p : ℤ) [ZMOD (2 * (p : ℤ) + 1)]) := by
  intro h; rw [Int.modEq_iff_dvd] at h
  have h3 : (3 : ℤ) ≤ ↑p := by exact_mod_cast hSG.ge_three
  exact absurd (Int.le_of_dvd (by linarith) h) (by linarith)

/-! ### In a Fermat triple, q must divide at least one variable

  If x^p + y^p = z^p and q ∤ x, q ∤ y, q ∤ z, then each p-th power is ±1 mod q.
  Checking all 2³ = 8 sign combinations: ±1 ± 1 ∓ 1 can never equal 0 mod q
  (since q ≥ 7 and the sum is at most 3 in absolute value). -/

theorem q_dvd_of_fermat_triple
    (hSG : SophieGermainPrime p) {x y z : ℤ}
    (hfermat : x ^ p + y ^ p = z ^ p)
    (hqx : ¬ (↑(2 * p + 1) : ℤ) ∣ x)
    (hqy : ¬ (↑(2 * p + 1) : ℤ) ∣ y)
    (hqz : ¬ (↑(2 * p + 1) : ℤ) ∣ z) : False := by
  have hp3 : 3 ≤ p := hSG.ge_three
  have hq_cast : (↑(2 * p + 1) : ℤ) = 2 * (↑p : ℤ) + 1 := by omega
  have hx_mod := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hqx)
  have hy_mod := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hqy)
  have hz_mod := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hqz)
  have h0 : x ^ p + y ^ p - z ^ p ≡ 0 [ZMOD (2 * (↑p : ℤ) + 1)] := by
    rw [show x ^ p + y ^ p - z ^ p = 0 from by linarith]
  have hp_int : (3 : ℤ) ≤ ↑p := by exact_mod_cast hp3
  -- Enumerate all eight sign combinations and derive contradiction
  rcases hx_mod with hxv | hxv <;> rcases hy_mod with hyv | hyv <;>
  rcases hz_mod with hzv | hzv <;> (
    have h_cong := (hxv.add hyv).sub hzv
    have h_zero := h_cong.symm.trans h0
    rw [Int.modEq_iff_dvd] at h_zero; obtain ⟨c, hc⟩ := h_zero
    have h2p1_pos : (0 : ℤ) ≤ 2 * ↑p + 1 := by linarith
    have hcz : c = 0 := by
      by_contra hc_ne
      rcases (show c ≥ 1 ∨ c ≤ -1 from by omega) with hpos | hneg
      · have := le_mul_of_one_le_right h2p1_pos hpos; linarith
      · have := mul_le_mul_of_nonneg_left hneg h2p1_pos; linarith
    simp only [hcz, mul_zero] at hc; omega)

end SophieGermainPrime

/-! ============================================================================
    PART III: THE SOPHIE GERMAIN SUM
    ============================================================================ -/

/-! ### Definition

  S(x,y,p) = Σ_{k=0}^{p-1} (-y)^{p-1-k} · x^k

  This is the cofactor in the factorization x^p + y^p = (x+y) · S(x,y,p)
  (valid when p is odd). -/

def SophieGermainSum (x y : ℤ) (p : ℕ) : ℤ :=
  ∑ k ∈ Finset.range p, (-y) ^ (p - 1 - k) * x ^ k

local notation "S" => SophieGermainSum

/-! ### Key identity: (x+y) · S(x,y,p) = x^p + y^p -/

theorem sgSum_mul_eq_pow_add_pow {p : ℕ} {x y : ℤ} (hodd : Odd p) :
    (x + y) * S x y p = x ^ p + y ^ p := by
  have h_eq : S x y p = ∑ i ∈ Finset.range p, x ^ i * (-y) ^ (p - 1 - i) := by
    simp only [SophieGermainSum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [h_eq, show x + y = x - (-y) from by ring, mul_comm, geom_sum₂_mul]
  rw [Odd.neg_pow hodd]; ring

/-! ### When y ≡ -x (mod n), the sum simplifies to p · x^{p-1} (mod n)

  Each term (-y)^{p-1-k} · x^k becomes x^{p-1} mod n, so the sum of p
  such terms is p · x^{p-1}. -/

theorem sgSum_congr_mod {p : ℕ} {x y n : ℤ}
    (_hp : p ≠ 0) (hcong : y ≡ -x [ZMOD n]) :
    S x y p ≡ ↑p * x ^ (p - 1) [ZMOD n] := by
  have hny : (-y) ≡ x [ZMOD n] := by have h := hcong.neg; rwa [neg_neg] at h
  have hterm : ∀ k ∈ Finset.range p,
      (-y) ^ (p - 1 - k) * x ^ k ≡ x ^ (p - 1) [ZMOD n] := by
    intro k hk; have hk' := Finset.mem_range.mp hk
    calc (-y) ^ (p - 1 - k) * x ^ k
        ≡ x ^ (p - 1 - k) * x ^ k [ZMOD n] := (hny.pow _).mul_right _
      _ = x ^ (p - 1 - k + k) := by rw [← pow_add]
      _ = x ^ (p - 1) := by congr 1; omega
  unfold SophieGermainSum
  calc ∑ k ∈ Finset.range p, (-y) ^ (p - 1 - k) * x ^ k
      ≡ ∑ _ ∈ Finset.range p, x ^ (p - 1) [ZMOD n] := Int.ModEq.finset_sum hterm
    _ = ↑(Finset.range p).card • x ^ (p - 1) := Finset.sum_const _
    _ = ↑p * x ^ (p - 1) := by rw [Finset.card_range, nsmul_eq_mul]

/-! ### (x+y) divides S(x,y,p) - p · x^{p-1} -/

theorem sum_dvd_sgSum_sub_scalar {p : ℕ} {x y : ℤ} (hodd : Odd p) :
    (x + y) ∣ (S x y p - ↑p * x ^ (p - 1)) := by
  have hp : p ≠ 0 := Odd.pos hodd |>.ne'
  have hcong : y ≡ -x [ZMOD (x + y)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  have h := (sgSum_congr_mod hp hcong).symm
  rwa [Int.modEq_iff_dvd] at h

/-! ============================================================================
    PART IV: THE FACTORIZATION LEMMA
    ============================================================================

  If x^p + y^p + z^p = 0 with p prime and odd, p ∤ x, and gcd(y,z) = 1,
  then both (y+z) and S(y,z,p) are perfect p-th powers.
  This follows because their product is (-x)^p and they are coprime. -/

theorem sophie_germain_factorization {p : ℕ} {x y z : ℤ}
    (hodd : Odd p) (hprime : Nat.Prime p)
    (hfermat : x ^ p + y ^ p + z ^ p = 0)
    (hx_mod : ¬ ((↑p : ℤ) ∣ x))
    (hcop_yz : IsCoprime y z) :
    ∃ a α, y + z = a ^ p ∧ S y z p = α ^ p := by
  -- Factorize: (y+z) · S(y,z,p) = y^p + z^p = (-x)^p
  have hfact : (y + z) * S y z p = y ^ p + z ^ p := sgSum_mul_eq_pow_add_pow hodd
  have hprod : (y + z) * S y z p = (-x) ^ p := by rw [hfact, Odd.neg_pow hodd]; linarith
  -- Show (y+z) and S are coprime: any common prime factor would divide p,
  -- forcing p | x (contradiction).
  have hcop_factors : IsCoprime (y + z) (S y z p) := by
    rw [isCoprime_comm]; by_contra hncop
    have hyz_ne : y + z ≠ 0 := by
      intro h; rw [h, zero_mul] at hprod
      exact hx_mod (dvd_neg.mp ((Int.prime_iff_natAbs_prime.mpr (by simp [hprime])).dvd_of_dvd_pow
        (hprod ▸ dvd_zero _)))
    have hS_ne : S y z p ≠ 0 := by
      intro h; rw [h, mul_zero] at hprod
      exact hx_mod (dvd_neg.mp ((Int.prime_iff_natAbs_prime.mpr (by simp [hprime])).dvd_of_dvd_pow
        (hprod ▸ dvd_zero _)))
    rw [← isRelPrime_iff_isCoprime,
        UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hS_ne] at hncop
    push_neg at hncop
    obtain ⟨q, hqS, hqyz, hq_prime⟩ := hncop
    -- q | (y+z) and q | S  ⟹  q | x
    have hq_dvd_x : q ∣ x := dvd_neg.mp (hq_prime.dvd_of_dvd_pow
      (hprod ▸ dvd_mul_of_dvd_left hqyz _))
    -- q cannot divide y (else q | z via y+z, contradicting gcd(y,z)=1)
    have hq_ndvd_y : ¬ q ∣ y := by
      intro hqy
      have hqz : q ∣ z := by
        have := dvd_sub hqyz hqy; rwa [show y + z - y = z from by ring] at this
      obtain ⟨u, v, huv⟩ := hcop_yz
      exact hq_prime.not_unit (isUnit_of_dvd_one
        (huv ▸ dvd_add (dvd_mul_of_dvd_right hqy u) (dvd_mul_of_dvd_right hqz v)))
    -- q | S and (y+z) | (S - p·y^{p-1})  ⟹  q | p·y^{p-1}  ⟹  q | p
    have hq_dvd_py : q ∣ ↑p * y ^ (p - 1) := by
      have hdiff : (y + z) ∣ (S y z p - ↑p * y ^ (p - 1)) := sum_dvd_sgSum_sub_scalar hodd
      have hq_dvd_diff : q ∣ (S y z p - ↑p * y ^ (p - 1)) := dvd_trans hqyz hdiff
      have h := dvd_sub hqS hq_dvd_diff
      rwa [show S y z p - (S y z p - ↑p * y ^ (p - 1)) = ↑p * y ^ (p - 1) from by ring] at h
    have hq_dvd_p : q ∣ (↑p : ℤ) := (hq_prime.dvd_or_dvd hq_dvd_py).resolve_right
      (fun h => hq_ndvd_y (hq_prime.dvd_of_dvd_pow h))
    -- q ~ p (both prime), so p | x — contradiction
    have hp_int : Prime (↑p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simp [hprime])
    exact hx_mod (dvd_trans (hq_prime.associated_of_dvd hp_int hq_dvd_p).symm.dvd hq_dvd_x)
  -- Extract p-th power structure from each coprime factor.
  obtain ⟨a, ha_or⟩ := eq_pow_or_neg_of_coprime_mul_pow hcop_factors hprod
  obtain ⟨α, hα_or⟩ := eq_pow_or_neg_of_coprime_mul_pow hcop_factors.symm
    (show S y z p * (y + z) = (-x) ^ p by linarith)
  -- Absorb the sign using oddness of p.
  have ha : ∃ a', y + z = a' ^ p := by
    rcases ha_or with h | h
    · exact ⟨a, h⟩
    · exact ⟨-a, by show y + z = (-a) ^ p; rw [Odd.neg_pow hodd]; linarith⟩
  have hα : ∃ α', S y z p = α' ^ p := by
    rcases hα_or with h | h
    · exact ⟨α, h⟩
    · exact ⟨-α, by show S y z p = (-α) ^ p; rw [Odd.neg_pow hodd]; linarith⟩
  obtain ⟨a', ha'⟩ := ha; obtain ⟨α', hα'⟩ := hα
  exact ⟨a', α', ha', hα'⟩

/-! ============================================================================
    PART V: MAIN THEOREM
    ============================================================================

  **Sophie Germain's Theorem (Case I of FLT for Sophie Germain primes):**

  If p is a Sophie Germain prime, then x^p + y^p = z^p has no solutions
  with p ∤ x, p ∤ y, p ∤ z.

  **Proof strategy:**
  1. Normalize: divide out gcd to get a coprime triple.
  2. By `q_dvd_of_fermat_triple`, q = 2p+1 divides some variable; WLOG q | x.
  3. Apply `sophie_germain_factorization` to each cyclic rearrangement,
     obtaining y+z = a^p, x+z = b^p, x+y = c^p (and the S-factors).
  4. Since q | x, we get b^p ≡ -z and c^p ≡ y (mod q).
  5. The sum S(y,-z,p) ≡ p · y^{p-1} ≡ p (mod q), since y^{p-1} ≡ 1.
  6. But S(y,-z,p) = α^p ≡ -1, 0, or 1 (mod q) — none equal p mod q.  □ -/

theorem sophie_germain_theorem {p : ℕ} (hSG : SophieGermainPrime p) :
    ∀ x y z : ℤ, x ^ p + y ^ p = z ^ p →
      ¬ ((↑p : ℤ) ∣ x) → ¬ ((↑p : ℤ) ∣ y) → ¬ ((↑p : ℤ) ∣ z) → False := by
  intro x y z hfermat hx hy hz
  set q : ℕ := 2 * p + 1 with hq_def
  have hq_prime := hSG.prime_twop_succ
  have hodd_p := hSG.odd
  have hprime_p := hSG.prime
  have hq_cast : (↑q : ℤ) = 2 * (↑p : ℤ) + 1 := by omega
  -- ── Core argument, assuming coprime triple with q | x ──
  suffices h_core : ∀ x y z : ℤ,
      x ^ p + y ^ p = z ^ p →
      ¬ ((↑p : ℤ) ∣ x) → ¬ ((↑p : ℤ) ∣ y) → ¬ ((↑p : ℤ) ∣ z) →
      IsCoprime x y → IsCoprime y z → IsCoprime x z →
      (↑q : ℤ) ∣ x → False by
    -- ── Reduction to coprime case ──
    -- Divide out d = gcd(gcd(x,y), z) so the quotient triple is setwise coprime.
    have hz_ne : z ≠ 0 := fun h => hz (h ▸ dvd_zero _)
    set d : ℕ := Int.gcd (↑(Int.gcd x y)) z
    have hd_pos : (0 : ℤ) < ↑d := by
      rw [Nat.cast_pos, Nat.pos_iff_ne_zero]
      intro heq; exact hz_ne (Int.gcd_eq_zero_iff.mp heq).2
    have hd_ne : (↑d : ℤ) ≠ 0 := ne_of_gt hd_pos
    set x₁ := x / (↑d : ℤ); set y₁ := y / (↑d : ℤ); set z₁ := z / (↑d : ℤ)
    have hd_dvd_x : (↑d : ℤ) ∣ x := dvd_trans (int_gcd_dvd_left _ _) (int_gcd_dvd_left _ _)
    have hd_dvd_y : (↑d : ℤ) ∣ y := dvd_trans (int_gcd_dvd_left _ _) (int_gcd_dvd_right _ _)
    have hd_dvd_z : (↑d : ℤ) ∣ z := int_gcd_dvd_right _ _
    -- The quotient triple still satisfies the Fermat equation (cancel d^p).
    have hf₁ : x₁ ^ p + y₁ ^ p = z₁ ^ p := by
      have hdn_ne : (↑d : ℤ) ^ p ≠ 0 := pow_ne_zero p hd_ne
      have key : x₁ ^ p * (↑d : ℤ) ^ p + y₁ ^ p * (↑d : ℤ) ^ p =
                 z₁ ^ p * (↑d : ℤ) ^ p := by
        simp only [← mul_pow]
        change (x / ↑d * ↑d) ^ p + (y / ↑d * ↑d) ^ p = (z / ↑d * ↑d) ^ p
        rw [Int.ediv_mul_cancel hd_dvd_x, Int.ediv_mul_cancel hd_dvd_y,
            Int.ediv_mul_cancel hd_dvd_z]; exact hfermat
      exact mul_right_cancel₀ hdn_ne (by ring_nf; linarith)
    -- p-indivisibility lifts to the quotient.
    have hx₁ : ¬ ((↑p : ℤ) ∣ x₁) := by
      intro h; apply hx; have := dvd_mul_of_dvd_left h (↑d : ℤ)
      rwa [show x₁ * (↑d : ℤ) = x from Int.ediv_mul_cancel hd_dvd_x] at this
    have hy₁ : ¬ ((↑p : ℤ) ∣ y₁) := by
      intro h; apply hy; have := dvd_mul_of_dvd_left h (↑d : ℤ)
      rwa [show y₁ * (↑d : ℤ) = y from Int.ediv_mul_cancel hd_dvd_y] at this
    have hz₁ : ¬ ((↑p : ℤ) ∣ z₁) := by
      intro h; apply hz; have := dvd_mul_of_dvd_left h (↑d : ℤ)
      rwa [show z₁ * (↑d : ℤ) = z from Int.ediv_mul_cancel hd_dvd_z] at this
    -- Setwise gcd = 1 ⟹ pairwise coprime.
    have hcop := Int.gcd_div_gcd_eq_one x y z hz_ne
    obtain ⟨hcop_xy, hcop_yz, hcop_xz⟩ :=
      pairwise_coprime_of_fermat_eq hprime_p hf₁ hcop
    -- q divides at least one of x₁, y₁, z₁.
    have q_dvd₁ : (↑q : ℤ) ∣ x₁ ∨ (↑q : ℤ) ∣ y₁ ∨ (↑q : ℤ) ∣ z₁ := by
      by_contra h_none; push_neg at h_none; obtain ⟨hqx₁, hqy₁, hqz₁⟩ := h_none
      exact hSG.q_dvd_of_fermat_triple hf₁ (hq_cast ▸ hqx₁) (hq_cast ▸ hqy₁) (hq_cast ▸ hqz₁)
    -- Permute so that q | x₁ and apply h_core.
    rcases q_dvd₁ with hq₁ | hq₁ | hq₁
    · exact h_core x₁ y₁ z₁ hf₁ hx₁ hy₁ hz₁ hcop_xy hcop_yz hcop_xz hq₁
    · exact h_core y₁ x₁ z₁ (by linarith) hy₁ hx₁ hz₁ hcop_xy.symm hcop_xz hcop_yz hq₁
    · have neg_pow := fun a : ℤ => Odd.neg_pow hodd_p a
      exact h_core (-z₁) x₁ (-y₁)
        (by rw [neg_pow z₁, neg_pow y₁]; linarith)
        (fun h => hz₁ (dvd_neg.mp h)) hx₁ (fun h => hy₁ (dvd_neg.mp h))
        (hcop_xz.symm.neg_left) (hcop_xy.neg_right)
        (hcop_yz.symm.neg_left.neg_right) (dvd_neg.mpr hq₁)
  -- ══════════════════════════════════════════════════════════════════════════
  -- Core: coprime triple (x,y,z) with x^p + y^p = z^p, q | x.
  -- ══════════════════════════════════════════════════════════════════════════
  intro x y z hfermat' hx' hy' hz' hcop_xy hcop_yz hcop_xz hq_dvd_x
  -- Rewrite as x^p + y^p + (-z)^p = 0 for the factorization lemma.
  have hfermat_sum : x ^ p + y ^ p + (-z) ^ p = 0 := by
    rw [Odd.neg_pow hodd_p]; linarith [hfermat']
  -- Apply factorization to three cyclic rearrangements:
  --   y + (-z) = a^p,   S(y,-z,p) = α^p
  --   x + (-z) = b^p
  --   (-z) + x = c^p    (i.e. x + y = c^p)
  have ⟨a, α, ha, hα⟩ := sophie_germain_factorization hodd_p hprime_p hfermat_sum hx'
    (IsCoprime.neg_right hcop_yz)
  have ⟨b, _, hb, _⟩ := sophie_germain_factorization hodd_p hprime_p
    (show y ^ p + x ^ p + (-z) ^ p = 0 by linarith [hfermat_sum])
    hy' (IsCoprime.neg_right hcop_xz)
  have ⟨c, _, hc, _⟩ := @sophie_germain_factorization p (-z) x y hodd_p hprime_p
    (show (-z) ^ p + x ^ p + y ^ p = 0 by linarith [hfermat_sum])
    (by rwa [dvd_neg]) hcop_xy
  -- q ∤ y and q ∤ z (coprimality with x, since q | x and q ≥ 2).
  have hq_ndvd_y : ¬ (↑q : ℤ) ∣ y := by
    intro hqy; have h_unit := hcop_xy.isUnit_of_dvd' hq_dvd_x hqy
    rw [Int.isUnit_iff] at h_unit
    have : (2 : ℤ) ≤ ↑q := by exact_mod_cast hq_prime.two_le
    rcases h_unit with h | h <;> linarith
  have hq_ndvd_z : ¬ (↑q : ℤ) ∣ z := by
    intro hqz; have h_unit := hcop_xz.isUnit_of_dvd' hq_dvd_x hqz
    rw [Int.isUnit_iff] at h_unit
    have : (2 : ℤ) ≤ ↑q := by exact_mod_cast hq_prime.two_le
    rcases h_unit with h | h <;> linarith
  -- Since q | x, the factorizations give: b^p ≡ -z,  c^p ≡ y  (mod q).
  have hbp : b ^ p ≡ -z [ZMOD ↑q] := by
    rw [Int.modEq_iff_dvd]; show (↑q : ℤ) ∣ (-z - b ^ p)
    rw [show (-z : ℤ) - b ^ p = -x from by linarith [hb]]; exact dvd_neg.mpr hq_dvd_x
  have hcp : c ^ p ≡ y [ZMOD ↑q] := by
    rw [Int.modEq_iff_dvd]; show (↑q : ℤ) ∣ (y - c ^ p)
    rw [show y - c ^ p = -x from by linarith [hc]]; exact dvd_neg.mpr hq_dvd_x
  -- q ∤ b (else b^p ≡ 0 ⟹ q | z, contradiction) and similarly q ∤ c.
  have hq_ndvd_b : ¬ (↑q : ℤ) ∣ b := by
    intro hqb
    apply hq_ndvd_z
    have h1 : b ^ p ≡ 0 [ZMOD ↑q] :=
      (Int.modEq_zero_iff_dvd).mpr (dvd_pow hqb hprime_p.ne_zero)
    have h2 := hbp.symm.trans h1
    rwa [Int.modEq_zero_iff_dvd, dvd_neg] at h2
  have hq_ndvd_c : ¬ (↑q : ℤ) ∣ c := by
    intro hqc
    apply hq_ndvd_y
    have h1 : c ^ p ≡ 0 [ZMOD ↑q] :=
      (Int.modEq_zero_iff_dvd).mpr (dvd_pow hqc hprime_p.ne_zero)
    exact (Int.modEq_zero_iff_dvd).mp (hcp.symm.trans h1)
  -- So b^p, c^p ≡ ±1 (mod q).
  have cong_b := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hq_ndvd_b)
  have cong_c := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hq_ndvd_c)
  -- b^p + c^p - a^p = 2x ≡ 0 (mod q), so q | a.
  have hbca_mod : b ^ p + c ^ p - a ^ p ≡ 0 [ZMOD ↑q] := by
    rw [show b ^ p + c ^ p - a ^ p = 2 * x from by linarith [ha, hb, hc],
        Int.modEq_iff_dvd, zero_sub]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hq_dvd_x 2)
  have hq_dvd_a : (↑q : ℤ) ∣ a := by
    by_contra hq_ndvd_a
    have cong_a := hSG.pow_congr_one_or_neg_one (hq_cast ▸ hq_ndvd_a)
    have hbca_mod' : b ^ p + c ^ p - a ^ p ≡ 0 [ZMOD (2 * (↑p : ℤ) + 1)] := by rwa [← hq_cast]
    have hp_int : (3 : ℤ) ≤ ↑p := by exact_mod_cast hSG.ge_three
    have h2p1_pos : (0 : ℤ) ≤ 2 * ↑p + 1 := by linarith
    -- All eight sign combos for (±1) + (±1) - (±1) have absolute value ≤ 3 < q.
    rcases cong_b with hbv | hbv <;> rcases cong_c with hcv | hcv <;>
    rcases cong_a with hav | hav <;> (
      have h_zero := ((hbv.add hcv).sub hav).symm.trans hbca_mod'
      rw [Int.modEq_iff_dvd] at h_zero; obtain ⟨k, hk⟩ := h_zero
      have hkz : k = 0 := by
        by_contra hk_ne
        rcases (show k ≥ 1 ∨ k ≤ -1 from by omega) with hpos | hneg
        · have := le_mul_of_one_le_right h2p1_pos hpos; linarith
        · have := mul_le_mul_of_nonneg_left hneg h2p1_pos; linarith
      simp only [hkz, mul_zero] at hk; omega)
  -- q | a  ⟹  y ≡ z (mod q)  (since y - z = a^p).
  have hyz_cong : y ≡ z [ZMOD ↑q] := by
    rw [Int.modEq_iff_dvd, show z - y = -(a ^ p) from by linarith [ha]]
    exact dvd_neg.mpr (dvd_pow hq_dvd_a hprime_p.ne_zero)
  -- α^p = S(y,-z,p) ≡ p · y^{p-1} ≡ p · 1 = p  (mod q).
  -- The congruence y^{p-1} ≡ 1 holds because c^p ≡ ±1 forces y ≡ ±1,
  -- and (±1)^{p-1} = 1 since p-1 is even.
  have halpha_cong : α ^ p ≡ (↑p : ℤ) [ZMOD ↑q] := by
    have hS_cong : S y (-z) p ≡ ↑p * y ^ (p - 1) [ZMOD ↑q] :=
      sgSum_congr_mod hprime_p.ne_zero (Int.ModEq.neg hyz_cong.symm)
    have hy_pow : y ^ (p - 1) ≡ 1 [ZMOD ↑q] := by
      have hy_cong : y ≡ 1 [ZMOD ↑q] ∨ y ≡ -1 [ZMOD ↑q] := by
        rcases cong_c with h | h <;> [left; right] <;>
          (rw [← hq_cast] at h; exact hcp.symm.trans h)
      rcases hy_cong with h | h
      · have := h.pow (p - 1); rwa [one_pow] at this
      · have heven : Even (p - 1) := by obtain ⟨k, hk⟩ := hodd_p; exact ⟨k, by omega⟩
        have := h.pow (p - 1); rwa [Even.neg_one_pow heven] at this
    rw [← hα]; calc S y (-z) p
        ≡ ↑p * y ^ (p - 1) [ZMOD ↑q] := hS_cong
      _ ≡ ↑p * 1 [ZMOD ↑q] := Int.ModEq.mul_left _ hy_pow
      _ = ↑p := by ring
  -- But α^p ∈ {-1, 0, 1} mod q, and none of these equal p mod q.  Contradiction!
  have halpha_range :
      α ^ p ≡ -1 [ZMOD ↑q] ∨ α ^ p ≡ 0 [ZMOD ↑q] ∨ α ^ p ≡ 1 [ZMOD ↑q] := by
    by_cases hq_dvd_alpha : (↑q : ℤ) ∣ α
    · right; left; exact (Int.modEq_zero_iff_dvd).mpr (dvd_pow hq_dvd_alpha hprime_p.ne_zero)
    · rcases hSG.pow_congr_one_or_neg_one (hq_cast ▸ hq_dvd_alpha) with h | h
      · right; right; rw [hq_cast]; exact h
      · left; rw [hq_cast]; exact h
  rcases halpha_range with h | h | h
  · exact hSG.p_not_congr_neg_one (by rw [← hq_cast]; exact (halpha_cong.symm.trans h).symm)
  · exact hSG.p_not_congr_zero (by rw [← hq_cast]; exact (halpha_cong.symm.trans h).symm)
  · exact hSG.p_not_congr_one (by rw [← hq_cast]; exact (halpha_cong.symm.trans h).symm)

end
