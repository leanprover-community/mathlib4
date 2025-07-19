import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Multiplicity

open Nat Int

/- Let $\mathbb{N}+$ denote the set of positive integers. A function $f: \mathbb{N}+ \rightarrow
\mathbb{N}+$ is said to be bonza if $f(a)$ divides $b^a-f(b)^{f(a)}$ for all positive integers $a$
and $b$. Determine the smallest real constant $c$ such that $f(n) \leq c n$ for all bonza functions
$f$ and all positive integers $n$.
-/

/-- Define bonza functions
-/
def bonza : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | (∀ a b : ℕ, 0 < a → 0 < b → (f a : ℤ) ∣ (b : ℤ) ^ a - (f b : ℤ) ^ (f a)) ∧
    ∀ n, 0 < n → f n > 0}

lemma hdvd {f : ℕ → ℕ} (hf : f ∈ bonza) {n : ℕ} (hn : n > 0) : f n ∣ n ^ n := by
  have : (f n : ℤ) ∣ (f n : ℤ) ^ f n :=
    Dvd.dvd.pow (Int.dvd_refl (f n)) (Nat.ne_zero_of_lt (hf.2 n hn))
  have : (f n : ℤ) ∣ (n : ℤ) ^ n := (Int.dvd_iff_dvd_of_dvd_sub (hf.1 n n hn hn)).mpr this
  rw [Eq.symm (Int.natCast_pow n n)] at this
  exact ofNat_dvd.mp this

lemma imp {f : ℕ → ℕ} (hf : f ∈ bonza) {p : ℕ} (hp : Nat.Prime p) :
    f p = 1 ∨ (∀ b : ℕ, b > 0 → (p : ℤ) ∣ (b : ℤ) - ((f b) : ℤ)) := by
  have : f p ∣ p ^ p := hdvd hf (Prime.pos hp)
  obtain ⟨α , ha1, ha2⟩ : ∃ α, α ≤ p ∧ f p = p ^ α := (Nat.dvd_prime_pow hp).mp this
  by_cases ch : α = 0
  · left
    rwa [ch, pow_zero] at ha2
  · right
    intro b hb
    have : (p : ℤ) ∣ (b : ℤ) ^ p - (f b) ^ f p := by calc
      _ ∣ (f p : ℤ) := by
        rw [ha2, natCast_dvd_natCast]
        exact dvd_pow_self p ch
      _ ∣ _ := hf.1 p b (Prime.pos hp) hb
    have : (b : ℤ) ≡ (f b : ℤ) [ZMOD p] := by calc
      _ ≡ (b : ℤ) ^ p [ZMOD p] := Int.ModEq.symm (ModEq.pow_card_eq_self hp)
      _ ≡ (f b) ^ f p [ZMOD p] := Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) this)
      _ ≡ _ [ZMOD p] := by
        rw [ha2]
        nth_rw 2 [← npow_one (f b)]
        exact Int.ModEq.pow_eq_pow hp (nat_sub_one_dvd_pow_sub_one p α)
          (one_le_pow α p (Prime.pos hp)) (by norm_num)
    exact Int.ModEq.dvd (id (Int.ModEq.symm this))

theorem cases {f : ℕ → ℕ} (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
    (∃ N, ∀ p > N, Nat.Prime p → f p = 1) := by
  obtain ⟨b, bgt, hb⟩ : ∃ b, b > 0 ∧ f b ≠ b := Set.not_subset.mp hnf
  have {p : ℕ} (hp : Nat.Prime p): f p = 1 ∨ (p : ℤ) ∣ (b : ℤ) - (f b : ℤ) :=
    Or.casesOn (imp hf hp) (fun ch ↦ Or.symm (Or.inr ch)) fun ch ↦ Or.inr (ch b bgt)
  use ((b : ℤ) - (f b : ℤ)).natAbs
  intro p pgt hp
  rcases this hp with ch | ch
  · exact ch
  · have : (p : ℤ).natAbs ≤ ((b : ℤ) - (f b : ℤ)).natAbs := by
      refine natAbs_le_of_dvd_ne_zero ch ?_
      refine sub_ne_zero_of_ne ?_
      simpa using id (Ne.symm hb)
    simp at this
    linarith

theorem Nat.exists_prime_gt_modEq_neg_one {k : ℕ} (n : ℕ) (hk0 : NeZero k) :
    ∃ (p : ℕ), Prime p ∧ n < p ∧ p ≡ -1 [ZMOD k] := by
  have : IsUnit (-1 : ZMod k) := by simp
  obtain ⟨p, hp⟩ :=  Nat.forall_exists_prime_gt_and_eq_mod this n
  use p
  constructor
  · exact hp.2.1
  constructor
  · exact hp.1
  · have := hp.2.2
    rw [eq_neg_iff_add_eq_zero, ← cast_add_one p, ZMod.natCast_eq_zero_iff] at this
    rw [← ZMod.intCast_eq_intCast_iff]
    refine Eq.symm ?_
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.sub_neg]
    exact ofNat_dvd_left.mpr this

theorem INF {f : ℕ → ℕ} (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
    ∀ p > 2, Nat.Prime p → f p = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ p > N, Nat.Prime p → f p = 1 := by
    have := cases hf
    tauto
  have tt {a p: ℕ} (ha : a > 0) (pp : Nat.Prime p) (hp : p > N) : (f a : ℤ) ∣ p ^ a - 1 := by
    have := hf.1 a p ha (by omega)
    rwa [hN p hp pp, Nat.cast_one, one_pow] at this
  intro q hq qp
  have dvd : f q ∣ q ^ q := by
    refine hdvd hf ?_
    exact zero_lt_of_lt hq
  obtain ⟨α , ha1, ha2⟩ : ∃ α, α ≤ q ∧ f q = q ^ α := (Nat.dvd_prime_pow qp).mp dvd
  by_cases ch : α = 0
  · simp [ch] at ha2
    exact ha2
  · have dvd1 : (q : ℤ) ∣ f q := by
      rw [ha2, Int.natCast_pow q α]
      exact dvd_pow_self (q : ℤ) ch
    have ttt {p : ℕ} (pp : Nat.Prime p) (hp : p > N) : p ≡ 1 [ZMOD q] := by calc
      _ ≡ p ^ q [ZMOD q] := Int.ModEq.symm (ModEq.pow_card_eq_self qp)
      _ ≡ _ [ZMOD q] :=
        have := tt (zero_lt_of_lt hq) pp hp
        Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) (Int.dvd_trans dvd1 this))
    obtain ⟨p, hp⟩ := Nat.exists_prime_gt_modEq_neg_one N (NeZero.of_gt hq)
    have : 1 ≡ -1 [ZMOD q] := by calc
      _ ≡ p [ZMOD q] := id (Int.ModEq.symm (ttt hp.1 hp.2.1))
      _ ≡ _ [ZMOD q] := hp.2.2
    have : (q : ℤ) ∣ 1 - (-1) := Int.ModEq.dvd (id (Int.ModEq.symm this))
    simp at this
    have : (q : ℤ).natAbs ≤ (2 : ℤ).natAbs := natAbs_le_of_dvd_ne_zero this (by norm_num)
    omega

lemma powp {f : ℕ → ℕ} (hf : f ∈ bonza) (hnf : ¬ ∀ x, x > 0 → f x = x) :
  ∀ n, n > 0 → ∃ a, f n = 2 ^ a := by
  intro n hn
  have : ∀ {p}, Nat.Prime p → p ∣ f n → p = 2 := by
    intro p pp pdvd
    by_contra nh
    have dvd : (p : ℤ) ∣ p ^ n - 1 := by calc
      _ ∣ (f n : ℤ) := ofNat_dvd.mpr pdvd
      _ ∣ _ := by
        have := hf.1 n p hn (Prime.pos pp)
        have lm : p > 2 := Nat.lt_of_le_of_ne (Prime.two_le pp) (fun a ↦ nh (id (Eq.symm a)))
        rwa [INF hf hnf p lm pp, Nat.cast_one, one_pow] at this
    have : (p : ℤ) ∣ p ^ n := dvd_pow (Int.dvd_refl p) (Nat.ne_zero_of_lt hn)
    have : (p : ℤ) ∣ 1 := (Int.dvd_iff_dvd_of_dvd_sub dvd).mp this
    have : p ∣ 1 := ofNat_dvd.mp this
    have : ¬ p ∣ 1 := Nat.Prime.not_dvd_one pp
    contradiction
  use (f n).primeFactorsList.length
  exact Nat.eq_prime_pow_of_unique_prime_dvd (Nat.ne_zero_of_lt (hf.2 n hn)) this

/-- asf
-/
def g : ℕ → ℕ := fun x ↦
  if ¬ 2 ∣ x then 1
  else if x = 2 then 4
  else 2 ^ (padicValNat 2 x + 2)

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
  have Oddb : Odd b := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hb)
  have : padicValNat 2 (b + 1) + padicValNat 2 (b - 1) ≥ 3 := by
    rw [← padicValNat.mul (by omega) (by omega)]
    have : (b + 1) * (b - 1) ≠ 0 := by simpa using by omega
    have dvd : 2 ^ 3 ∣ (b + 1) * (b - 1) := by
      simpa [← Nat.pow_two_sub_pow_two b 1] using Nat.eight_dvd_sq_sub_one_of_odd Oddb
    exact (padicValNat_dvd_iff_le (hp := fact_prime_two) this).mp dvd
  omega

lemma padicValNat_le {a : ℕ} (ha : a ≥ 4) (dvd : 2 ∣ a) : padicValNat 2 a + 2 ≤ a := by
  rcases dvd with ⟨k, hk⟩
  rw [hk, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  have : padicValNat 2 k < k := by calc
    _ ≤ Nat.log 2 k := padicValNat_le_nat_log k
    _ < _ := log_lt_self 2 (by omega)
  omega

lemma dvd_lemma (a b : ℕ) (x : ℤ) (hb : 2 ∣ b) (ha : a ≥ 4) (ha2 : 2 ∣ a) (hx : 2 ∣ x) :
    2 ^ (padicValNat 2 a + 2) ∣ (b : ℤ) ^ a - x ^ 2 ^ (padicValNat 2 a + 2) := by
  refine dvd_sub ?_ ?_
  · exact Int.dvd_trans (pow_dvd_pow 2 (padicValNat_le ha ha2))
      (pow_dvd_pow_of_dvd (ofNat_dvd_right.mpr hb) a)
  · have dvd1 : 2 ^ (padicValNat 2 a + 2) ∣ (2 : ℤ) ^ 2 ^ (padicValNat 2 a + 2) := by
      refine (padicValInt_dvd_iff (hp := fact_prime_two) (padicValNat 2 a + 2)
            (2 ^ 2 ^ (padicValNat 2 a + 2))).mpr ?_
      right
      simp [padicValInt]
      calc
      _ < 2 ^ (padicValNat 2 a + 1) := Nat.lt_two_pow_self
      _ ≤ _ := by
        rw [propext (Nat.pow_le_pow_iff_right le.refl)]
        omega
    exact Int.dvd_trans dvd1 (pow_dvd_pow_of_dvd hx (2 ^ (padicValNat 2 a + 2)))

lemma exist : g ∈ bonza := by
  constructor
  · intro a b ha hb
    by_cases ch1 : ¬ 2 ∣ a
    · simp [g, ch1]
    by_cases ch2 : a = 2
    · simp [g, ch2]
      split_ifs with hb1 hb2
      · exact dvd_self_sub_of_emod_eq
          (sq_mod_four_eq_one_of_odd (by simpa using Nat.odd_iff.mpr hb1))
      · simp [hb2]
      · refine dvd_sub ?_ ?_
        · have : 2 ∣ (b : ℤ) := ofNat_dvd_natCast.mpr (dvd_of_mod_eq_zero (mod_two_ne_one.mp hb1))
          have : 2 ^ 2 ∣ (b : ℤ) ^ 2 := pow_dvd_pow_of_dvd this 2
          simpa
        · refine Dvd.dvd.pow ?_ (by norm_num)
          use 2 ^ padicValNat 2 b
          ring
    · simp [g, ch1, ch2]
      have ha4 : a ≥ 4 := by omega
      have h2a : 2 ∣ a := by tauto
      split_ifs with hb1 hb2
      · by_cases lt : b = 1
        · simp [lt]
        simp at ch1
        have : (padicValNat 2 a + 2) ≤ padicValInt 2 (b ^ a - 1) := by
          rw [← LucasLehmer.Int.natCast_pow_pred b a hb]
          exact LTE (by omega) (Nat.two_dvd_ne_zero.mpr hb1) (by omega) (Nat.even_iff.mpr ch1)
        exact Int.dvd_trans (pow_dvd_pow 2 this) (padicValInt_dvd ((b : ℤ) ^ a - 1))
      · exact dvd_lemma a b 4 (by simp [hb2]) ha4 h2a (by norm_num)
      · exact dvd_lemma a b (2 ^ (padicValNat 2 b + 2)) (dvd_of_mod_eq_zero (mod_two_ne_one.mp hb1))
          ha4 h2a (Dvd.intro_left (Int.pow 2 (padicValNat 2 b + 1)) rfl)
  · intro n hn
    simp [g]
    split_ifs with h
    · norm_num
    · norm_num
    · exact Nat.two_pow_pos (padicValNat 2 n + 2)

theorem fforall {f : ℕ → ℕ} (hf : f ∈ bonza) {n : ℕ} (hn : 0 < n) : f n ≤ 4 * n := by
  by_cases hnf : ∀ x, x > 0 → f x = x
  · rw [hnf n hn]
    omega
  · rcases Nat.even_or_odd n with ch | ch
    · have : f n ∣ 3 ^ n - 1 := by
        have := hf.1 n 3 hn (by norm_num)
        have eq : f 3 = 1 := INF hf hnf 3 (by norm_num) (Nat.prime_three)
        simp [eq] at this
        have eq : (3 : ℤ) ^ n - 1 = (3 ^ n - 1 : ℕ) := by
          have : (3 : ℤ) ^ n = (3 ^ n : ℕ) := by simp
          rw [this]
          refine Eq.symm (natCast_pred_of_pos (pos_of_neZero (3 ^ n)))
        rw [eq] at this
        exact ofNat_dvd.mp this
      obtain ⟨a, ha⟩ := powp hf hnf n hn
      rw [ha] at this
      have le : a ≤ padicValNat 2 (3 ^ n - 1) := by
        refine (padicValNat_dvd_iff_le ?_).mp this
        have : 3 ^ n > 1 := one_lt_pow (by omega) (by norm_num)
        omega
      have := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num)
        (by norm_num) (n := n) (by omega) ch
      have eq : padicValNat 2 4 = 2 := by
        have : 4 = 2 ^ 2 := by norm_num
        rw [this, padicValNat.prime_pow]
      simp [eq] at this
      have : padicValNat 2 (3 ^ n - 1) = 2 + padicValNat 2 n := by omega
      calc
        _ ≤ 2 ^ padicValNat 2 (3 ^ n - 1) := by
          rw [ha]
          refine Nat.pow_le_pow_right (by norm_num) le
        _ = 2 ^ (2 + padicValNat 2 n) := congrArg (HPow.hPow 2) this
        _ = 4 * 2 ^ padicValNat 2 n := by rw [Nat.pow_add]
        _ ≤ _ := Nat.mul_le_mul_left 4 (Nat.le_of_dvd hn pow_padicValNat_dvd)
    · have dvd : f n ∣ n ^ n := hdvd hf hn
      have : Odd (n ^ n) := Odd.pow ch
      have Of : Odd (f n) := Odd.of_dvd_nat this dvd
      obtain ⟨t, ht⟩ : ∃ t, f n = 2 ^ t := powp hf hnf n hn
      rw [ht] at Of
      have : t = 0 := by
        by_contra! nh
        have : 2 ∣ 2 ^ t := dvd_pow_self 2 nh
        have : ¬ 2 ∣ 2 ^ t := Odd.not_two_dvd_nat Of
        contradiction
      simp [this] at ht
      rw [ht]
      omega

theorem my_favorite_theorem : IsLeast {c : ℝ | ∀ f : ℕ → ℕ, f ∈ bonza →
  ∀ n, 0 < n → f n ≤ c * n} 4 := by
  constructor
  · intro f hf n hn
    have : 4 * (n : ℝ) = (4 * n : ℕ) := by simp
    rw [this, Nat.cast_le]
    exact fforall hf hn
  · intro c h
    have := h g exist 4 (by norm_num)
    have eq : padicValNat 2 4 = 2 := by
      have : 4 = 2 ^ 2 := by norm_num
      rw [this, padicValNat.prime_pow]
    simp [g, eq] at this
    have : c ≥ 16 / 4 := (div_le_iff₀ (by norm_num)).mpr this
    norm_num at this
    exact this
