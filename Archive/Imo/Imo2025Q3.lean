import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.Basic

open Nat Int

/- Let $\mathbb{N}+$ denote the set of positive integers. A function $f: \mathbb{N}+ \rightarrow
\mathbb{N}+$ is said to be bonza if $f(a)$ divides $b^a-f(b)^{f(a)}$ for all positive integers $a$
and $b$. Determine the smallest real constant $c$ such that $f(n) \leq c n$ for all bonza functions
$f$ and all positive integers $n$.
-/

def bonza : Set (ℕ → ℕ) :=
  {f : ℕ → ℕ | (∀ a b : ℕ, 0 < a → 0 < b → (f a : ℤ) ∣ (b : ℤ) ^ a - (f b : ℤ) ^ (f a)) ∧
    ∀ n, 0 < n → f n > 0}

lemma hdvd : ∀ f ∈ bonza, ∀ n, n > 0 → f n ∣ n ^ n := by
  intro f hf n hn
  have dvd1 := hf.1 n n hn hn
  have : (f n : ℤ) ∣ (f n : ℤ) ^ f n := by
    refine Dvd.dvd.pow ?_ ?_
    exact Int.dvd_refl ↑(f n)
    have := hf.2 n hn
    exact Nat.ne_zero_of_lt this
  have : (f n : ℤ) ∣ (n : ℤ) ^ n := by
    exact (Int.dvd_iff_dvd_of_dvd_sub dvd1).mpr this
  rw [Eq.symm (Int.natCast_pow n n)] at this
  exact ofNat_dvd.mp this

theorem Int.ModEq.pow_card_eq_self' {p k : ℕ} (hp : Nat.Prime p) {n : ℤ} :
    n ^ (p ^ k) ≡ n [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases ch : (p : ℤ) ∣ n
  · calc
    _ ≡ 0 [ZMOD p] :=
      ModEq.symm (Dvd.dvd.zero_modEq_int (dvd_pow ch (Ne.symm (NeZero.ne' (p ^ k)))))
    _ ≡ _ [ZMOD p] := Dvd.dvd.zero_modEq_int ch
  · have : IsCoprime n p := by
      rw [ofNat_dvd_left, ← Nat.Prime.coprime_iff_not_dvd hp] at ch
      exact IsCoprime.symm ((fun {m n} ↦ isCoprime_iff_gcd_eq_one.mpr) ch)
    have : n ^ (p ^ k - 1) ≡ 1 [ZMOD p] := by
      refine ModEq.symm ((fun {n a b} ↦ modEq_iff_dvd.mpr) ?_)
      have dvd1 : (p : ℤ) ∣ n ^ (p - 1) - 1 := by
        refine modEq_iff_dvd.mp ?_
        exact ModEq.symm (pow_card_sub_one_eq_one hp this)
      have : p ^ 1 - 1 ∣ p ^ (1 * k) - 1 := by
        exact nat_pow_one_sub_dvd_pow_mul_sub_one p 1 k
      simp at this
      rcases this with ⟨m, hm⟩
      have dvd2 : n ^ (p - 1) - 1 ∣ n ^ (p ^ k - 1) - 1 := by
        rw [hm]
        exact pow_one_sub_dvd_pow_mul_sub_one n (p - 1) m
      exact Int.dvd_trans dvd1 dvd2
    have : n ^ (p ^ k - 1) * n ≡ 1 * n [ZMOD p] := by
      exact ModEq.mul this rfl
    have eq : p ^ k - 1 + 1 = p ^ k := by
      refine Nat.sub_add_cancel ?_
      exact NeZero.one_le
    rwa [← Int.pow_succ, eq, one_mul] at this

lemma imp : ∀ f ∈ bonza, ∀ p, Nat.Prime p → f p = 1 ∨
    (∀ b : ℕ, b > 0 → (p : ℤ) ∣ (b : ℤ) - ((f b) : ℤ)) := by
  intro f hf p hp
  have : f p ∣ p ^ p := by
    refine hdvd f hf p ?_
    exact Prime.pos hp
  obtain ⟨α , ha1, ha2⟩ : ∃ α, α ≤ p ∧ f p = p ^ α := by
    exact (Nat.dvd_prime_pow hp).mp this
  by_cases ch : α = 0
  · left
    rwa [ch, pow_zero] at ha2
  · right
    intro b hb
    have dvd1 : (p : ℤ) ∣ f p := by
      rw [ha2]
      refine natCast_dvd_natCast.mpr ?_
      exact dvd_pow_self p ch
    have dvd2 := hf.1 p b (by exact Prime.pos hp) hb
    have : (p : ℤ) ∣ (b : ℤ) ^ p - (f b) ^ f p := Int.dvd_trans dvd1 dvd2
    have : (b : ℤ) ≡ (f b : ℤ) [ZMOD p] := by
      calc
      _ ≡ (b : ℤ) ^ p [ZMOD p] := Int.ModEq.symm (ModEq.pow_card_eq_self hp)
      _ ≡ (f b) ^ f p [ZMOD p] := Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) this)
      _ ≡ _ [ZMOD p] := by
        rw [ha2]
        exact ModEq.pow_card_eq_self' hp
    exact Int.ModEq.dvd (id (Int.ModEq.symm this))

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
  have Oddb : Odd b :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hb)
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
          have := LTE (by omega) (Nat.two_dvd_ne_zero.mpr hb1) (by omega) (Nat.even_iff.mpr ch1)
          rwa [← LucasLehmer.Int.natCast_pow_pred b a hb]
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

theorem fforall : ∀ f : ℕ → ℕ, f ∈ bonza → ∀ n, 0 < n → f n ≤ 4 * n := by
  intro f hf n hn

  sorry

theorem my_favorite_theorem : IsLeast {c : ℝ | ∀ f : ℕ → ℕ, f ∈ bonza →
  ∀ n, 0 < n → f n ≤ c * n} 4 := by
  constructor
  · intro f hf
    sorry
  · intro c h
    have := h g exist 4 (by norm_num)
    have eq : padicValNat 2 4 =2 := by
      have : 4 = 2 ^ 2 := by norm_num
      rw [this, padicValNat.prime_pow]
    simp [g, eq] at this
    have : c ≥ 16 / 4 := (div_le_iff₀ (by norm_num)).mpr this
    norm_num at this
    exact this
