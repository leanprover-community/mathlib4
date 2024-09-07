
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.RingTheory.Regular.RegularSequence

/- We prove a special case of Dickson's Conjecture as stated in
`On factoring of unlimited integers` by KAREL HRBACEK:
the case where:
* `gcd(a,b)>1` or `b=1`

n = gcd(a,b) > 1 implies n | f(k) = a+bk for all k,
violating the main hypothesis of Dickson's conjecture.

See `dickson_strong`.

Dickson's Conjecture is trivial for ℓ = 0
and we do not need Hrbacek's assumption that ℓ ≥ 1.
 -/

#eval Nat.gcd 0 5

open Finset
def prod_f {ℓ : ℕ} (a b : Fin ℓ → ℕ) : ℕ → ℕ :=
  λ k ↦ Finset.prod univ (λ i : Fin ℓ ↦ a i + b i * k)


theorem dickson_strong {ℓ : ℕ} (a b: Fin ℓ → ℕ)
  (ha : ∀ i, Nat.gcd (a i) (b i) > 1 ∨ b i = 1)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime := by
  by_cases h : ∀ i, b i = 1
  · rw [h i]
    simp
    obtain ⟨p,hp⟩ := Nat.exists_infinite_primes (a i + n₀)
    exists (p - a i)
    constructor
    · suffices a i + n₀ ≤ a i + (p - a i) by
        refine Nat.le_sub_of_add_le ?h
        linarith

      calc
      a i + n₀ ≤ p := hp.1
      _ ≤ _ := le_add_tsub
    have : a i + (p - a i) = p := by
      apply Nat.add_sub_of_le
      linarith
    rw [this]
    exact hp.2
  · simp at h
    obtain ⟨i,_⟩ := h
    exfalso
    apply hc
    simp
    exists Nat.gcd (a i) (b i)
    constructor
    · have := ha i
      tauto
    · intro k
      let h₀ := prod_dvd_prod_of_subset {i} univ
        (λ j : Fin ℓ ↦ a j + b j * k) (subset_univ {i})
      rw [prod_singleton] at h₀
      unfold prod_f
      have h₁ : b i ∣ b i * k := Nat.dvd_mul_right (b i) k
      have h₂: (a i).gcd (b i) ∣ a i := Nat.gcd_dvd_left (a i) (b i)
      have h₃: (a i).gcd (b i) ∣ b i := Nat.gcd_dvd_right (a i) (b i)
      have h₄: (a i).gcd (b i) ∣ a i + b i * k := by
        refine (Nat.dvd_add_iff_right h₂).mp ?_
        exact Nat.dvd_trans h₃ h₁
      exact Nat.dvd_trans h₄ h₀

theorem dickson_gcd {ℓ : ℕ} (a b: Fin ℓ → ℕ)
  (ha : ∀ i, Nat.gcd (a i) (b i) > 1)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime :=
  dickson_strong a b (fun i => .inl <| ha i) hc i n₀


lemma gcd_gt_of_dvd {a b : ℕ} (ha : b ∣ a) (h_b : b > 1):
  Nat.gcd a b > 1 := by
    have hb : b ≥ 1 := Nat.one_le_of_lt h_b
    unfold Nat.gcd
    by_cases Ha : a = 0
    · rw [if_pos Ha]
      tauto
    rw [if_neg Ha]
    obtain ⟨k,hk⟩ := ha
    have hbk: b ∣ b.gcd (b * k) := by
      refine Nat.dvd_gcd_iff.mpr ?_
      constructor
      · simp
      · exact Nat.dvd_mul_right b k
    rw [hk]
    simp
    by_cases Hab : a = b
    · rw [Hab] at hk
      have : k = 1 := (Nat.mul_right_eq_self_iff hb).mp (id (Eq.symm hk))
      subst this;simp;tauto
    · have hk₀: k ≠ 0 := fun hc => Ha  <| mul_zero b ▸ hc ▸ hk
      have hk₁: k ≠ 1 := fun hc => Hab <| mul_one  b ▸ hc ▸ hk
      have hk1: k > 1 := Nat.one_lt_iff_ne_zero_and_ne_one.mpr  ⟨hk₀, hk₁⟩
      have : b % (b * k) = b :=
        Nat.mod_eq_of_lt <| (Nat.lt_mul_iff_one_lt_right (hb)).mpr hk1
      rw [this]
      have g₀ : (b).gcd (b * k) ≠ 0 := by
        refine Nat.gcd_ne_zero_left ?_
        intro hc
        rw [hc] at hb
        simp only [ge_iff_le, nonpos_iff_eq_zero, one_ne_zero] at hb
      have g₁ : b.gcd (b * k) ≠ 1 := by
        intro hc
        have : b ∣ 1 :=
          (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod hc) (b.gcd (b * k))) hbk).mp hbk
        simp at this
        rw [this] at h_b
        simp only [gt_iff_lt,lt_self_iff_false] at h_b
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨g₀, g₁⟩


lemma gcd_gt_or_eq_one_of_dvd {a b : ℕ} (ha : b ∣ a) (hb : b ≥ 1):
  Nat.gcd a b > 1 ∨ b = 1 := by
    by_cases H : b = 1
    tauto
    left
    have hbi: b > 1 := Nat.lt_of_le_of_ne (hb) fun a ↦ H (id (Eq.symm a))
    exact gcd_gt_of_dvd ha hbi


lemma dickson_dvd {ℓ : ℕ} {a b: Fin ℓ → ℕ} (hb : ∀ i, b i ≥ 1)
  (ha : ∀ i, b i ∣ a i)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime :=
  dickson_strong a b (λ i ↦ gcd_gt_or_eq_one_of_dvd (ha i) (hb i)) hc i n₀

  theorem dickson_linear {ℓ : ℕ} {a b: Fin ℓ → ℕ} {hb : ∀ i, b i ≥ 1}
  (ha : ∀ i, a i = 0)
  (hc : ¬ (∃ n, n > 1 ∧ ∀ k, n ∣ (prod_f a b k))) (i : Fin ℓ) (n₀:ℕ) :
  ∃ n ≥ n₀, (a i + b i * n).Prime :=
    dickson_dvd hb (fun i => (ha i) ▸ Nat.dvd_zero (b i)) hc i n₀
