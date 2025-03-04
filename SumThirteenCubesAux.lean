import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Util.Qq

open Nat

def sum_of_powers (i k : ℕ) : Set ℕ := {n | ∃ l : List ℕ, l.length = k ∧ (l.map (· ^ i)).sum = n}

lemma sum_of_powers_mono_right {i : ℕ} (hi : i ≠ 0) : Monotone (sum_of_powers i) := by
  apply monotone_nat_of_le_succ
  rintro k n ⟨l, rfl, rfl⟩
  exact ⟨0 :: l, by simpa⟩

lemma mem_sum_of_powers {i k n : ℕ} :
    n ∈ sum_of_powers i k ↔ ∃ l : List ℕ, l.length = k ∧ (l.map (· ^ i)).sum = n :=
  Iff.rfl

lemma mem_sum_of_powers_multiset {i k n : ℕ} :
    n ∈ sum_of_powers i k ↔ ∃ l : Multiset ℕ, l.card = k ∧ (l.map (· ^ i)).sum = n := by
  rw [mem_sum_of_powers]
  constructor
  · rintro ⟨l, hlk, rfl⟩
    exact ⟨l, hlk, by simp⟩
  · rintro ⟨l, hlk, rfl⟩
    induction l using Quotient.inductionOn
    exact ⟨_, hlk, by simp⟩

lemma pow_mem_sum_of_powers : n ^ i ∈ sum_of_powers i 1 := ⟨[n], rfl, by simp⟩

@[simp] lemma zero_mem_sum_of_powers (hi : i ≠ 0) : 0 ∈ sum_of_powers i k :=
  ⟨List.replicate k 0, by simp [hi]⟩

@[simp] lemma sum_of_powers_zero_right : sum_of_powers i 0 = {0} := by simp [sum_of_powers]

@[simp] lemma sum_of_powers_zero_left : sum_of_powers 0 k = {k} := by
  simpa [sum_of_powers, Set.eq_singleton_iff_unique_mem] using Exists.intro (List.range k) (by simp)

lemma mem_sum_of_powers_zero_left_iff {n k : ℕ} : n ∈ sum_of_powers 0 k ↔ n = k := by simp

lemma add_mem_sum_of_powers {i kn km n m : ℕ}
    (hn : n ∈ sum_of_powers i kn) (hm : m ∈ sum_of_powers i km) :
    n + m ∈ sum_of_powers i (kn + km) := by
  obtain ⟨l, hlk, rfl⟩ := hn
  obtain ⟨l', hlk', rfl⟩ := hm
  exact ⟨l ++ l', by simp [hlk, hlk']⟩

open Pointwise in
lemma sum_of_powers_add_sum_of_powers_subset {i k₁ k₂ : ℕ} :
    sum_of_powers i k₁ + sum_of_powers i k₂ ⊆ sum_of_powers i (k₁ + k₂) := by
  intro n
  simp only [Set.mem_add, forall_exists_index, and_imp]
  rintro n hn m hm rfl
  exact add_mem_sum_of_powers hn hm

section unbounded_range

def ϕ (z : ℕ) : ℕ := 11 * z ^ 9 + (z ^ 3 + 1) ^ 3 + (5 * z) ^ 3
def ψ (z : ℕ) : ℕ := 14 * z ^ 9
lemma ϕ_eq (z : ℕ) : ϕ z = 12 * z ^ 9 + 3 * z ^ 6 + 128 * z ^ 3 + 1 := by rw [ϕ]; ring_nf

lemma ϕ_add_six_le_ψ_aux (t : ℝ) (hz : 379 ≤ t) :
    12 * t ^ 9 + 3 * t ^ 6 + 128 * t ^ 3 + (1 : ℝ) < 14 * (t - 6) ^ 9 := by
  have ht₀ : 0 < t := by linarith
  have h₁ : -2 ≤ - (6 / t) := by rw [←neg_div, le_div_iff₀ ht₀]; linarith
  have h₂ : 12 * t ^ 9 + 2 * t ^ 8 * (t - (378 : ℝ)) ≤ 14 * (t - 6) ^ 9 := by
    have h₃ := one_add_mul_le_pow h₁ 9
    rw [←sub_eq_add_neg, one_sub_div ht₀.ne', div_pow, le_div_iff₀, ←sub_nonneg] at h₃
    swap
    · positivity
    rw [←sub_nonneg]
    refine (mul_nonneg h₃ (by norm_num1 : (0 : ℝ) ≤ 14)).trans_eq ?_
    field_simp [ht₀.ne']
    ring_nf
  refine h₂.trans_lt' ?_
  rw [add_assoc, add_assoc, add_lt_add_iff_left, ←add_assoc]
  have h₃ : 3 * t ^ 6 ≤ 3 * t ^ 8 / (379 : ℝ) ^ 2 := by
    rw [le_div_iff₀, (by norm_num : 8 = 6 + 2), pow_add, ←mul_assoc]
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz _) (by positivity)
    · positivity
  have h₄ : 128 * t ^ 3 ≤ 128 * t ^ 8 / (379 : ℝ) ^ 5 := by
    rw [le_div_iff₀, (by norm_num : 8 = 3 + 5), pow_add, ←mul_assoc]
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz _) (by positivity)
    · positivity
  have h₅ : (1 : ℝ) ≤ t ^ 8 / 379 ^ 8 := by -- why do i need the ascription here :(
    rw [one_le_div]
    · exact pow_le_pow_left₀ (by positivity) hz _
    · positivity
  have h₆ : 2 * t ^ 8 ≤ 2 * t ^ 8 * (t - 378) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  refine (add_le_add_three h₃ h₄ h₅).trans_lt (h₆.trans_lt' ?_)
  ring_nf
  exact mul_lt_mul_of_pos_left (by norm_num) (by positivity)

lemma ϕ_add_six_le_ψ {z : ℕ} (hz : 373 ≤ z) : ϕ (z + 6) < ψ z := by
  rw [ϕ_eq, ←Nat.cast_lt (α := ℝ)]
  push_cast
  refine (ϕ_add_six_le_ψ_aux (z + 6) ?_).trans_eq ?_
  · norm_cast
    linarith only [hz]
  simp only [add_sub_cancel, ψ]
  simp -- norm_cast used to work

def I (z : ℕ) : Finset ℕ := Finset.Icc (ϕ z) (ψ z)

lemma self_le_ψ (z : ℕ) : z < ψ (z + 1) :=
  lt_mul_of_one_le_of_lt (by norm_num) ((Nat.le_self_pow (by norm_num1) _).trans_lt' (by simp))

lemma ψ_increasing : StrictMono ψ := fun x y h =>
  mul_lt_mul_of_pos_left (by gcongr) (by norm_num1)

lemma in_some_I (n : ℕ) (hn : 14 * 379 ^ 9 ≤ n) : ∃ z, z % 6 = 1 ∧ n ∈ I z := by
  have hn' : ψ 379 ≤ n := hn
  have ex : ∃ z, z % 6 = 1 ∧ n ≤ ψ (z + 6) := by
    use n / 6 * 6 + 1
    rw [Nat.add_mod, Nat.mul_mod_left]
    simp only [true_and]
    refine (self_le_ψ _).le.trans ?_
    rw [ψ, ψ]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by simp) ?_ _) (by norm_num1)
    rw [add_le_add_iff_right]
    exact (Nat.lt_div_mul_add (by norm_num : 0 < 6)).le.trans (add_le_add_left (by norm_num) _)
  let z := Nat.find ex
  have ⟨(hz₁ : z % 6 = 1), (hz₂ : n ≤ ψ (z + 6))⟩ := Nat.find_spec ex
  have hz : 373 ≤ z := by
    rw [←add_le_add_iff_right 6, ←ψ_increasing.le_iff_le]
    exact hz₂.trans' hn'
  have h₆z : 6 ≤ z := by linarith
  have hn'' : ψ z < n := by
    have : z - 6 < z := Nat.sub_lt (by linarith) (by norm_num)
    have := Nat.find_min ex this
    rw [not_and, not_le, ←Nat.mod_eq_sub_mod h₆z, Nat.sub_add_cancel h₆z] at this
    exact this hz₁
  refine ⟨z + 6, (Nat.add_mod_right _ _).trans hz₁, ?_⟩
  rw [I, Finset.mem_Icc]
  exact ⟨((ϕ_add_six_le_ψ hz).trans hn'').le, hz₂⟩

lemma six_coprime_cube {z : ℕ} (hz : z % 6 = 1) : Nat.Coprime 6 (z ^ 3) := by
  have hz₂ : z % 2 = 1 := by
    have := congr_arg (· % 2) hz
    dsimp at this
    rw [Nat.mod_mod_of_dvd _ (by norm_num)] at this
    simpa using this
  have hz₃ : z % 3 = 1 := by
    have := congr_arg (· % 3) hz
    dsimp at this
    rw [Nat.mod_mod_of_dvd _ (by norm_num)] at this
    simpa using this
  rw [Nat.coprime_pow_right_iff three_pos, (by norm_num : 6 = 2 * 3), Nat.coprime_mul_iff_left,
    Nat.prime_two.coprime_iff_not_dvd, Nat.prime_three.coprime_iff_not_dvd,
    Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hz₂, hz₃]
  simp

def represent_partial_r_aux (n : ℕ) {z : ℕ} (hz : z % 6 = 1) :
    ∃ r, r < z ^ 3 ∧ n ≡ (6 * r) [MOD z ^ 3] := by
  have := six_coprime_cube hz
  have : NeZero (z ^ 3) := ⟨fun h => by simp [h] at this⟩
  refine ⟨_, ZMod.val_lt (((6 : ℕ) : ZMod (z ^ 3))⁻¹ * n : ZMod (z ^ 3)), ?_⟩
  rwa [←ZMod.eq_iff_modEq_nat, Nat.cast_mul, ZMod.natCast_zmod_val,
    ←mul_assoc, ZMod.coe_mul_inv_eq_one, one_mul]

def represent_partial_r (n : ℕ) {z : ℕ} (hz : z % 6 = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ z ^ 3 ∧ n ≡ (6 * r) [MOD z ^ 3] := by
  have ⟨r, hr, hr'⟩ := represent_partial_r_aux n hz
  cases' r with r
  · exact ⟨z ^ 3, hr, le_rfl, by simpa [Nat.ModEq] using hr'⟩
  exact ⟨r + 1, by simp, hr.le, hr'⟩

def represent_partial_s (n : ℕ) :
    ∃ s, s ≤ 5 ∧ n ≡ (s + 4) [MOD 6] := by
  refine ⟨(n - 4 : ZMod 6).val, Nat.le_of_lt_succ (ZMod.val_lt _), ?_⟩
  rw [←ZMod.eq_iff_modEq_nat, Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_ofNat,
    sub_add_cancel]

lemma cube_mod_6 {n : ℕ} : n ^ 3 % 6 = n % 6 := by
  rw [pow_mod]
  have : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 6 <;> norm_num

lemma N_plus_eight_mod_6 {r s z : ℕ} (hr : 1 ≤ r) (hr₂ : r ≤ z ^ 3)
  (hz : z % 6 = 1) :
    ((r + 1) ^ 3 + (r - 1) ^ 3 + (z ^ 3 - r) ^ 3 + (z ^ 3 - r) ^ 3 + (s * z) ^ 3 + 8) % 6
      = (s + 4) % 6 := by
  rw [add_mod, add_mod _ (_ ^ 3), cube_mod_6, add_mod _ (_ ^ 3), cube_mod_6, add_mod _ (_ ^ 3),
    cube_mod_6, add_mod (_ ^ 3), cube_mod_6, cube_mod_6, ←add_mod (r + 1), ←add_mod (r + 1 + _),
    ←add_mod _ (z ^ 3 - r), ←add_mod, add_assoc r, add_tsub_cancel_of_le hr, ←two_mul,
    add_assoc (2 * r), ←two_mul, ←mul_add, add_tsub_cancel_of_le hr₂, add_mod, mul_mod, cube_mod_6,
    ←mul_mod, ←add_mod (2 * z), ←add_mul, add_comm 2, mul_mod, hz, mul_one, mod_mod, ←add_mod,
    add_assoc, add_mod, add_mod s]
  norm_num

lemma N_mod_z_cubed_int {r s z : ℤ} :
    ((r + 1) ^ 3 + (r - 1) ^ 3 + (z ^ 3 - r) ^ 3 + (z ^ 3 - r) ^ 3 + (s * z) ^ 3) % (z ^ 3)
      = (6 * r) % (z ^ 3) := by
  have : (r + 1) ^ 3 + (r - 1) ^ 3 + (z ^ 3 - r) ^ 3 + (z ^ 3 - r) ^ 3 + (s * z) ^ 3 =
    6 * r + z ^ 3 * (6 * r ^ 2 + 2 * z ^ 6 - 6 * r * z ^ 3 + s ^ 3) := by ring
  rw [this]
  simp

lemma N_mod_z_cubed {r s z : ℕ} (hr : 1 ≤ r) (hr₂ : r ≤ z ^ 3) :
    ((r + 1) ^ 3 + (r - 1) ^ 3 + (z ^ 3 - r) ^ 3 + (z ^ 3 - r) ^ 3 + (s * z) ^ 3) % (z ^ 3)
      = (6 * r) % (z ^ 3) := by
  zify [hr, hr₂]
  exact N_mod_z_cubed_int

lemma represent_partial (n : ℕ) (hn : n ≠ 0) {z : ℕ} (hz : z % 6 = 1) (hnz : n ∈ I z) :
    ∃ (x₁ x₂ x₃ x₄ x₅ N m : ℕ),
      n = N + 8 * z ^ 9 + 6 * m * z ^ 3 ∧ 0 < m ∧ m < z ^ 6 ∧
      N = x₁ ^ 3 + x₂ ^ 3 + x₃ ^ 3 + x₄ ^ 3 + x₅ ^ 3 := by
  have ⟨r, hr₁, hr₂, hrn⟩ := represent_partial_r n hz
  have ⟨s, hs₁, hsn⟩ := represent_partial_s n
  rw [I, Finset.mem_Icc] at hnz
  let N := (r + 1) ^ 3 + (r - 1) ^ 3 + (z ^ 3 - r) ^ 3 + (z ^ 3 - r) ^ 3 + (s * z) ^ 3
  have : 0 < N := by positivity
  have hN₁ : N < ϕ z - 8 * z ^ 9 := by
    rw [ϕ, add_assoc, ←tsub_add_eq_add_tsub, ←tsub_mul, ←add_assoc]
    swap
    · exact mul_le_mul_right' (by norm_num1) (z ^ 9)
    refine add_lt_add_of_lt_of_le ?_ ?_
    swap
    · exact pow_le_pow_of_le_left (mul_le_mul_right' hs₁ z) 3
    rw [add_assoc, add_assoc, add_comm, ←two_mul]
    refine add_lt_add_of_lt_of_le ?_ ?_
    swap
    · exact pow_le_pow_left₀ (by positivity) (add_le_add_right hr₂ 1) 3
    have h₁ : (r - 1) ^ 3 < z ^ (3 * 3) := by
      rw [pow_mul]
      refine Nat.pow_lt_pow_left ?_ (by norm_num1)
      rwa [tsub_lt_iff_right hr₁, Nat.lt_add_one_iff]
    have h₂ : 2 * (z ^ 3 - r) ^ 3 ≤ 2 * z ^ (3 * 3) := by
      rw [pow_mul]
      exact mul_le_mul_left' (pow_le_pow_left₀ (by positivity) (sub_le _ _) 3) 2
    refine (add_lt_add_of_lt_of_le h₁ h₂).trans_eq ?_
    ring
  have hN₂ : N + 8 * z ^ 9 < n := by
    rw [←lt_tsub_iff_right]
    exact hN₁.trans_le (Nat.sub_le_sub_right hnz.1 _)
  have hN₃ : n - N < 14 * z ^ 9 := (Nat.sub_lt (by positivity) (by positivity)).trans_le hnz.2
  have hN₄ : (N + 8) % 6 = (s + 4) % 6 := N_plus_eight_mod_6 hr₁ hr₂ hz
  have h₉ : z ^ 9 = (z ^ 3) ^ 3 := by rw [←pow_mul]
  have : 6 * z ^ 3 ∣ n - (N + 8 * z ^ 9) := by
    refine (six_coprime_cube hz).mul_dvd_of_dvd_of_dvd ?_ ?_
    · rw [←modEq_iff_dvd', ModEq, hsn, ←hN₄, add_mod, mul_mod, pow_mod, hz, one_pow,
      ←mul_mod, ←add_mod, mul_one]
      exact hN₂.le
    rw [←modEq_iff_dvd', ModEq, hrn, h₉, add_mod, mul_mod, pow_mod, mod_self,
      zero_pow three_ne_zero, ←mul_mod, mul_zero, ←add_mod, add_zero, N_mod_z_cubed hr₁ hr₂]
    exact hN₂.le
  obtain ⟨m, hm⟩ := this
  refine ⟨_, _, _, _, _, N, m, ?_, ?_, ?_, rfl⟩
  · rw [mul_right_comm, ←hm, add_tsub_cancel_of_le hN₂.le]
  · rw [pos_iff_ne_zero]
    rintro rfl
    rw [mul_zero, Nat.sub_eq_zero_iff_le] at hm
    exact hN₂.not_le hm
  rw [←tsub_tsub] at hm
  by_contra! hm'
  have : 6 * z ^ 3 * z ^ 6 ≤ n - N - 8 * z ^ 9 := by
    rw [hm]
    gcongr
  have := this.trans_lt (tsub_lt_tsub_right_of_le (le_tsub_of_add_le_left hN₂.le) hN₃)
  rw [←tsub_mul] at this
  ring_nf at this
  simp at this

lemma sum_of_thirteen_cubes_large (n : ℕ) (hn : 14 * 379 ^ 9 ≤ n) :
  ∃ (a b c d e f g h i j k l m : ℕ),
    n = a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 + e ^ 3 + f ^ 3 + g ^ 3 + h ^ 3 + i ^ 3 + j ^ 3 + k ^ 3 +
      l ^ 3 + m ^ 3 := by
  have ⟨z, hz, hzn⟩ := in_some_I n hn
  obtain ⟨a, b, c, d, e, N, m, hn', hm₀, hmz, hN⟩ :=
    represent_partial n (by positivity) hz hzn
  obtain ⟨x₁, x₂, x₃, x₄, rfl⟩ := sum_four_squares m
  have hx₁ : x₁ < z ^ 3 := by
    rw [←(Nat.pow_left_strictMono two_ne_zero).lt_iff_lt, ←pow_mul]
    refine hmz.trans_le' (by nlinarith only)
  have hx₂ : x₂ < z ^ 3 := by
    rw [←(Nat.pow_left_strictMono two_ne_zero).lt_iff_lt, ←pow_mul]
    exact hmz.trans_le' (by nlinarith only)
  have hx₃ : x₃ < z ^ 3 := by
    rw [←(Nat.pow_left_strictMono two_ne_zero).lt_iff_lt, ←pow_mul]
    exact hmz.trans_le' (by nlinarith only)
  have hx₄ : x₄ < z ^ 3 := by
    rw [←(Nat.pow_left_strictMono two_ne_zero).lt_iff_lt, ←pow_mul]
    exact hmz.trans_le' (by nlinarith only)
  have : 8 * z ^ 9 + 6 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) * z ^ 3 =
    (z ^ 3 + x₁) ^ 3 + (z ^ 3 - x₁) ^ 3 +
    (z ^ 3 + x₂) ^ 3 + (z ^ 3 - x₂) ^ 3 +
    (z ^ 3 + x₃) ^ 3 + (z ^ 3 - x₃) ^ 3 +
    (z ^ 3 + x₄) ^ 3 + (z ^ 3 - x₄) ^ 3 := by
    zify [hx₁.le, hx₂.le, hx₃.le, hx₄.le]
    ring
  refine ⟨a, b, c, d, e, z ^ 3 + x₁, z ^ 3 - x₁, z ^ 3 + x₂, z ^ 3 - x₂, z ^ 3 + x₃, z ^ 3 - x₃,
    z ^ 3 + x₄, z ^ 3 - x₄, ?_⟩
  rw [hn', add_assoc, this, hN]
  ring

-- Note this shows `sum_of_powers 3 13` is in `Filter.atTop`
lemma sum_of_thirteen_cubes_set_large (n : ℕ) (hn : 14 * 379 ^ 9 ≤ n) :
    n ∈ sum_of_powers 3 13 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, rfl⟩ := sum_of_thirteen_cubes_large n hn
  refine ⟨[a, b, c, d, e, f, g, h, i, j, k, l, m], ?_⟩
  simp
  ring

end unbounded_range

section reduction

lemma difference_of_cubes {x y : ℝ} : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring

lemma sum_of_cubes_reduce (N : ℕ) : ∃ m k, m ^ 3 + k = N ∧ k ≤ 3 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  let m : ℕ := ⌊((N : ℝ) ^ (1 / 3 : ℝ) : ℝ)⌋₊
  have h₁ : (m : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
  have h₂ : m ^ 3 ≤ N := by
    rwa [←Nat.cast_le (α := ℝ), Nat.cast_pow, ←Real.rpow_natCast,
      ←Real.rpow_le_rpow_iff (by positivity) (Nat.cast_nonneg N) (by norm_num : (0 : ℝ) < 1 / 3),
      Nat.cast_ofNat, ←Real.rpow_mul (Nat.cast_nonneg m), mul_one_div, div_self three_ne_zero,
      Real.rpow_one]
  refine ⟨m, N - m ^ 3, add_tsub_cancel_of_le h₂, ?_⟩
  have h₃ : (N - m ^ 3 : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ) - m) *
    (((N : ℝ) ^ (1 / 3 : ℝ)) ^ 2 + (N : ℝ) ^ (1 / 3 : ℝ) * m + (m : ℝ) ^ 2) := by
    rw [←difference_of_cubes, ←Real.rpow_natCast (_ ^ _), ←Real.rpow_mul (Nat.cast_nonneg _),
    mul_comm, mul_one_div, Nat.cast_ofNat, div_self three_ne_zero, Real.rpow_one]
  have h₄ : (N : ℝ) ^ (1 / 3 : ℝ) - m < 1 := by
    rw [sub_lt_iff_lt_add']
    exact Nat.lt_floor_add_one _
  rw [Nat.cast_sub h₂, Nat.cast_pow, h₃]
  refine (mul_le_of_le_one_left (by positivity) h₄.le).trans ?_
  refine (add_le_add_three le_rfl (mul_le_mul_of_nonneg_left h₁ (by positivity))
    (pow_le_pow_left₀ (Nat.cast_nonneg _) h₁ _)).trans_eq ?_
  have h₅ : (N : ℝ) ^ (2 / 3 : ℝ) = ((N : ℝ) ^ (1 / 3 : ℝ) : ℝ) ^ 2 := by
    rw [←Real.rpow_two, ←Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [←sq, ←h₅]
  ring_nf

lemma sum_of_cubes_reduce_helper (n : ℕ) : ∃ m k, m ^ 3 + k = n ∧ k ^ 3 ≤ 3 ^ 3 * n ^ 2 := by
  obtain ⟨m, k, hn', hk⟩ := sum_of_cubes_reduce n
  refine ⟨m, k, hn', ?_⟩
  rw [←Nat.cast_le (α := ℝ), Nat.cast_pow]
  refine (pow_le_pow_left₀ (Nat.cast_nonneg _) hk _).trans_eq ?_
  rw [mul_pow, Nat.cast_mul, ←Real.rpow_natCast (_ ^ _ : ℝ), ←Real.rpow_mul (by positivity)]
  norm_num

lemma sum_of_cubes_reduce_helper' (big small : ℕ) (h : 3 ^ 3 * big ^ 2 ≤ small ^ 3)
    (n : ℕ) (hn : n ≤ big) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ small := by
  obtain ⟨m, k, hn', hk⟩ := sum_of_cubes_reduce_helper n
  refine ⟨m, k, hn', ?_⟩
  by_contra!
  have : small ^ 3 < 3 ^ 3 * big ^ 2 := by
    refine (Nat.pow_lt_pow_left this three_ne_zero).trans_le (hk.trans ?_)
    gcongr
  exact this.not_le h

lemma sum_of_cubes_clean (big small i : ℕ) (h : 3 ^ 3 * big ^ 2 ≤ small ^ 3)
    (h' : ∀ n ≤ small, n + t ∈ sum_of_powers 3 i) :
    ∀ n ≤ big, n + t ∈ sum_of_powers 3 (i + 1) := by
  intro n hn
  obtain ⟨m, k, hmkn, hkn⟩ := sum_of_cubes_reduce_helper n
  have hk : k ^ 3 ≤ small ^ 3 :=
    calc
      _ ≤ 3 ^ 3 * n ^ 2 := hkn
      _ ≤ 3 ^ 3 * big ^ 2 := by gcongr
      _ ≤ small ^ 3 := h
  replace hk : k ≤ small := by contrapose! hk; gcongr
  specialize h' k hk
  rw [← hmkn, add_assoc, add_comm]
  exact add_mem_sum_of_powers pow_mem_sum_of_powers h'

lemma reduce_1 (n : ℕ) (hn : n < 14 * 379 ^ 9) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 51646616093922930 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn.le

lemma reduce_2 (n : ℕ) (hn : n ≤ 51646616093922930) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 416053489788 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn

lemma reduce_3 (n : ℕ) (hn : n ≤ 416053489788) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 167194005 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn

lemma reduce_4 (n : ℕ) (hn : n ≤ 167194005) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 910476 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn

lemma reduce_5 (n : ℕ) (hn : n ≤ 910476) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 28182 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn

lemma reduce_6 (n : ℕ) (hn : n ≤ 28182) :
    ∃ m k, m ^ 3 + k = n ∧ k ≤ 2779 :=
  sum_of_cubes_reduce_helper' _ _ (by norm_num) n hn

lemma reduce_many (t : ℕ) (h : ∀ k ≤ 2779, k + t ∈ sum_of_powers 3 i) :
    ∀ n ≤ 14 * 379 ^ 9, n + t ∈ sum_of_powers 3 (i + 6) :=
  sum_of_cubes_clean _ 51646616093922930 _ (by norm_num) <|
    sum_of_cubes_clean _ 416053489788 _ (by norm_num) <|
      sum_of_cubes_clean _ 167194005 _ (by norm_num) <|
        sum_of_cubes_clean _ 910476 _ (by norm_num) <|
          sum_of_cubes_clean _ 28182 _ (by norm_num) <|
            sum_of_cubes_clean _ 2779 _ (by norm_num) h

end reduction

section compute

open List

/--
`find_rep n m k i` consists of all the decreasing lists of length `n` whose elements are `≤ k`
and whose sum of `i`th powers is exactly `m`
-/
def find_rep (pow : ℕ) :
    (allowed_nums : ℕ) → (remaining_tot : ℕ) → (lowest_used : ℕ) → List (List ℕ)
  | n, 0, _ => [List.replicate n 0]
  | 0, (_ + 1), _ => []
  | n + 1, m@(_ + 1), k => do
      let i ← (List.range' 1 k).reverse
      if (i ^ pow ≤ m) then (find_rep pow n (m - i ^ pow) i).map (i :: ·) else []

/--
`find_rep' n m k` determines whether there is a list of length `n` whose elements are `≤ k`
and whose sum of cubes is exactly `m`
-/
def find_rep' (pow : ℕ) : (allowed_nums : ℕ) → (remaining_tot : ℕ) → (lowest_used : ℕ) → Bool
| _, 0, _ => true
| 0, (_ + 1), _ => false
| n + 1, m@(_ + 1), k =>
    (List.range' 1 k).reverse.any fun i => i ^ pow ≤ m && find_rep' pow n (m - i ^ pow) i

lemma find_rep_not_isEmpty_iff (i : ℕ) : ∀ n m k, (find_rep i n m k).isEmpty = !find_rep' i n m k
| n, 0, x => by rw [find_rep, find_rep']; rfl
| 0, (_ + 1), _ => rfl
| n + 1, m + 1, k => by
    rw [find_rep, find_rep', bind_eq_flatMap, Bool.eq_iff_iff]
    simp only [List.isEmpty_iff, flatMap_eq_nil_iff, ite_eq_right_iff, map_eq_nil_iff,
      Bool.not_eq_true', ← Bool.not_eq_true, any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      not_exists, not_and]
    simp only [← List.isEmpty_iff, find_rep_not_isEmpty_iff i, Bool.not_eq_true', Bool.not_eq_true]

/-- This is a special case of `find_rep_iff` which makes it a bit easier to prove -/
private lemma find_rep_iff_zero_middle (i n k : ℕ) (l : List ℕ) (hi : i ≠ 0) :
    l ∈ find_rep i n 0 k ↔
      l.length = n ∧ (∀ x ∈ l, x ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ i)).sum = 0 := by
  rw [find_rep, List.mem_singleton]
  constructor
  · rintro rfl
    simp [hi]
  rintro ⟨h₁, -, -, h₂⟩
  simpa [eq_replicate_iff, h₁, sum_eq_zero_iff, hi] using h₂

/-- `find_rep` consists exactly of the lists it should -/
lemma find_rep_iff (n m k : ℕ) (l : List ℕ) (hi : i ≠ 0) :
    l ∈ find_rep i n m k ↔
      l.length = n ∧ (∀ x ∈ l, x ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ i)).sum = m := by
  induction' n with n ih generalizing m k l
  · cases' m with m
    · exact find_rep_iff_zero_middle _ _ _ _ hi
    simp only [find_rep, not_mem_nil, zero_eq, ge_iff_le, false_iff, not_and, length_eq_zero]
    rintro rfl
    simp
  cases' m with m
  · exact find_rep_iff_zero_middle _ _ _ _ hi
  rw [find_rep]
  simp only [bind_eq_flatMap, mem_flatMap, mem_reverse, mem_range'_1, add_comm 1,
    Nat.lt_add_one_iff]
  constructor
  · simp only [forall_exists_index, and_imp]
    rintro x - hxk hl
    cases' em' (x ^ i ≤ m + 1) with h' h'
    · simp [if_neg h'] at hl
    rw [if_pos h', mem_map] at hl
    obtain ⟨a, ha, rfl⟩ := hl
    rw [ih] at ha
    simp only [length_cons, ha, mem_cons, forall_eq_or_imp, ge_iff_le, pairwise_cons, and_true, map,
      List.sum_cons, true_and, hxk]
    simp
    exact ⟨fun i hi => (ha.2.1 _ hi).trans hxk, ha.2.1, add_tsub_cancel_of_le h'⟩
  cases' l with x l
  · simp
  simp only [length_cons, succ.injEq, mem_cons, forall_eq_or_imp, ge_iff_le, pairwise_cons, map,
    List.sum_cons, and_imp]
  intros h hxk _ hl₂ hl₃ hl₄
  refine ⟨x, ⟨?_, hxk⟩, ?_⟩
  · rw [Nat.add_one_le_iff, pos_iff_ne_zero]
    rintro rfl
    have : ∀ a ∈ l, a = 0 := by simpa using hl₂
    rw [List.eq_replicate_iff.2 ⟨rfl, this⟩] at hl₄
    rw [map_replicate, sum_replicate] at hl₄
    simp [hi] at hl₄
  have : x ^ i ≤ succ m := by rw [succ_eq_add_one, ←hl₄]; simp
  rw [if_pos this]
  simp only [mem_map, cons.injEq, true_and, exists_eq_right]
  refine (ih _ _ l).2 ⟨h, hl₂, hl₃, ?_⟩
  rw [eq_tsub_iff_add_eq_of_le this, add_comm, hl₄]

def find_all (i k n : ℕ) : List (List ℕ) := find_rep i k n (n.findGreatest (· ^ i ≤ n))

lemma find_all_nonempty_iff {i k n : ℕ} (hi : i ≠ 0) :
    find_all i k n ≠ [] ↔ n ∈ sum_of_powers i k := by
  rw [find_all, ← length_pos, length_pos_iff_exists_mem]
  simp only [find_rep_iff _ _ _ _ hi]
  constructor
  · rintro ⟨l, hl₁, -, -, hl₂⟩
    exact ⟨l, hl₁, hl₂⟩
  rintro ⟨l, hl₁, rfl⟩
  have hl := List.perm_insertionSort (· ≥ ·) l
  refine ⟨l.insertionSort (· ≥ ·), by simp only [length_insertionSort, hl₁], ?_,
    sorted_insertionSort _ _, by rw [(hl.map _).sum_eq]⟩
  intros x hx
  rw [hl.mem_iff] at hx
  have : x ^ i ∈ l.map (· ^ i) := by
    simp only [mem_map, _root_.zero_le]
    use x, hx
  have := List.single_le_sum (by simp) _ this
  exact Nat.le_findGreatest ((Nat.le_self_pow hi _).trans this) this

def find_all' (i k n : ℕ) : Bool := find_rep' i k n (n.findGreatest (· ^ i ≤ n))

lemma find_all'_iff {i k n : ℕ} (hi : i ≠ 0) :
    find_all' i k n = true ↔ n ∈ sum_of_powers i k := by
  rw [← find_all_nonempty_iff hi, ne_eq, ←List.isEmpty_iff, find_all, find_rep_not_isEmpty_iff,
    Bool.not_eq_true', Bool.not_eq_false, find_all']

lemma twenty_three_is_not_sum_of_eight_cubes' : 23 ∉ sum_of_powers 3 8 := by
  rw [← find_all'_iff (by norm_num), Bool.not_eq_true]
  rfl

-- use the kernel to prove no list exists
lemma two_hundred_thirty_nine_is_not_sum_of_eight_cubes : 239 ∉ sum_of_powers 3 8 := by
  rw [← find_all'_iff (by norm_num), Bool.not_eq_true]
  rfl

-- I used #eval to find the list then typed it in
lemma two_hundred_thirty_nine_is_sum_of_nine_cubes' : 239 ∈ sum_of_powers 3 9 :=
  ⟨[5, 3, 3, 3, 2, 2, 2, 2, 1], rfl, rfl⟩

section

open Lean Meta Elab Qq

def test_val (i n : ℕ) : Array (List ℕ) := Id.run do
  let mut tab := Array.mkEmpty (α := List ℕ) (n + 1)
  tab := tab.push []
  for j in [1:n+1] do
    let mut best := List.replicate j 1
    for t in [1:n+1] do
      if j < t ^ i then break
      else
        if t ^ i = j then best := [t]
          else
            let k := tab.getD (j - t ^ i) []
            if k.length + 1 < best.length then best := t :: k
    tab := tab.push best
  return tab

def myPowSum (i : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ^ i + myPowSum i xs

lemma myPowSum_eq (i : ℕ) (l : List ℕ) : myPowSum i l = (l.map (· ^ i)).sum := by
  induction l <;> aesop (add simp myPowSum)

lemma Tactic.mem_sum_of_powers_le (n i k : ℕ) (l : List ℕ)
    (h1 : Nat.ble l.length k = true) (h2 : myPowSum i l = n) (h3 : (i != 0) = true) :
    n ∈ sum_of_powers i k :=
  sum_of_powers_mono_right (by simpa using h3) (by simpa using h1)
    ⟨l, rfl, myPowSum_eq _ _ ▸ h2⟩

lemma Tactic.mem_sum_of_powers_base (i k : ℕ) (hi : (i != 0) = true) : 0 ∈ sum_of_powers i k := by
  apply zero_mem_sum_of_powers
  simpa using hi

lemma Tactic.mem_sum_of_powers_step (n' i k' n k x : ℕ)
    (hk : k' + 1 = k) (hn : n' + x ^ i = n) (hm : n' ∈ sum_of_powers i k') :
    n ∈ sum_of_powers i k := by
  substs k n
  exact add_mem_sum_of_powers hm pow_mem_sum_of_powers

lemma Tactic.sum_of_powers_zero_of_eq (n k : ℕ) (h : n = k) : n ∈ sum_of_powers 0 k := by
  simp [h]

def goalShape (l u i k : ℕ) : Prop := ∀ x, l ≤ x → x < u → x ∈ sum_of_powers i k

lemma Tactic.mem_sum_of_powers_many_lt (i k l u : ℕ) (h : Nat.ble u l = true) :
    goalShape l u i k :=
  fun _ hl hu ↦ ((hl.trans_lt hu).not_le (by simpa using h)).elim

lemma Tactic.mem_sum_of_powers_many_one {l : ℕ} (u i k : ℕ)
    (hl : l ∈ sum_of_powers i k)
    (hu : l + 1 = u) :
    goalShape l u i k := by
  intro j hli hui
  obtain rfl : j = l := by omega
  exact hl

lemma Tactic.mem_sum_of_powers_many_halve {l m u : ℕ} (i k : ℕ)
    (h_lo : goalShape l m i k)
    (h_hi : goalShape m u i k) :
    goalShape l u i k := by
  intro j hli hui
  obtain hm | hm := lt_or_le j m
  · exact h_lo j hli hm
  · exact h_hi j hm hui

lemma Tactic.end_sum_of_powers (h : goalShape l u 3 k) :
    ∀ x, l ≤ x → x < u → x ∈ sum_of_powers 3 k := h

/--
Given expressions `en, ek, ei` representing natural numbers `n, k, i` and a list `list : List ℕ`
whose sum of `i`th powers is `n` and of length at most `k`, produce a proof of
`n ∈ sum_of_powers i k`.
-/
def prove_sumOfPowers (n k i : ℕ) (en ek ei : Q(ℕ)) : List ℕ → MetaM Expr
  | [] => do
      let h ← mkEqRefl (mkConst `Bool.true)
      mkAppM `Tactic.mem_sum_of_powers_base #[ei, ek, h]
  | x :: xs => do
      let n' := n - x ^ i
      let k' := k - 1
      let en' := mkNatLit n'
      let ek' := mkNatLit k'
      let pf ← prove_sumOfPowers n' k' i en' ek' ei xs
      let hk ← mkEqRefl ek
      let hn ← mkEqRefl en
      mkAppM `Tactic.mem_sum_of_powers_step #[en', ei, ek', en, ek, mkNatLit x, hk, hn, pf]

def prove_sumOfPowers_many (l u k i : ℕ) (el eu ek ei : Expr)
    (arr : Array (List ℕ)) :
    MetaM Expr := do
  if l < u then
    if l + 1 = u then
      let list := arr.get! l
      if k < list.length
        then throwError "goal {l} ∈ sum_of_powers {i} {k} is false, best is {list.length}"
      let pf ← prove_sumOfPowers l k i el ek ei list
      mkAppM `Tactic.mem_sum_of_powers_many_one #[eu, ei, ek, pf, ← mkEqRefl eu]
    else
      let m := (l + u) / 2
      let em := mkNatLit m
      let pf_lo ← prove_sumOfPowers_many l m k i el em ek ei arr
      let pf_hi ← prove_sumOfPowers_many m u k i em eu ek ei arr
      mkAppM `Tactic.mem_sum_of_powers_many_halve #[ei, ek, pf_lo, pf_hi]
  else
    let h ← mkEqRefl (mkConst `Bool.true)
    mkAppM `Tactic.mem_sum_of_powers_many_lt #[ei, ek, el, eu, h]

def sum_of_powers_tac (g : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← g.getType
  match t with
  | ~q($en ∈ sum_of_powers $ei $ek) =>
      let some i := ei.nat? | throwError "{ei} not a natural literal"
      let some n := en.nat? | throwError "{en} not a natural literal"
      let some k := ek.nat? | throwError "{ek} not a natural literal"
      if i = 0 then
        if n = k then g.assign (← mkAppM `Tactic.sum_of_powers_zero_of_eq #[en, ek, ← mkEqRefl ek])
        else throwError "sum_of_powers goal is false; simp can prove it is false"
      else
        let list :: _ := find_all i k n | throwError "sum_of_powers goal is false"
        let list := list.takeWhile (· ≠ 0)
        g.assign (← prove_sumOfPowers n k i en ek ei list)
  | ~q(∀ x, $el ≤ x → x < $eu → x ∈ sum_of_powers $ei $ek) =>
      let some i := ei.nat? | throwError "{ei} not a natural literal"
      let some l := el.nat? | throwError "{el} not a natural literal"
      let some u := eu.nat? | throwError "{eu} not a natural literal"
      let some k := ek.nat? | throwError "{ek} not a natural literal"
      if i = 0 then throwError "tactic does not support zeroth powers"
      let arr := test_val i u
      let pf ← prove_sumOfPowers_many l u k i el eu ek ei arr
      let pf_final ← mkAppM `Tactic.end_sum_of_powers #[pf]
      g.assign pf_final
  | _ => throwError
         "the prove_sumOfPowers tactic only supports goals of the form\n\
          n ∈ sum_of_powers i k\n\
          or\n\
          ∀ x, l ≤ x → x < u → x ∈ sum_of_powers i k"

elab "prove_sumOfPowers" : tactic =>
  Elab.Tactic.liftMetaFinishingTactic sum_of_powers_tac

end

lemma mid_range : ∀ i : ℕ, 455 ≤ i → i < 3235 → i ∈ sum_of_powers 3 7 := by
  prove_sumOfPowers

end compute

lemma low_range : ∀ (i : ℕ), 0 ≤ i → i < 455 → i ∈ sum_of_powers 3 13 := by
  prove_sumOfPowers

theorem sum_thirteen_cubes (n : ℕ) : n ∈ sum_of_powers 3 13 := by
  cases' le_or_lt (14 * 379 ^ 9) n with h₁ h₁
  · exact sum_of_thirteen_cubes_set_large _ h₁
  cases' lt_or_le n 455 with h₂ h₂
  · exact low_range _ (by simp) h₂
  obtain ⟨N, hN⟩ := exists_add_of_le h₂
  rw [add_comm] at hN
  rw [hN]
  refine reduce_many 455 ?_ _ (by omega)
  intro k hk
  exact mid_range _ (by simp) (by omega)

#print axioms sum_thirteen_cubes
