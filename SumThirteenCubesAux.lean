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

@[simp] lemma sum_of_powers_zero_right : sum_of_powers i 0 = {0} := by simp [sum_of_powers]

@[simp] lemma sum_of_powers_zero_left : sum_of_powers 0 k = {k} := by
  simpa [sum_of_powers, Set.eq_singleton_iff_unique_mem] using Exists.intro (List.range k) (by simp)

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
    (h' : ∀ n ≤ small, n ∈ sum_of_powers 3 i) :
    ∀ n ≤ big, n ∈ sum_of_powers 3 (i + 1) := by
  intro n hn
  obtain ⟨m, k, hmkn, hkn⟩ := sum_of_cubes_reduce_helper n
  have hk : k ^ 3 ≤ small ^ 3 :=
    calc
      _ ≤ 3 ^ 3 * n ^ 2 := hkn
      _ ≤ 3 ^ 3 * big ^ 2 := by gcongr
      _ ≤ small ^ 3 := h
  replace hk : k ≤ small := by contrapose! hk; gcongr
  specialize h' k hk
  rw [← hmkn, add_comm]
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

lemma reduce_6' (h : ∀ k ≤ 2779, k ∈ sum_of_powers 3 i) :
    ∀ n ≤ 28182, n ∈ sum_of_powers 3 (i + 1) :=
  sum_of_cubes_clean _ _ _ (by norm_num) h

lemma reduce_many (h : ∀ k ≤ 2779, k ∈ sum_of_powers 3 i) :
    ∀ n ≤ 14 * 379 ^ 9, n ∈ sum_of_powers 3 (i + 6) :=
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
`find_rep n m k` consists of all the decreasing lists of length `n` whose elements are `≤ k`
and whose sum of cubes is exactly `m`
-/
def find_rep : (allowed_nums : ℕ) → (remaining_tot : ℕ) → (lowest_used : ℕ) → List (List ℕ)
  | n, 0, _ => [List.replicate n 0]
  | 0, (_ + 1), _ => []
  | n + 1, m@(_ + 1), k => do
      let i ← (List.range' 1 k).reverse
      if (i ^ 3 ≤ m) then (find_rep n (m - i ^ 3) i).map (i :: ·) else []

/--
`find_rep' n m k` determines whether there is a list of length `n` whose elements are `≤ k`
and whose sum of cubes is exactly `m`
-/
def find_rep' : (allowed_nums : ℕ) → (remaining_tot : ℕ) → (lowest_used : ℕ) → Bool
| _, 0, _ => true
| 0, (_ + 1), _ => false
| n + 1, m@(_ + 1), k =>
    (List.range' 1 k).reverse.any fun i => i ^ 3 ≤ m && find_rep' n (m - i ^ 3) i

lemma find_rep_not_isEmpty_iff : ∀ n m k, (find_rep n m k).isEmpty = !find_rep' n m k
| n, 0, x => by rw [find_rep, find_rep']; rfl
| 0, (_ + 1), _ => rfl
| n + 1, m + 1, k => by
    rw [find_rep, find_rep', bind_eq_flatMap, Bool.eq_iff_iff]
    simp only [List.isEmpty_iff, flatMap_eq_nil_iff, ite_eq_right_iff, map_eq_nil_iff,
      Bool.not_eq_true', ← Bool.not_eq_true, any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      not_exists, not_and]
    simp only [← List.isEmpty_iff, find_rep_not_isEmpty_iff n, Bool.not_eq_true', Bool.not_eq_true]

/-- This is a special case of `find_rep_iff` which makes it a bit easier to prove -/
private lemma find_rep_iff_zero_middle (n k : ℕ) (l : List ℕ) :
    l ∈ find_rep n 0 k ↔
      l.length = n ∧ (∀ i ∈ l, i ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ 3)).sum = 0 := by
  rw [find_rep, List.mem_singleton]
  constructor
  · rintro rfl
    simp
  rintro ⟨h₁, -, -, h₂⟩
  simpa [eq_replicate_iff, h₁, sum_eq_zero_iff] using h₂

/-- `find_rep` consists exactly of the lists it should -/
lemma find_rep_iff (n m k : ℕ) (l : List ℕ) :
    l ∈ find_rep n m k ↔
      l.length = n ∧ (∀ i ∈ l, i ≤ k) ∧ l.Pairwise (· ≥ ·) ∧ (l.map (· ^ 3)).sum = m := by
  induction' n with n ih generalizing m k l
  · cases' m with m
    · exact find_rep_iff_zero_middle _ _ _
    simp only [find_rep, not_mem_nil, zero_eq, ge_iff_le, false_iff, not_and, length_eq_zero]
    rintro rfl
    simp
  cases' m with m
  · exact find_rep_iff_zero_middle _ _ _
  rw [find_rep]
  simp only [bind_eq_flatMap, mem_flatMap, mem_reverse, mem_range'_1, add_comm 1,
    Nat.lt_add_one_iff]
  -- simp?

  -- simp only [succ_eq_add_one, mem_ite_nil_right, mem_map, ge_iff_le]
  -- simp?
  constructor
  · simp only [forall_exists_index, and_imp]
    rintro x - hxk hl
    cases' em' (x ^ 3 ≤ m + 1) with h' h'
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
    simp at hl₄
  have : x ^ 3 ≤ succ m := by rw [succ_eq_add_one, ←hl₄]; simp
  rw [if_pos this]
  simp only [mem_map, cons.injEq, true_and, exists_eq_right]
  refine (ih _ _ l).2 ⟨h, hl₂, hl₃, ?_⟩
  rw [eq_tsub_iff_add_eq_of_le this, add_comm, hl₄]

def find_all (k n : ℕ) : List (List ℕ) := find_rep k n (n.findGreatest (· ^ 3 ≤ n))

lemma find_all_nonempty_iff (k n : ℕ) :
  find_all k n ≠ [] ↔ n ∈ sum_of_powers 3 k := by
  rw [find_all, ←length_pos, length_pos_iff_exists_mem]
  simp only [find_rep_iff]
  constructor
  · rintro ⟨l, hl₁, -, -, hl₂⟩
    exact ⟨l, hl₁, hl₂⟩
  rintro ⟨l, hl₁, rfl⟩
  have hl := List.perm_insertionSort (· ≥ ·) l
  refine ⟨l.insertionSort (· ≥ ·), by simp only [length_insertionSort, hl₁], ?_,
    sorted_insertionSort _ _, by rw [(hl.map _).sum_eq]⟩
  intros i hi
  rw [hl.mem_iff] at hi
  have : i ^ 3 ∈ l.map (· ^ 3) := by simp [hi]
  have := List.single_le_sum (by simp) _ this
  exact Nat.le_findGreatest ((Nat.le_self_pow (by norm_num) _).trans this) this

def find_all' (k n : ℕ) : Bool := find_rep' k n (n.findGreatest (· ^ 3 ≤ n))

lemma find_all'_iff (k n : ℕ) :
  find_all' k n = true ↔ n ∈ sum_of_powers 3 k := by
  rw [←find_all_nonempty_iff, ne_eq, ←List.isEmpty_iff, find_all, find_rep_not_isEmpty_iff,
    Bool.not_eq_true', Bool.not_eq_false, find_all']

lemma twenty_three_is_not_sum_of_eight_cubes' : 23 ∉ sum_of_powers 3 8 := by
  rw [←find_all'_iff, Bool.not_eq_true]
  rfl

lemma headD_eq_or_mem {α : Type _} {a : α} :
  ∀ l : List α, l.headD a = a ∨ l.headD a ∈ l
| [] => by simp
| (x :: xs) => by simp

-- use the kernel to prove no list exists
lemma two_hundred_thirty_nine_is_not_sum_of_eight_cubes : 239 ∉ sum_of_powers 3 8 := by
  rw [← find_all'_iff, Bool.not_eq_true]
  rfl

-- i used #eval to find the list then typed it in
lemma two_hundred_thirty_nine_is_sum_of_nine_cubes' : 239 ∈ sum_of_powers 3 9 :=
  ⟨[5, 3, 3, 3, 2, 2, 2, 2, 1], rfl, rfl⟩

section

open Lean Meta Elab Qq

def test_val (n : ℕ) : Array (List ℕ) := Id.run do
  let mut tab := Array.mkEmpty (α := List ℕ) (n + 1)
  tab := tab.push []
  for i in [1:n+1] do
    let mut best := List.replicate i 1
    for t in [1:n+1] do
      if i < t ^ 3 then break
      else
        if t ^ 3 = i then best := [t]
          else
            let k := tab.getD (i - t ^ 3) []
            if k.length + 1 < best.length then best := t :: k
    tab := tab.push best
  return tab

lemma Tactic.mem_sum_of_powers (n i k : ℕ) (l : List ℕ)
    (h1 : l.length = k) (h2 : (l.map (· ^ i)).sum = n) : n ∈ sum_of_powers i k :=
  ⟨l, h1, h2⟩

lemma Tactic.mem_sum_of_powers_table (n i k : ℕ) (l : List ℕ) (hi : i ≠ 0)
    (h1 : l.length ≤ k) (h2 : (l.map (· ^ i)).sum = n) : n ∈ sum_of_powers i k :=
  sum_of_powers_mono_right hi h1 ⟨l, rfl, h2⟩

/-- Given `n, k : ℕ`, return a proof of `n ∈ sum_of_powers 3 k`. -/
def prove_sumOfPowers (n k : ℕ) : MetaM Expr := do
  let l :: _ := find_rep k n (n.findGreatest (· ^ 3 ≤ n)) | throwError "no list found"
  let h1 ← mkEqRefl (toExpr k)
  let h2 ← mkEqRefl (toExpr n)
  let pf ← mkAppOptM `Tactic.mem_sum_of_powers #[toExpr n, mkNatLit 3, none, toExpr l, h1, h2]
  pure pf

def sum_of_powers_tac (g : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← g.getType
  match t with
  | ~q($en ∈ sum_of_powers 3 $ek) =>
      let some n := en.nat? | throwError "{en} not a natural literal"
      let some k := ek.nat? | throwError "{ek} not a natural literal"
      let pf ← prove_sumOfPowers n k
      g.assign pf
  | _ => throwError "goal is not a sum_of_powers"

elab "prove_sumOfPowers" : tactic =>
  Elab.Tactic.liftMetaFinishingTactic sum_of_powers_tac

lemma two_hundred_thirty_nine_is_sum_of_nine_cubes : 239 ∈ sum_of_powers 3 9 := by
  prove_sumOfPowers

lemma Tactic.mem_sum_of_powers_many_lt (k : ℕ) (h : ¬ l < u) :
    ∀ i, l ≤ i → i < u → i ∈ sum_of_powers 3 k := fun _ hl hu ↦ (h (hl.trans_lt hu)).elim

lemma Tactic.mem_sum_of_powers_many_step {l u : ℕ} (k : ℕ)
    (h_this : l ∈ sum_of_powers 3 k)
    (h_next : ∀ i, l + 1 ≤ i → i < u → i ∈ sum_of_powers 3 k) :
    ∀ i, l ≤ i → i < u → i ∈ sum_of_powers 3 k := by
  intro i hli hui
  obtain rfl | lt := Nat.eq_or_lt_of_le hli
  · exact h_this
  · exact h_next i lt hui

lemma Tactic.mem_sum_of_powers_many_one {l : ℕ} (k : ℕ)
    (h_this : l ∈ sum_of_powers 3 k) :
    ∀ i, l ≤ i → i < l + 1 → i ∈ sum_of_powers 3 k := by
  intro i hli hui
  obtain rfl : i = l := by omega
  assumption

lemma Tactic.mem_sum_of_powers_many_halve {l m u : ℕ} (k : ℕ)
    (h_lo : ∀ i, l ≤ i → i < m → i ∈ sum_of_powers 3 k)
    (h_hi : ∀ i, m ≤ i → i < u → i ∈ sum_of_powers 3 k) :
    ∀ i, l ≤ i → i < u → i ∈ sum_of_powers 3 k := by
  intro i hli hui
  obtain hm | hm := lt_or_le i m
  · exact h_lo i hli hm
  · exact h_hi i hm hui

/-- Given `l, u, k : ℕ`, return a proof of `∀ i, l ≤ i → i < u → i ∈ sum_of_powers 3 k`. -/
def prove_sumOfPowers_many (l u k : ℕ) (el eu ek : Expr) (t : Q(Prop)) : MetaM Expr := do
  if l < u
    then
      let pf_this ← prove_sumOfPowers l k
      let pf_next ← prove_sumOfPowers_many (l + 1) u k (mkNatLit (l + 1)) eu ek t
      let pf ← mkAppM `Tactic.mem_sum_of_powers_many_step #[ek, pf_this, pf_next]
      return pf
    else
      let lt ← mkLt el eu
      let h ← mkDecideProof (mkNot lt)
      let pf ← mkAppM `Tactic.mem_sum_of_powers_many_lt #[ek, h]
      return pf

def prove_sumOfPowers_many_half (l u k : ℕ) (el eu ek : Expr) (t : Q(Prop)) : MetaM Expr := do
  if l < u then
    if l + 1 = u
      then
        let pf_this ← prove_sumOfPowers l k
        let pf ← mkAppM `Tactic.mem_sum_of_powers_many_one #[ek, pf_this]
        return pf
      else
        let m := (l + u) / 2
        let em := mkNatLit m
        let pf_lo ← prove_sumOfPowers_many_half l m k el em ek t
        let pf_hi ← prove_sumOfPowers_many_half m u k em eu ek t
        let pf ← mkAppM `Tactic.mem_sum_of_powers_many_halve #[ek, pf_lo, pf_hi]
        return pf
  else
    let lt ← mkLt el eu
    let h ← mkDecideProof (mkNot lt)
    let pf ← mkAppM `Tactic.mem_sum_of_powers_many_lt #[ek, h]
    return pf

-- lemma Tactic.mem_sum_of_powers_table (n i k : ℕ) (l : List ℕ) (hi : i ≠ 0)
--     (h1 : l.length ≤ k) (h2 : (l.map (· ^ i)).sum = n) : n ∈ sum_of_powers i k :=
--   sum_of_powers_mono_right hi h1 ⟨l, rfl, h2⟩

#check OfNat.ofNat

/-- Given `l, u, k : ℕ`, return a proof of `∀ i, l ≤ i → i < u → i ∈ sum_of_powers 3 k`. -/
def prove_sumOfPowers_many_table (l u k : ℕ) (el eu ek : Expr) (t : Q(Prop))
    (arr : Array (List ℕ)) : MetaM Expr := do
  if l < u
    then
      let lst := arr.get! l
      let elst := toExpr lst
      let hk ← mkDecideProof (mkNot (← mkEq (mkNatLit 3) (mkNatLit 0)))
      let hlength ← mkDecideProof (← mkLe (← mkAppM `List.length #[elst]) ek)
      let h2 ← mkEqRefl el
      let pf_this ←
        mkAppM `Tactic.mem_sum_of_powers_table #[el, mkNatLit 3, ek, elst, hk, hlength, h2]
      let pf_next ← prove_sumOfPowers_many (l + 1) u k (mkNatLit (l + 1)) eu ek t
      let pf ← mkAppM `Tactic.mem_sum_of_powers_many_step #[ek, pf_this, pf_next]
      return pf
    else
      let lt ← mkLt el eu
      let h ← mkDecideProof (mkNot lt)
      let pf ← mkAppM `Tactic.mem_sum_of_powers_many_lt #[ek, h]
      return pf

def prove_sumOfPowers_many_half_table (l u k : ℕ) (el eu ek : Expr) (t : Q(Prop))
    (arr : Array (List ℕ)) :
    MetaM Expr := do
  if l < u then
    if l + 1 = u
      then
        let lst := arr.get! l
        let elst := toExpr lst
        let hk ← mkDecideProof (mkNot (← mkEq (mkNatLit 3) (mkNatLit 0)))
        let hlength ← mkDecideProof (← mkLe (← mkAppM `List.length #[elst]) ek)
        trace[debug] "{elst}"
        let h2 ← mkEqRefl el
        let pf_one ←
          mkAppM `Tactic.mem_sum_of_powers_table #[el, mkNatLit 3, ek, elst, hk, hlength, h2]
        let pf ← mkAppM `Tactic.mem_sum_of_powers_many_one #[ek, pf_one]
        return pf
      else
        let m := (l + u) / 2
        let em := mkNatLit m
        let pf_lo ← prove_sumOfPowers_many_half_table l m k el em ek t arr
        let pf_hi ← prove_sumOfPowers_many_half_table m u k em eu ek t arr
        let pf ← mkAppM `Tactic.mem_sum_of_powers_many_halve #[ek, pf_lo, pf_hi]
        return pf
  else
    let lt ← mkLt el eu
    let h ← mkDecideProof (mkNot lt)
    let pf ← mkAppM `Tactic.mem_sum_of_powers_many_lt #[ek, h]
    return pf

-- def sum_of_powers_many_tac (g : MVarId) : MetaM Unit := do
--   let t : Q(Prop) ← g.getType
--   match t with
--   | ~q(∀ i, $el ≤ i → i < $eu → i ∈ sum_of_powers 3 $ek) =>
--       let some l := el.nat? | throwError "{el} not a natural literal"
--       let some u := eu.nat? | throwError "{eu} not a natural literal"
--       let some k := ek.nat? | throwError "{ek} not a natural literal"
--       -- let pf : Q($t) := q(sorry)
--       let pf ← prove_sumOfPowers_many l u k el eu ek t
--       g.assign pf
--   | _ => throwError "goal is not a sum_of_powers"

-- def sum_of_powers_many_tac_half (g : MVarId) : MetaM Unit := do
--   let t : Q(Prop) ← g.getType
--   match t with
--   | ~q(∀ i, $el ≤ i → i < $eu → i ∈ sum_of_powers 3 $ek) =>
--       trace[debug] "{el} {eu} {ek}"
--       let some l := el.nat? | throwError "{el} not a natural literal"
--       let some u := eu.nat? | throwError "{eu} not a natural literal"
--       let some k := ek.nat? | throwError "{ek} not a natural literal"
--       let pf ← prove_sumOfPowers_many_half l u k el eu ek t
--       g.assign pf
--       -- let pf : Q($t) := q(sorry)
--       -- g.assign pf
--   | _ => throwError "goal is not a sum_of_powers"

def sum_of_powers_many_tac_half_table (g : MVarId) : MetaM Unit := do
  let t : Q(Prop) ← g.getType
  match t with
  | ~q(∀ i, $el ≤ i → i < $eu → i ∈ sum_of_powers 3 $ek) =>
      trace[debug] "{el} {eu} {ek}"
      let some l := el.nat? | throwError "{el} not a natural literal"
      let some u := eu.nat? | throwError "{eu} not a natural literal"
      let some k := ek.nat? | throwError "{ek} not a natural literal"
      let arr := test_val u
      let pf ← prove_sumOfPowers_many_half_table l u k el eu ek t arr
      g.assign pf
      -- let pf : Q($t) := q(sorry)
      -- g.assign pf
  | _ => throwError "goal is not a sum_of_powers"

-- elab "prove_sumOfPowers_many" : tactic =>
--   Elab.Tactic.liftMetaFinishingTactic sum_of_powers_many_tac

-- elab "prove_sumOfPowers_many_half" : tactic =>
--   Elab.Tactic.liftMetaFinishingTactic sum_of_powers_many_tac_half

elab "prove_sumOfPowers_many_half_table" : tactic =>
  Elab.Tactic.liftMetaFinishingTactic sum_of_powers_many_tac_half_table

-- set_option trace.debug true in
-- lemma test : ∀ n, 2 ≤ n → n < 3000 → n ∈ sum_of_powers 3 9 := by
--   prove_sumOfPowers_many

-- lemma test : ∀ n, 24 ≤ n → n < 25 → n ∈ sum_of_powers 3 8 := by
--   prove_sumOfPowers_many_half

-- set_option trace.debug true in
-- set_option trace.profiler true in
-- lemma test' : ∀ n, 455 ≤ n → n < 1000 → n ∈ sum_of_powers 3 7 := by
--   prove_sumOfPowers_many

-- set_option trace.debug true in
-- set_option trace.profiler true in
-- lemma test'' : ∀ n, 455 ≤ n → n < 2000 → n ∈ sum_of_powers 3 7 := by
--   prove_sumOfPowers_many_half

set_option trace.debug true in
set_option trace.profiler true in
lemma test''' : ∀ n, 455 ≤ n → n < 3234 → n ∈ sum_of_powers 3 7 := by
  prove_sumOfPowers_many_half_table

#print test'''

set_option trace.profiler true in
#eval test_val 3000

-- set_option trace.debug true in
-- set_option trace.profiler true in
-- lemma test' : ∀ n, 455 ≤ n → n < 800 → n ∈ sum_of_powers 3 7 := by
--   prove_sumOfPowers_many

-- #print test

end
-- use the kernel to check a list exists
lemma first_range (i : ℕ) (hi : i ≤ 23) : i ∈ sum_of_powers 3 9 := by
  rw [←find_all'_iff]; interval_cases i <;> rfl

-- use the kernel to compute the list then check it works
lemma second_range (i : ℕ) (hi : 23 < i) (hi' : i < 239) :
    i ∈ sum_of_powers 3 8 := by
  interval_cases i <;> prove_sumOfPowers

-- use the vm to check a list exists
lemma third_range : ∀ i : ℕ, i < 455 → 240 ≤ i → find_all' 8 i = true := by native_decide

lemma third_range' : ∀ i : ℕ, i < 455 → 240 ≤ i → i ∈ sum_of_powers 3 8 := by
  intro i hi hi'
  interval_cases i
  all_goals prove_sumOfPowers

-- use the vm to check a list exists
set_option trace.profiler true in
lemma fourth_range : ∀ i : ℕ, i ≤ 3234 → 455 ≤ i → find_all' 7 i = true := by native_decide

#exit

end compute

theorem sum_thirteen_cubes (n : ℕ) : n ∈ sum_of_powers 3 13 := by
  cases' le_or_lt (14 * 379 ^ 9) n with h₁ h₁
  · exact sum_of_thirteen_cubes_set_large _ h₁
  cases' lt_or_le n 455 with h₂ h₂
  · cases' lt_or_le n 240 with h₃ h₃
    · cases' le_or_lt n 23 with h₄ h₄
      · exact sum_of_powers_mono_right (by norm_num1) (by norm_num1) (first_range _ h₄)
      · rw [Nat.lt_succ_iff_lt_or_eq] at h₃
        rcases h₃ with h₃ | rfl
        · exact sum_of_powers_mono_right (by norm_num1) (by norm_num1) (second_range _ h₄ h₃)
        exact sum_of_powers_mono_right (by norm_num1) (by norm_num1)
          two_hundred_thirty_nine_is_sum_of_nine_cubes
    · refine sum_of_powers_mono_right (by norm_num1) (by norm_num1 : 8 ≤ 13) ?_
      rw [←find_all'_iff]
      exact third_range _ h₂ h₃
  obtain ⟨N, hN⟩ := exists_add_of_le h₂
  rw [add_comm] at hN
  subst hN
  have : N < 14 * 379 ^ 9 := h₁.trans_le' (by simp)
  obtain ⟨m₁, k₁, rfl, hk₁⟩ := reduce_1 _ this
  obtain ⟨m₂, k₂, rfl, hk₂⟩ := reduce_2 _ hk₁
  obtain ⟨m₃, k₃, rfl, hk₃⟩ := reduce_3 _ hk₂
  obtain ⟨m₄, k₄, rfl, hk₄⟩ := reduce_4 _ hk₃
  obtain ⟨m₅, k₅, rfl, hk₅⟩ := reduce_5 _ hk₄
  obtain ⟨m₆, k₆, rfl, hk₆⟩ := reduce_6 _ hk₅
  simp only [add_assoc]
  have := fourth_range (k₆ + 455) (by linarith only [hk₆]) (by simp)
  rw [find_all'_iff] at this
  obtain ⟨l, hl₁, hl₂⟩ := this
  refine ⟨m₁ :: m₂ :: m₃ :: m₄ :: m₅ :: m₆ :: l, by simp [hl₁], ?_⟩
  simp [hl₂]

#print axioms sum_thirteen_cubes
