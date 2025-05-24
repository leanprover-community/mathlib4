import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Qify


variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [Archimedean M]

noncomputable
def Archimedean.kfloor {one : M} (hone: 0 < one) (k : ℕ) (a : M) :=
  (existsUnique_zsmul_near_of_pos hone ((2 ^ k) • a)).choose

def Archimedean.kfloor_left {one : M} (hone: 0 < one) (k : ℕ) (a : M):
    (kfloor hone k a) • one ≤ ((2 ^ k) • a) :=
  (existsUnique_zsmul_near_of_pos hone ((2 ^ k) • a)).choose_spec.1.1

def Archimedean.kfloor_right {one : M} (hone: 0 < one) (k : ℕ) (a : M):
    ((2 ^ k) • a) < (kfloor hone k a + 1) • one :=
  (existsUnique_zsmul_near_of_pos hone ((2 ^ k) • a)).choose_spec.1.2

def Archimedean.kfloor_next {one : M} (hone: 0 < one) (k : ℕ) (a : M):
    kfloor hone (k + 1) a ∈ Set.Ico (2 * (kfloor hone k a)) (2 * (kfloor hone k a + 1)) := by

  obtain hleft := (smul_le_smul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr <|
    Archimedean.kfloor_left hone k a
  obtain hright := (smul_lt_smul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr <|
    Archimedean.kfloor_right hone k a
  rw [smul_smul, ← natCast_zsmul, smul_smul] at hleft hright
  norm_cast at hleft hright
  have : (2 * 2 ^ k : ℕ) = 2 ^ (k + 1) := by rw [add_comm, pow_add]; simp
  rw [this] at hleft hright

  obtain hleft' := Archimedean.kfloor_left hone (k + 1) a
  obtain hright' := Archimedean.kfloor_right hone (k + 1) a

  constructor
  · obtain h := hleft.trans_lt hright'
    rw [smul_lt_smul_iff_of_pos_right hone] at h
    exact Int.lt_add_one_iff.mp h
  · obtain h := hleft'.trans_lt hright
    rw [smul_lt_smul_iff_of_pos_right hone] at h
    exact h

def Archimedean.kfloor_next_n {one : M} (hone: 0 < one) (k : ℕ) (n : ℕ) (a : M):
    kfloor hone (k + n) a ∈ Set.Ico (2 ^ n * (kfloor hone k a)) (2 ^ n * (kfloor hone k a + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ihleft, ihright⟩ := ih
    obtain ihleft := (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr ihleft
    obtain ihright := (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr
      (Int.add_one_le_iff.mpr ihright)
    rw [← mul_assoc] at ihleft ihright
    have : (2 * 2 ^ n : ℤ) = 2 ^ (n + 1) := by rw [add_comm, pow_add]; simp
    rw [this] at ihleft ihright
    rw [mul_add] at ihright
    rw [show (2 * 1 : ℤ) = 1 + 1 by simp] at ihright
    rw [← add_assoc] at ihright
    obtain ihright' := Int.add_one_le_iff.mp ihright

    rw [← add_assoc]
    obtain ⟨hleft, hright⟩ := Archimedean.kfloor_next hone (k + n) a
    constructor
    · exact ihleft.trans hleft
    · have hright' : kfloor hone (k + n + 1) a ≤ 2 * (kfloor hone (k + n) a) + 1 := by
        rw [mul_add] at hright
        simp only [mul_one] at hright
        apply Int.lt_add_one_iff.mp
        rw [add_assoc _ 1 1]
        simpa using hright

      apply hright'.trans_lt ihright

theorem εbound {ε : ℚ} (h : 0 < ε) : 1 < ε * (2 ^ (⌊ε⁻¹⌋₊)) := by
  suffices ε⁻¹ < 2 ^ (⌊ε⁻¹⌋₊) by
    apply (inv_mul_lt_iff₀ h).mp
    simpa using this
  apply lt_of_lt_of_le (b := (⌊ε⁻¹⌋₊ + 1 : ℚ))
  · exact Nat.lt_floor_add_one ε⁻¹
  · generalize ⌊ε⁻¹⌋₊ = n
    norm_cast
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.pow_add_one, mul_two]
      apply add_le_add ih
      exact Nat.one_le_two_pow



noncomputable
abbrev Archimedean.embedRealFun {one : M} (hone: 0 < one) (a : M) : ℝ :=
  let seq (k : ℕ) := (Archimedean.kfloor hone k a / (2 ^ k) : ℚ)
  let causeq : CauSeq ℚ abs := ⟨seq, by
    intro ε hε
    use ⌊ε⁻¹⌋₊
    intro k hk
    unfold seq
    have : (↑(kfloor hone ⌊ε⁻¹⌋₊ a) / 2 ^ ⌊ε⁻¹⌋₊ : ℚ) = 2 ^ (k - ⌊ε⁻¹⌋₊) * ↑(kfloor hone ⌊ε⁻¹⌋₊ a)  / 2 ^ k := by
      rw [div_eq_div_iff (by simp) (by simp)]
      rw [mul_comm (2 ^ (k - ⌊ε⁻¹⌋₊)), mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    rw [this]
    rw [← sub_div, abs_div]
    rw [div_lt_iff₀ (by simp)]
    apply lt_of_le_of_lt (b := 2 ^ (k - ⌊ε⁻¹⌋₊))
    · have : k = k - ⌊ε⁻¹⌋₊ + ⌊ε⁻¹⌋₊ := (Nat.sub_eq_iff_eq_add hk).mp rfl
      nth_rw 1 [this]
      obtain ⟨hleft, hright⟩ := Archimedean.kfloor_next_n hone ⌊ε⁻¹⌋₊ (k - ⌊ε⁻¹⌋₊) a
      rw [abs_le]
      constructor
      · simp only [neg_le_sub_iff_le_add]
        qify at hleft
        apply le_trans hleft
        rw [add_comm]
        simp only [le_add_iff_nonneg_right]
        simp
      · apply sub_left_le_of_le_add
        rw [add_comm]
        qify at hright
        rw [← mul_add_one]
        exact le_of_lt hright
    · rw [abs_eq_self.mpr (by simp)]
      rw [← one_lt_div (by simp)]
      rw [mul_div_assoc, div_eq_mul_inv]
      rw [← pow_sub₀ _ (by simp) (by simp), Nat.sub_sub_self (hk)]
      exact εbound hε
  ⟩
  Real.mk causeq

theorem Archimedean.embedReal_map_zero {one : M} (hone: 0 < one) : embedRealFun hone 0 = 0 := by
    convert Real.mk_zero
    rw [Subtype.eq_iff]
    simp only [CauSeq.coe_zero]
    ext k
    obtain hleft := Archimedean.kfloor_left hone k 0
    obtain hright := Archimedean.kfloor_right hone k 0
    rw [smul_zero] at hleft hright
    rw [smul_nonpos_iff] at hleft
    rw [or_iff_right (by simp [hone])] at hleft
    rw [smul_pos_iff_of_pos_right hone] at hright
    obtain hle := hleft.1
    obtain hge := Int.add_one_le_iff.mpr (Int.sub_lt_iff.mpr hright)
    simp only [zero_sub, Int.reduceNeg, neg_add_cancel] at hge
    obtain heq := le_antisymm hle hge
    simpa using heq

theorem Archimedean.embedReal_map_add {one : M} (hone: 0 < one) (a b : M) :
    embedRealFun hone (a + b) = embedRealFun hone a + embedRealFun hone b := by
  unfold embedRealFun
  simp only [smul_add, and_imp]
  rw [← Real.mk_add, Real.mk_eq]
  unfold HasEquiv.Equiv instHasEquivOfSetoid CauSeq.equiv
  simp only
  intro ε hε
  use ⌊ε⁻¹⌋₊
  intro k hk
  simp only [CauSeq.sub_apply, CauSeq.add_apply]
  rw [← add_div, ← sub_div, abs_div]
  rw [div_lt_iff₀ (by simp)]
  apply lt_of_le_of_lt (b := 1)
  · obtain hal := Archimedean.kfloor_left hone k a
    obtain har := Archimedean.kfloor_right hone k a
    obtain hbl := Archimedean.kfloor_left hone k b
    obtain hbr := Archimedean.kfloor_right hone k b
    obtain habl := Archimedean.kfloor_left hone k (a + b)
    obtain habr := Archimedean.kfloor_right hone k (a + b)
    obtain habl' := add_le_add hal hbl
    obtain habr' := add_lt_add har hbr
    rw [← smul_add, ← add_smul] at habl' habr'

    obtain hab1 := (smul_lt_smul_iff_of_pos_right hone).mp <| lt_of_le_of_lt habl' habr
    obtain hab2 := (smul_lt_smul_iff_of_pos_right hone).mp <| lt_of_le_of_lt habl habr'
    rw [add_right_comm] at hab2
    rw [Int.lt_add_one_iff] at hab2
    rw [← add_assoc] at hab2
    qify at hab1 hab2

    rw [abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      exact hab1.le
    · apply sub_left_le_of_le_add
      exact hab2
  · rw [abs_eq_self.mpr (by simp)]
    apply lt_of_lt_of_le (b := ε * 2 ^ ⌊ε⁻¹⌋₊)
    · exact εbound hε
    · rw [mul_le_mul_left hε]
      refine pow_le_pow_right₀ (by simp) hk

theorem Archimedean.embedReal_strictMono {one : M} (hone: 0 < one) :
    StrictMono (embedRealFun hone) := by
  intro a b hab
  have : b = a + (b - a) := by abel
  rw [this, Archimedean.embedReal_map_add]
  simp only [lt_add_iff_pos_right]
  set x := b - a
  have hx : 0 < x := sub_pos.mpr hab
  obtain ⟨s, hs⟩ := Archimedean.arch one hx

  unfold embedRealFun
  simp only [Real.mk_pos]


  have hpos : ∃k, 0 < kfloor hone k x := by
    by_contra! hkfloor
    have (k) : (kfloor hone k x + 1) • one ≤ one := by
      nth_rw 3 [show one = (1: ℤ) • one by simp]
      rw [smul_le_smul_iff_of_pos_right hone]
      simpa using hkfloor k
    have (k) : ((2 ^ k) • x) < one := by
      refine lt_of_lt_of_le ?_ (this k)
      apply Archimedean.kfloor_right
    obtain hxx := lt_of_lt_of_le (this s) hs
    -- optimize?
    rw [← natCast_zsmul, ← natCast_zsmul] at hxx
    rw [zsmul_lt_zsmul_iff_left hx] at hxx
    norm_cast at hxx

    contrapose! hxx
    generalize s = a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.pow_add_one, mul_two]
      exact add_le_add ih Nat.one_le_two_pow

  obtain ⟨k, hk⟩ := hpos
  use 1 / 2 ^ k
  refine ⟨by simp, ?_⟩
  use k
  intro j hj
  obtain hleft := (Archimedean.kfloor_next_n hone k (j - k) x).1
  have : k + (j - k) = j := by exact Nat.add_sub_of_le hj
  rw [this] at hleft
  qify at hleft

  simp only
  rw [le_div_iff₀ (by simp), one_div_mul_eq_div]
  rw [div_eq_mul_inv]
  rw [← pow_sub₀ _ (by simp) hj]
  refine le_trans ?_ hleft
  simp only [Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_right]
  norm_cast

noncomputable
def Archimedean.embedReal_of_pos {one : M} (hone: 0 < one) : M →+o ℝ where
  toFun := embedRealFun hone
  map_zero' := embedReal_map_zero hone
  map_add' := embedReal_map_add hone
  monotone' := (embedReal_strictMono hone).monotone

theorem Archimedean.embedReal_of_pos_injective {one : M} (hone: 0 < one) :
    Function.Injective (embedReal_of_pos hone) :=
  (embedReal_strictMono hone).injective

noncomputable
def Archimedean.embedReal_of_trivial : M →+o ℝ where
  toFun := fun _ ↦ 0
  map_zero' := by simp
  map_add' := by simp
  monotone' := by
    intro a b h
    simp

theorem Archimedean.embedReal_of_trivial_injective {M : Type*} [AddCommGroup M] [LinearOrder M]
    (h : Subsingleton M) :
    Function.Injective (embedReal_of_trivial (M := M)) :=
  Function.injective_of_subsingleton embedReal_of_trivial

open Classical in
variable (M) in
noncomputable
def Archimedean.embedReal : M →+o ℝ :=
  if h : Subsingleton M then
    embedReal_of_trivial
  else
    have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    let h := exists_ne (0 : M)
    let a := h.choose
    have ha : 0 < |a| := by simpa using h.choose_spec
    embedReal_of_pos ha


variable (M) in
theorem Archimedean.embedReal_injective : Function.Injective (embedReal M) := by
  unfold embedReal
  split_ifs with h
  · exact embedReal_of_trivial_injective h
  · apply embedReal_of_pos_injective

variable (M) in
noncomputable
def Archimedean.embedReal_orderEmbedding : M ↪o ℝ where
  toFun := Archimedean.embedReal M
  inj' := Archimedean.embedReal_injective M
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      contrapose! h
      apply lt_of_le_of_ne
      · apply OrderHomClass.monotone (embedReal M) h.le
      · contrapose! h
        apply le_of_eq
        exact (Archimedean.embedReal_injective M) h.symm
    · intro h
      apply OrderHomClass.monotone (embedReal M) h
