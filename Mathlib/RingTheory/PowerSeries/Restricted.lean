import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.Ultra

variable (c : NNReal) (R : Type*) [NormedRing R]

open PowerSeries Filter IsUltrametricDist
open scoped Topology

/-- The convergence property for restricted powerseries. -/
def Convergent (f : PowerSeries R) : Prop :=
  Tendsto (fun (i : ℕ) => (norm (coeff R i f)) * c^i) atTop (𝓝 0)

/-- The set of restricted powerseries over a normed ring `R` for a given parameter `c` as a subset
of the powerseries over `R`. -/
def CRestrictedPowerSeries : Set (PowerSeries R) :=
  {f | Convergent c R f}

namespace CRestrictedPowerSeries

def zero : (0 : PowerSeries R) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_zero, norm_zero,
  zero_mul, tendsto_const_nhds_iff]

def one : (1 : PowerSeries R) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, coeff_one,
    @NormedAddCommGroup.tendsto_atTop, sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs,
    NNReal.abs_eq]
  intro ε hε
  use 1
  intro n hn
  simp only [Nat.ne_zero_of_lt hn, ↓reduceIte, norm_zero, zero_mul, gt_iff_lt]
  exact hε

/-- Addition is closed. -/
def add (f g : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R)
    (hg : g ∈ CRestrictedPowerSeries c R) : f + g ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_add]
  have h1 : ∀ (t : ℕ), 0 ≤ ‖(coeff R t) f + (coeff R t) g‖ * c ^ t := by
    intro t
    exact mul_nonneg (norm_nonneg _) (pow_nonneg c.2 t)
  have h2 : ∀ (t : ℕ), ‖(coeff R t) f + (coeff R t) g‖ * c ^ t ≤ ‖coeff R t f‖ * c^t +
      ‖coeff R t g‖ * c^t := by
    intro t
    have := mul_le_mul_of_nonneg_right (norm_add_le (coeff R t f) (coeff R t g))
        (pow_nonneg c.2 t)
    rw [RightDistribClass.right_distrib] at this
    exact this
  have h3 : Tendsto (fun t ↦ ‖(coeff R t) f‖ * c ^ t + ‖(coeff R t) g‖ * c ^ t) atTop (𝓝 0) := by
    have := Tendsto.add hf hg
    simp only [add_zero] at this
    exact this
  exact squeeze_zero h1 h2 h3

/-- Negation is closed. -/
def neg (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    (-f) ∈ CRestrictedPowerSeries c R:= by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, map_neg, norm_neg]
  exact hf

def addsubgroup : AddSubgroup (PowerSeries R) where
  carrier := CRestrictedPowerSeries c R
  zero_mem' := zero c R
  add_mem' := by
    intro f g hf hg
    exact add c R f g hf hg
  neg_mem' := by
    intro f hf
    exact neg c R f hf

/-- The restricted powerseries over a normed ring `R` form an additive group for a given
paramter `c`. -/
noncomputable
instance IsAddSubgroup : AddGroup (CRestrictedPowerSeries c R) :=
    AddSubgroup.toAddGroup (addsubgroup c R)

variable [IsUltrametricDist R]


def bddabove (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    BddAbove {‖coeff R i f‖ * c^i | i : ℕ} := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq,
    NormedAddCommGroup.tendsto_atTop] at hf
  specialize hf 1
  simp only [zero_lt_one, sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq,
   forall_const, abs_norm] at hf
  obtain ⟨N, hf⟩ := hf
  simp_rw [@bddAbove_def]
  have h : (Finset.image (fun i => ‖coeff R i f‖ * c^i) (Finset.range (N+1))).Nonempty := by
    simp only [Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  use max 1 (Finset.max' (Finset.image (fun i => ‖coeff R i f‖ * c^i) (Finset.range (N+1))) h)
  simp only [Set.mem_setOf_eq, le_sup_iff, forall_exists_index, forall_apply_eq_imp_iff]
  intro a
  cases' (Nat.le_total a N) with h h
  · right
    apply Finset.le_max'
    simp only [Finset.mem_image, Finset.mem_range]
    use a
    constructor
    · exact Order.lt_add_one_iff.mpr h
    · rfl
  · left
    exact le_of_lt (hf a h)

def bddabove_nneg (f : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R) :
    ∃ A : ℝ, A > 0 ∧ ∀ i : ℕ, ‖coeff R i f‖ * c^i ≤ A := by
  have := bddabove c R f hf
  rw [@bddAbove_def] at this
  obtain ⟨x, h⟩ := this
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at h
  use x + 1
  constructor
  · have : x ≥ 0 := by
      have : 0 ≤ ‖(coeff R 0) f‖ * c^0 := by
        simp only [coeff_zero_eq_constantCoeff, pow_zero, mul_one, norm_nonneg]
      exact le_trans this (h 0)
    rw [← add_zero x] at this
    exact lt_of_le_of_lt this ((add_lt_add_iff_left x).mpr (zero_lt_one' ℝ))
  · have : x ≤ x + 1 := by
      nth_rw 1 [← add_zero x]
      exact (add_le_add_iff_left x).mpr (zero_le_one' ℝ)
    intro i
    exact le_trans (h i) this

/-- Multiplication is closed. -/
def mul (f g : PowerSeries R) (hf : f ∈ CRestrictedPowerSeries c R)
    (hg : g ∈ CRestrictedPowerSeries c R) : (f * g) ∈ CRestrictedPowerSeries c R := by
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, @NormedAddCommGroup.tendsto_atTop,
    sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq, PowerSeries.coeff_mul]
  intro ε hε
  obtain ⟨a, ha, fBound1⟩ := bddabove_nneg c R f hf
  obtain ⟨b, hb, gBound1⟩ := bddabove_nneg c R g hg
  simp_rw [CRestrictedPowerSeries, Convergent, Set.mem_setOf_eq, @NormedAddCommGroup.tendsto_atTop,
    sub_zero, norm_mul, norm_norm, norm_pow, Real.norm_eq_abs, NNReal.abs_eq] at hf hg
  obtain ⟨Nf, fBound2⟩ := (hf (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  obtain ⟨Ng, gBound2⟩ := (hg (ε/ (max a b))) (div_pos hε (lt_sup_of_lt_left ha))
  use 2 * max Nf Ng
  intro n hn
  have Nonempty : (Finset.antidiagonal n).Nonempty := by
    use (0,n)
    simp only [Finset.mem_antidiagonal, zero_add]
  obtain ⟨i, hi, ultrametric⟩ := exists_norm_finset_add_le (Finset.antidiagonal n)
    (fun a => (coeff R a.1) f * (coeff R a.2) g)
  apply hi at Nonempty
  have InterimBound1 := mul_le_mul_of_nonneg_right ultrametric (zero_le (c ^ n))
  have InterimBound2 := mul_le_mul_of_nonneg_right
    (NormedRing.norm_mul_le ((coeff R i.1) f) ((coeff R i.2) g)) (zero_le (c ^ n))
  have : ‖(coeff R i.1) f‖ * ‖(coeff R i.2) g‖ * ↑c^n =
      ‖(coeff R i.1) f‖ * ↑c^i.1 * (‖(coeff R i.2) g‖ * ↑c^i.2) := by
    ring_nf
    simp only [Finset.mem_antidiagonal] at Nonempty
    simp_rw [mul_assoc, ←Nonempty, pow_add]
  simp only [NNReal.val_eq_coe, NNReal.coe_pow, this] at InterimBound2
  have : i.1 ≥ max Nf Ng ∨ i.2 ≥ max Nf Ng := by
    simp only [Finset.mem_antidiagonal] at Nonempty
    rw [← Nonempty] at hn
    have : i.1 + i.2 ≤ 2 * max i.1 i.2 := by
      cases' (Nat.le_total i.1 i.2) with h h
      · rw [congrArg (HMul.hMul 2) (Nat.max_eq_right h), Nat.two_mul]
        exact Nat.add_le_add_right h i.2
      · rw [congrArg (HMul.hMul 2) (Nat.max_eq_left h), Nat.two_mul]
        exact Nat.add_le_add_left h i.1
    have := le_trans hn this
    simp only [Nat.ofNat_pos, mul_le_mul_left] at this
    exact le_sup_iff.mp this
  cases' this with this this
  · have FinalBound1 := mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ((fBound2 i.1)
      (le_of_max_le_left this)) (gBound1 i.2) (Left.mul_nonneg (norm_nonneg ((coeff R i.1) f))
      (zero_le (c ^ i.1))) hb
    have FinalBound2 : ε / (max a b) * b ≤ ε := by
      cases' (max_choice a b) with h h
      · rw [h]
        ring_nf
        rw [mul_assoc]
        nth_rw 2 [mul_comm]
        rw [← mul_assoc]
        exact (mul_inv_le_iff₀ ha).mpr ((mul_le_mul_iff_of_pos_left hε).mpr (sup_eq_left.mp h))
      · rw [h]
        ring_nf
        rw [mul_assoc]
        simp_rw [CommGroupWithZero.mul_inv_cancel b (ne_of_gt hb), mul_one, le_refl]
    exact lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound1)
      FinalBound2
  · have FinalBound1 := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (fBound1 i.1) ((gBound2 i.2)
      (le_of_max_le_right this)) (Left.mul_nonneg (norm_nonneg ((coeff R i.2) g))
      (zero_le (c ^ i.2))) ha
    apply lt_of_lt_of_le (lt_of_le_of_lt (le_trans InterimBound1 InterimBound2) FinalBound1)
    cases' (max_choice a b) with h h
    · rw [h]
      ring_nf
      rw [mul_comm, ←mul_assoc]
      have := CommGroupWithZero.mul_inv_cancel a (ne_of_gt ha)
      rw [mul_comm] at this
      simp_rw [this, one_mul, le_refl]
    · rw [h]
      ring_nf
      rw [mul_assoc, mul_comm, mul_assoc]
      nth_rw 2 [mul_comm]
      rw [← mul_assoc]
      have h : max b a = b := by
        simp only [sup_eq_left]
        simp only [sup_eq_right] at h
        exact h
      exact (mul_inv_le_iff₀ hb).mpr ((mul_le_mul_iff_of_pos_left hε).mpr (sup_eq_left.mp h))

def subring: Subring (PowerSeries R) where
  carrier := CRestrictedPowerSeries c R
  zero_mem' := zero c R
  add_mem' := by
    intro f g hf hg
    exact add c R f g hf hg
  neg_mem' := by
    intro f hf
    exact neg c R f hf
  one_mem' := one c R
  mul_mem' := by
    intro f g hf hg
    exact mul c R f g hf hg

/-- The restricted powerseries over a normed ring `R` with the ultrametric property form a ring for
a given parameter `c`. -/
noncomputable
instance IsRing  : Ring (CRestrictedPowerSeries c R) :=
    Subring.toRing (subring c R)
