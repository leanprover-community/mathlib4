/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The unit interval, as a topological space

Use `open unitInterval` to turn on the notation `I := Set.Icc (0 : ℝ) (1 : ℝ)`.

We provide basic instances, as well as a custom tactic for discharging
`0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` when `x : I`.

-/

@[expose] public section

noncomputable section

open Topology Filter Set Int Set.Icc

/-! ### The unit interval -/


/-- The unit interval `[0,1]` in ℝ. -/
abbrev unitInterval : Set ℝ :=
  Set.Icc 0 1

@[inherit_doc]
scoped[unitInterval] notation "I" => unitInterval

namespace unitInterval

theorem zero_mem : (0 : ℝ) ∈ I :=
  ⟨le_rfl, zero_le_one⟩

theorem one_mem : (1 : ℝ) ∈ I :=
  ⟨zero_le_one, le_rfl⟩

theorem mul_mem {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
  ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩

theorem div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
  ⟨div_nonneg hx hy, div_le_one_of_le₀ hxy hy⟩

theorem fract_mem (x : ℝ) : fract x ∈ I :=
  ⟨fract_nonneg _, (fract_lt_one _).le⟩

lemma univ_eq_Icc : (univ : Set I) = Icc (0 : I) (1 : I) := Icc_bot_top.symm

@[norm_cast] theorem coe_ne_zero {x : I} : (x : ℝ) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not

@[norm_cast] theorem coe_ne_one {x : I} : (x : ℝ) ≠ 1 ↔ x ≠ 1 := coe_eq_one.not

@[simp, norm_cast] theorem coe_pos {x : I} : (0 : ℝ) < x ↔ 0 < x := Iff.rfl

@[simp, norm_cast] theorem coe_lt_one {x : I} : (x : ℝ) < 1 ↔ x < 1 := Iff.rfl

theorem mul_le_left {x y : I} : x * y ≤ x :=
  Subtype.coe_le_coe.mp <| mul_le_of_le_one_right x.2.1 y.2.2

theorem mul_le_right {x y : I} : x * y ≤ y :=
  Subtype.coe_le_coe.mp <| mul_le_of_le_one_left y.2.1 x.2.2

theorem eq_closedBall : I = Metric.closedBall 2⁻¹ 2⁻¹ := by
  norm_num [unitInterval, Real.Icc_eq_closedBall]

/-- Unit interval central symmetry. -/
def symm : I → I := fun t => ⟨1 - t, Icc.mem_iff_one_sub_mem.mp t.prop⟩

@[inherit_doc]
scoped notation "σ" => unitInterval.symm

@[simp, grind =]
theorem symm_zero : σ 0 = 1 :=
  Subtype.ext <| by simp [symm]

@[simp, grind =]
theorem symm_one : σ 1 = 0 :=
  Subtype.ext <| by simp [symm]

@[simp, grind =]
theorem symm_symm (x : I) : σ (σ x) = x :=
  Subtype.ext <| by simp [symm]

theorem symm_involutive : Function.Involutive (symm : I → I) := symm_symm

theorem symm_bijective : Function.Bijective (symm : I → I) := symm_involutive.bijective

@[simp, grind =]
theorem coe_symm_eq (x : I) : (σ x : ℝ) = 1 - x :=
  rfl

lemma image_coe_preimage_symm {s : Set I} :
    Subtype.val '' (σ ⁻¹' s) = (1 - ·) ⁻¹' (Subtype.val '' s) := by
  simp [symm_involutive, ← Function.Involutive.image_eq_preimage_symm, image_image]

@[simp]
theorem symm_projIcc (x : ℝ) :
    symm (projIcc 0 1 zero_le_one x) = projIcc 0 1 zero_le_one (1 - x) := by
  ext
  rcases le_total x 0 with h₀ | h₀
  · simp [projIcc_of_le_left, projIcc_of_right_le, h₀]
  · rcases le_total x 1 with h₁ | h₁
    · lift x to I using ⟨h₀, h₁⟩
      simp_rw [← coe_symm_eq, projIcc_val]
    · simp [projIcc_of_le_left, projIcc_of_right_le, h₁]

@[continuity, fun_prop]
theorem continuous_symm : Continuous σ :=
  Continuous.subtype_mk (by fun_prop) _

/-- `unitInterval.symm` as a `Homeomorph`. -/
@[simps]
def symmHomeomorph : I ≃ₜ I where
  toFun := symm
  invFun := symm
  left_inv := symm_symm
  right_inv := symm_symm

theorem strictAnti_symm : StrictAnti σ := fun _ _ h ↦ sub_lt_sub_left (α := ℝ) h _


@[simp]
theorem symm_inj {i j : I} : σ i = σ j ↔ i = j := symm_bijective.injective.eq_iff

theorem half_le_symm_iff (t : I) : 1 / 2 ≤ (σ t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 := by
  rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le, sub_half]

@[simp]
lemma symm_eq_one {i : I} : σ i = 1 ↔ i = 0 := by
  rw [← symm_zero, symm_inj]

@[simp]
lemma symm_eq_zero {i : I} : σ i = 0 ↔ i = 1 := by
  rw [← symm_one, symm_inj]

@[simp]
theorem symm_le_symm {i j : I} : σ i ≤ σ j ↔ j ≤ i := by
  simp only [symm, Subtype.mk_le_mk, sub_le_sub_iff, add_le_add_iff_left, Subtype.coe_le_coe]

theorem le_symm_comm {i j : I} : i ≤ σ j ↔ j ≤ σ i := by
  rw [← symm_le_symm, symm_symm]

theorem symm_le_comm {i j : I} : σ i ≤ j ↔ σ j ≤ i := by
  rw [← symm_le_symm, symm_symm]

@[simp]
theorem symm_lt_symm {i j : I} : σ i < σ j ↔ j < i := by
  simp only [symm, Subtype.mk_lt_mk, sub_lt_sub_iff_left, Subtype.coe_lt_coe]

theorem lt_symm_comm {i j : I} : i < σ j ↔ j < σ i := by
  rw [← symm_lt_symm, symm_symm]

theorem symm_lt_comm {i j : I} : σ i < j ↔ σ j < i := by
  rw [← symm_lt_symm, symm_symm]

instance : ConnectedSpace I :=
  Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩

/-- Verify there is an instance for `CompactSpace I`. -/
example : CompactSpace I := by infer_instance

theorem nonneg (x : I) : 0 ≤ (x : ℝ) :=
  x.2.1

theorem one_minus_nonneg (x : I) : 0 ≤ 1 - (x : ℝ) := by simpa using x.2.2

theorem le_one (x : I) : (x : ℝ) ≤ 1 :=
  x.2.2

theorem one_minus_le_one (x : I) : 1 - (x : ℝ) ≤ 1 := by simpa using x.2.1

theorem add_pos {t : I} {x : ℝ} (hx : 0 < x) : 0 < (x + t : ℝ) :=
  add_pos_of_pos_of_nonneg hx <| nonneg _

/-- like `unitInterval.nonneg`, but with the inequality in `I`. -/
theorem nonneg' {t : I} : 0 ≤ t :=
  t.2.1

/-- like `unitInterval.le_one`, but with the inequality in `I`. -/
theorem le_one' {t : I} : t ≤ 1 :=
  t.2.2

protected lemma pos_iff_ne_zero {x : I} : 0 < x ↔ x ≠ 0 := bot_lt_iff_ne_bot

protected lemma lt_one_iff_ne_one {x : I} : x < 1 ↔ x ≠ 1 := lt_top_iff_ne_top

lemma eq_one_or_eq_zero_of_le_mul {i j : I} (h : i ≤ j * i) : i = 0 ∨ j = 1 := by
  contrapose! h
  rw [← unitInterval.lt_one_iff_ne_one, ← coe_lt_one, ← unitInterval.pos_iff_ne_zero,
    ← coe_pos] at h
  rw [← Subtype.coe_lt_coe, coe_mul]
  simpa using mul_lt_mul_of_pos_right h.right h.left

instance : Nontrivial I := ⟨⟨1, 0, (one_ne_zero <| congrArg Subtype.val ·)⟩⟩

theorem mul_pos_mem_iff {a t : ℝ} (ha : 0 < a) : a * t ∈ I ↔ t ∈ Set.Icc (0 : ℝ) (1 / a) := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
  · exact nonneg_of_mul_nonneg_right h₁ ha
  · rwa [le_div_iff₀ ha, mul_comm]
  · exact mul_nonneg ha.le h₁
  · rwa [le_div_iff₀ ha, mul_comm] at h₂

theorem two_mul_sub_one_mem_iff {t : ℝ} : 2 * t - 1 ∈ I ↔ t ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The unit interval as a submonoid of ℝ. -/
def submonoid : Submonoid ℝ where
  carrier := unitInterval
  one_mem' := unitInterval.one_mem
  mul_mem' := unitInterval.mul_mem

@[simp] theorem coe_unitIntervalSubmonoid : submonoid = unitInterval := rfl
@[simp] theorem mem_unitIntervalSubmonoid {x} : x ∈ submonoid ↔ x ∈ unitInterval :=
  Iff.rfl

protected theorem prod_mem {ι : Type*} {t : Finset ι} {f : ι → ℝ}
    (h : ∀ c ∈ t, f c ∈ unitInterval) :
    ∏ c ∈ t, f c ∈ unitInterval := _root_.prod_mem (S := unitInterval.submonoid) h

instance : LinearOrderedCommMonoidWithZero I where
  zero_mul i := zero_mul i
  mul_zero i := mul_zero i
  zero_le x := x.2.1
  mul_lt_mul_of_pos_left i hi j k hjk := by
    simp only [← Subtype.coe_lt_coe, coe_mul]; gcongr

lemma subtype_Iic_eq_Icc (x : I) : Subtype.val ⁻¹' (Iic ↑x) = Icc 0 x := by
  rw [preimage_subtype_val_Iic]
  exact Icc_bot.symm

lemma subtype_Iio_eq_Ico (x : I) : Subtype.val ⁻¹' (Iio ↑x) = Ico 0 x := by
  rw [preimage_subtype_val_Iio]
  exact Ico_bot.symm

lemma subtype_Ici_eq_Icc (x : I) : Subtype.val ⁻¹' (Ici ↑x) = Icc x 1 := by
  rw [preimage_subtype_val_Ici]
  exact Icc_top.symm

lemma subtype_Ioi_eq_Ioc (x : I) : Subtype.val ⁻¹' (Ioi ↑x) = Ioc x 1 := by
  rw [preimage_subtype_val_Ioi]
  exact Ioc_top.symm

end unitInterval

section partition

namespace Set.Icc

variable {α} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {a b c d : α} (h : a ≤ b) {δ : α}

-- TODO: Set.projIci, Set.projIic
/-- `Set.projIcc` is a contraction. -/
lemma _root_.Set.abs_projIcc_sub_projIcc : (|projIcc a b h c - projIcc a b h d| : α) ≤ |c - d| := by
  wlog hdc : d ≤ c generalizing c d
  · rw [abs_sub_comm, abs_sub_comm c]; exact this (le_of_not_ge hdc)
  rw [abs_eq_self.2 (sub_nonneg.2 hdc),
    abs_eq_self.2 (sub_nonneg.2 <| mod_cast monotone_projIcc h hdc)]
  rw [← sub_nonneg] at hdc
  refine (max_sub_max_le_max _ _ _ _).trans (max_le (by rwa [sub_self]) ?_)
  refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rwa [sub_self, abs_zero]
  · exact (abs_eq_self.mpr hdc).le

/-- When `h : a ≤ b` and `δ > 0`, `addNSMul h δ` is a sequence of points in the closed interval
`[a,b]`, which is initially equally spaced but eventually stays at the right endpoint `b`. -/
def addNSMul (δ : α) (n : ℕ) : Icc a b := projIcc a b h (a + n • δ)

omit [IsOrderedAddMonoid α] in
lemma addNSMul_zero : addNSMul h δ 0 = a := by
  rw [addNSMul, zero_smul, add_zero, projIcc_left]

lemma addNSMul_eq_right [Archimedean α] (hδ : 0 < δ) :
    ∃ m, ∀ n ≥ m, addNSMul h δ n = b := by
  obtain ⟨m, hm⟩ := Archimedean.arch (b - a) hδ
  refine ⟨m, fun n hn ↦ ?_⟩
  rw [addNSMul, coe_projIcc, add_comm, min_eq_left_iff.mpr, max_eq_right h]
  exact sub_le_iff_le_add.mp (hm.trans <| nsmul_le_nsmul_left hδ.le hn)

lemma monotone_addNSMul (hδ : 0 ≤ δ) : Monotone (addNSMul h δ) :=
  fun _ _ hnm ↦ monotone_projIcc h <| (add_le_add_iff_left _).mpr (nsmul_le_nsmul_left hδ hnm)

lemma abs_sub_addNSMul_le (hδ : 0 ≤ δ) {t : Icc a b} (n : ℕ)
    (ht : t ∈ Icc (addNSMul h δ n) (addNSMul h δ (n + 1))) :
    (|t - addNSMul h δ n| : α) ≤ δ :=
  calc
    (|t - addNSMul h δ n| : α) = t - addNSMul h δ n := abs_eq_self.2 <| sub_nonneg.2 ht.1
    _ ≤ projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n := by apply sub_le_sub_right; exact ht.2
    _ ≤ (|projIcc a b h (a + (n + 1) • δ) - addNSMul h δ n| : α) := le_abs_self _
    _ ≤ |a + (n + 1) • δ - (a + n • δ)| := abs_projIcc_sub_projIcc h
    _ ≤ δ := by
          rw [add_sub_add_comm, sub_self, zero_add, succ_nsmul', add_sub_cancel_right]
          exact (abs_eq_self.mpr hδ).le

/--
Form a convex linear combination of two points in a closed interval.

This should be removed once a general theory of convex spaces is available in Mathlib.
-/
def convexCombo {a b : ℝ} (x y : Icc a b) (t : unitInterval) : Icc a b :=
  ⟨(1 - t) * x + t * y, by
    constructor
    · nlinarith [x.2.1, y.2.1, t.2.1, t.2.2]
    · nlinarith [x.2.2, y.2.2, t.2.1, t.2.2]⟩

@[simp, grind =]
theorem coe_convexCombo {a b : ℝ} (x y : Icc a b) (t : unitInterval) :
  (convexCombo x y t : ℝ) = (1 - t) * x + t * y := rfl

@[simp, grind =]
theorem convexCombo_zero {a b : ℝ} (x y : Icc a b) : convexCombo x y 0 = x := by
  simp [convexCombo]

@[simp, grind =]
theorem convexCombo_one {a b : ℝ} (x y : Icc a b) : convexCombo x y 1 = y := by
  simp [convexCombo]

@[simp, grind =]
theorem convexCombo_zero_one (t : unitInterval) : convexCombo 0 1 t = t := by
  simp [convexCombo]

@[simp, grind =]
theorem convexCombo_eq {a b : ℝ} (x : Icc a b) (t : unitInterval) : convexCombo x x t = x := by
  simp [convexCombo, sub_mul]

@[simp, grind =]
theorem convexCombo_symm {a b : ℝ} (x y : Icc a b) (t : unitInterval) :
    convexCombo x y (unitInterval.symm t) = convexCombo y x t := by
  simp [convexCombo]
  abel

@[grind .]
theorem le_convexCombo {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    x ≤ convexCombo x y t := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[grind .]
theorem convexCombo_le {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    convexCombo x y t ≤ y := by
  rw [← Subtype.coe_le_coe] at h ⊢
  simp
  nlinarith [t.2.1, t.2.2]

@[continuity, fun_prop]
theorem continuous_convexCombo {a b : ℝ} (x y : Icc a b) : Continuous (convexCombo x y) := by
  unfold Icc.convexCombo
  fun_prop

@[continuity, fun_prop]
theorem continuous_convexCombo_prod {a b : ℝ} :
    Continuous fun x : Icc a b × Icc a b × unitInterval ↦ Icc.convexCombo x.1 x.2.1 x.2.2 := by
  unfold Icc.convexCombo
  fun_prop

/--
Helper definition for `convexCombo_assoc`, giving one of the coefficients appearing
when we reassociate a convex combination.
-/
abbrev convexCombo_assoc_coeff₁ (s t : unitInterval) : unitInterval :=
  ⟨s * (1 - t) / (1 - s * t),
    by
      apply div_nonneg
      · nlinarith [s.2.1, t.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1],
    by
      apply div_le_one_of_le₀
      · nlinarith [s.2.2]
      · nlinarith [s.2.2, t.2.2, t.2.1]⟩

/--
Helper definition for `convexCombo_assoc`, giving one of the coefficients appearing
when we reassociate a convex combination.
-/
abbrev convexCombo_assoc_coeff₂ (s t : unitInterval) : unitInterval := s * t

private theorem one_sub_coe_ne_zero {t : unitInterval} (ht : (t : ℝ) ≠ 1) : (1 - t : ℝ) ≠ 0 := by
  grind

private theorem one_sub_mul_coe_ne_zero {s t : unitInterval}
    (ht : (t : ℝ) ≠ 1) : (1 - s * t : ℝ) ≠ 0 := by
  intro h
  have : 1 ≤ (t : ℝ) := by nlinarith [s.2.2, t.2.1]
  grind

theorem convexCombo_assoc {a b : ℝ} (x y z : Icc a b) (s t : unitInterval) :
    convexCombo x (convexCombo y z t) s =
      convexCombo (convexCombo x y (convexCombo_assoc_coeff₁ s t)) z
        (convexCombo_assoc_coeff₂ s t) := by
  simp only [convexCombo, coe_mul, Subtype.mk.injEq]
  by_cases hs : (s : ℝ) = 1
  · simp only [hs]
    by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · field_simp [one_sub_coe_ne_zero ht]
      ring
  · by_cases ht : (t : ℝ) = 1
    · simp [ht]
    · field_simp [one_sub_mul_coe_ne_zero ht]
      ring_nf

/--
Helper definition for `convexCombo_assoc'`, giving one of the coefficients appearing
when we reassociate a convex combination in the reverse direction.
-/
abbrev convexCombo_assoc_coeff₁' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexCombo_assoc_coeff₂ (unitInterval.symm t) (unitInterval.symm s))

/--
Helper definition for `convexCombo_assoc'`, giving one of the coefficients appearing
when we reassociate a convex combination in the reverse direction.
-/
abbrev convexCombo_assoc_coeff₂' (s t : unitInterval) : unitInterval :=
  unitInterval.symm (convexCombo_assoc_coeff₁ (unitInterval.symm t) (unitInterval.symm s))

theorem convexCombo_assoc' {a b : ℝ} (x y z : Icc a b) (s t : unitInterval) :
    convexCombo (convexCombo x y s) z t =
      convexCombo x (convexCombo y z (convexCombo_assoc_coeff₂' s t))
        (convexCombo_assoc_coeff₁' s t) := by
  rw [← convexCombo_symm, ← convexCombo_symm y x, convexCombo_assoc, ← convexCombo_symm x,
    ← convexCombo_symm z y]
  rw [convexCombo_assoc_coeff₁', convexCombo_assoc_coeff₂', unitInterval.symm_symm]

set_option backward.privateInPublic true in
private theorem eq_convexCombo.zero_le {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    0 ≤ ((y - x) / (z - x) : ℝ) := by
  by_cases h : (z - x : ℝ) = 0
  · simp_all
  · replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    apply div_nonneg <;> grind

set_option backward.privateInPublic true in
private theorem eq_convexCombo.le_one {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    ((y - x) / (z - x) : ℝ) ≤ 1 := by
  by_cases h : (z - x : ℝ) = 0
  · simp_all
  · replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    apply div_le_one_of_le₀ <;> grind

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
A point between two points in a closed interval
can be expressed as a convex combination of them.
-/
theorem eq_convexCombo {a b : ℝ} {x y z : Icc a b} (hxy : x ≤ y) (hyz : y ≤ z) :
    y = convexCombo x z ⟨((y - x) / (z - x)),
          eq_convexCombo.zero_le hxy hyz, eq_convexCombo.le_one hxy hyz⟩ := by
  ext
  simp only [coe_convexCombo]
  by_cases h : (z - x : ℝ) = 0
  · simp_all only [div_zero, sub_zero, one_mul, zero_mul, add_zero]
    replace hxy : (x : ℝ) ≤ (y : ℝ) := hxy
    replace hyz : (y : ℝ) ≤ (z : ℝ) := hyz
    linarith
  · field_simp
    ring_nf

end Set.Icc

open scoped unitInterval

private theorem mem_ball_addNSMul_of_mem_Icc {a b δ : ℝ} (h : a ≤ b) (δ_pos : 0 < δ)
    (n : ℕ) {t : Icc a b}
    (ht : t ∈ Icc (addNSMul h (δ / 2) n) (addNSMul h (δ / 2) (n + 1))) :
    t ∈ Metric.ball (addNSMul h (δ / 2) n) δ :=
  Metric.mem_ball.mpr <|
    (abs_sub_addNSMul_le h (half_pos δ_pos).le n ht).trans_lt <| half_lt_self δ_pos

private theorem mem_ball_addNSMul_prod_of_mem_Icc {δ : ℝ} (δ_pos : 0 < δ)
    (n m : ℕ) {t : I × I}
    (ht₁ : t.1 ∈ Icc (addNSMul zero_le_one (δ / 2) n) (addNSMul zero_le_one (δ / 2) (n + 1)))
    (ht₂ : t.2 ∈ Icc (addNSMul zero_le_one (δ / 2) m) (addNSMul zero_le_one (δ / 2) (m + 1))) :
    t ∈ Metric.ball (addNSMul zero_le_one (δ / 2) n, addNSMul zero_le_one (δ / 2) m) δ :=
  Metric.mem_ball.mpr <|
    (max_le (abs_sub_addNSMul_le zero_le_one (half_pos δ_pos).le n ht₁)
      (abs_sub_addNSMul_le zero_le_one (half_pos δ_pos).le m ht₂)).trans_lt <| half_lt_self δ_pos

/-- Any open cover `c` of a closed interval `[a, b]` in ℝ
can be refined to a finite partition into subintervals. -/
lemma exists_monotone_Icc_subset_open_cover_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → Icc a b, t 0 = a ∧
      Monotone t ∧ (∃ m, ∀ n ≥ m, t n = b) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  refine ⟨addNSMul h (δ/2), addNSMul_zero h,
    monotone_addNSMul h (half_pos δ_pos).le, addNSMul_eq_right h (half_pos δ_pos), fun n ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset (addNSMul h (δ / 2) n) trivial
  exact ⟨i, fun t ht ↦ hsub <| mem_ball_addNSMul_of_mem_Icc h δ_pos n ht⟩

/-- Any open cover of the unit interval can be refined to a finite partition into subintervals. -/
lemma exists_monotone_Icc_subset_open_cover_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧
      Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧ ∀ n, ∃ i, Icc (t n) (t (n + 1)) ⊆ c i := by
  simp_rw [← Subtype.coe_inj]
  exact exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂

lemma exists_monotone_Icc_subset_open_cover_unitInterval_prod_self {ι} {c : ι → Set (I × I)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n m, ∃ i, Icc (t n) (t (n + 1)) ×ˢ Icc (t m) (t (m + 1)) ⊆ c i := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  simp_rw [Subtype.ext_iff]
  refine ⟨addNSMul zero_le_one (δ/2), addNSMul_zero zero_le_one,
    monotone_addNSMul zero_le_one (half_pos δ_pos).le,
    addNSMul_eq_right zero_le_one (half_pos δ_pos), fun n m ↦ ?_⟩
  obtain ⟨i, hsub⟩ := ball_subset
    (addNSMul zero_le_one (δ / 2) n, addNSMul zero_le_one (δ / 2) m) trivial
  exact ⟨i, fun t ht ↦ hsub <| mem_ball_addNSMul_prod_of_mem_Icc δ_pos n m ht.1 ht.2⟩

/-- Finite-`Fin` partition variant: Any open cover of `[a, b]` can be refined to a monotone
partition indexed by `Fin (n + 1)`. -/
lemma exists_monotone_partition_Icc {ι} {a b : ℝ} (h : a ≤ b) {c : ι → Set (Icc a b)}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Icc a b),
      Monotone t ∧ t 0 = a ∧ t (Fin.last n) = b ∧
      ∀ i : Fin n, ∃ j : ι, Icc (t i.castSucc) (t i.succ) ⊆ c j := by
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc h hc₁ hc₂
  refine ⟨N, fun k ↦ t (k : ℕ), fun _ _ hij ↦ ht_mono hij, ?_, ?_, fun i ↦ ?_⟩
  · simpa using ht0
  · simpa using hN N le_rfl
  · obtain ⟨j, hj⟩ := ht_cover i
    exact ⟨j, by simpa [Fin.val_succ, Fin.val_castSucc] using hj⟩

/-- Finite-`Fin` partition variant for the unit interval. -/
lemma exists_monotone_partition_unitInterval {ι} {c : ι → Set I}
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : univ ⊆ ⋃ i, c i) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ∃ j : ι, Icc (t i.castSucc) (t i.succ) ⊆ c j := by
  obtain ⟨N, t, ht_mono, ht0, htN, ht_cover⟩ :=
    exists_monotone_partition_Icc zero_le_one hc₁ hc₂
  exact ⟨N, t, ht_mono, Subtype.ext ht0, Subtype.ext htN, ht_cover⟩

end partition

@[simp]
theorem projIcc_eq_zero {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 0 ↔ x ≤ 0 :=
  projIcc_eq_left zero_lt_one

@[simp]
theorem projIcc_eq_one {x : ℝ} : projIcc (0 : ℝ) 1 zero_le_one x = 1 ↔ 1 ≤ x :=
  projIcc_eq_right zero_lt_one

namespace Tactic.Interactive

/-- A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`. -/
macro "unit_interval" : tactic =>
  `(tactic| (first
  | apply unitInterval.nonneg
  | apply unitInterval.one_minus_nonneg
  | apply unitInterval.le_one
  | apply unitInterval.one_minus_le_one))

example (x : unitInterval) : 0 ≤ (x : ℝ) := by unit_interval

end Tactic.Interactive

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

-- We only need the ordering on `𝕜` here to avoid talking about flipping the interval over.
-- At the end of the day I only care about `ℝ`, so I'm hesitant to put work into generalizing.
/-- The image of `[0,1]` under the homeomorphism `fun x ↦ a * x + b` is `[b, a+b]`.
-/
theorem affineHomeomorph_image_I (a b : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne.symm '' Set.Icc 0 1 = Set.Icc b (a + b) := by simp [h]

/-- The affine homeomorphism from a nontrivial interval `[a,b]` to `[0,1]`.
-/
def iccHomeoI (a b : 𝕜) (h : a < b) : Set.Icc a b ≃ₜ Set.Icc (0 : 𝕜) (1 : 𝕜) := by
  let e := Homeomorph.image (affineHomeomorph (b - a) a (sub_pos.mpr h).ne.symm) (Set.Icc 0 1)
  refine (e.trans ?_).symm
  apply Homeomorph.setCongr
  rw [affineHomeomorph_image_I _ _ (sub_pos.2 h)]
  simp

@[simp]
theorem iccHomeoI_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc a b) :
    ((iccHomeoI a b h) x : 𝕜) = (x - a) / (b - a) :=
  rfl

@[simp]
theorem iccHomeoI_symm_apply_coe (a b : 𝕜) (h : a < b) (x : Set.Icc (0 : 𝕜) (1 : 𝕜)) :
    ((iccHomeoI a b h).symm x : 𝕜) = (b - a) * x + a :=
  rfl

end

namespace unitInterval

open NNReal

/-- The coercion from `I` to `ℝ≥0`. -/
def toNNReal : I → ℝ≥0 := fun i ↦ ⟨i.1, i.2.1⟩

@[simp] lemma toNNReal_zero : toNNReal 0 = 0 := rfl

@[simp] lemma toNNReal_one : toNNReal 1 = 1 := rfl

@[fun_prop] lemma toNNReal_continuous : Continuous toNNReal := by delta toNNReal; fun_prop

@[simp] lemma coe_toNNReal (x : I) : ((toNNReal x) : ℝ) = x := rfl

@[simp] lemma toNNReal_add_toNNReal_symm (x : I) : toNNReal x + toNNReal (σ x) = 1 := by ext; simp
@[simp] lemma toNNReal_symm_add_toNNReal (x : I) : toNNReal (σ x) + toNNReal x = 1 := by ext; simp

end unitInterval
