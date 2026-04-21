/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Floor
public import Mathlib.Data.Real.Pointwise
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Data.Nat.Lattice

/-!
# Basic results on nonnegative real numbers

This file contains all results on `NNReal` that do not directly follow from its basic structure.
As a consequence, it is a bit of a random collection of results, and is a good target for cleanup.

## Notation

This file uses `ℝ≥0` as a localized notation for `NNReal`.
-/
set_option backward.defeqAttrib.useBackward true

public section

assert_not_exists TrivialStar

open Function Set
open scoped BigOperators

namespace NNReal

noncomputable instance : FloorSemiring ℝ≥0 := inferInstanceAs <| FloorSemiring (Subtype _)

@[simp, norm_cast]
theorem coe_mulIndicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.mulIndicator f a : ℝ≥0) : ℝ) = s.mulIndicator (fun x => ↑(f x)) a :=
  map_mulIndicator toRealHom _ _ _

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator toRealHom _ _ _

@[simp, norm_cast]
theorem coe_mulSingle {α} [DecidableEq α] (a : α) (b : ℝ≥0) (c : α) :
    ((Pi.mulSingle a b : α → ℝ≥0) c : ℝ) = (Pi.mulSingle a b : α → ℝ) c := by
  simpa using coe_mulIndicator {a} (fun _ ↦ b) c

@[simp, norm_cast]
theorem coe_single {α} [DecidableEq α] (a : α) (b : ℝ≥0) (c : α) :
    ((Pi.single a b : α → ℝ≥0) c : ℝ) = (Pi.single a b : α → ℝ) c := by
  simpa using coe_indicator {a} (fun _ ↦ b) c

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.sum : ℝ≥0) : ℝ) = (l.map (↑)).sum :=
  map_list_sum toRealHom l

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.prod : ℝ≥0) : ℝ) = (l.map (↑)).prod :=
  map_list_prod toRealHom l

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.sum : ℝ≥0) : ℝ) = (s.map (↑)).sum :=
  map_multiset_sum toRealHom s

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.prod : ℝ≥0) : ℝ) = (s.map (↑)).prod :=
  map_multiset_prod toRealHom s

variable {ι : Type*} {s : Finset ι} {f : ι → ℝ}

@[simp, norm_cast]
theorem coe_sum (s : Finset ι) (f : ι → ℝ≥0) : ∑ i ∈ s, f i = ∑ i ∈ s, (f i : ℝ) :=
  map_sum toRealHom _ _

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → ℝ≥0) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℝ) :=
  map_expect toRealHom ..

theorem _root_.Real.toNNReal_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]
theorem coe_prod (s : Finset ι) (f : ι → ℝ≥0) : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ) :=
  map_prod toRealHom _ _

theorem _root_.Real.toNNReal_prod_of_nonneg (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a ∈ s, f a) = ∏ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

theorem le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_iInf, coe_iInf]
  exact le_ciInf_add_ciInf h

theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)

theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)

theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]

section Set

@[simp] lemma bddAbove_natCast_image_iff {s : Set ℕ} : BddAbove ((↑) '' s : Set ℝ≥0) ↔ BddAbove s :=
  ⟨.imp' Nat.floor (by simp [upperBounds, Nat.le_floor_iff]), .imp' (↑) (by simp [upperBounds])⟩

@[simp, norm_cast] lemma bddAbove_range_natCast_iff {ι : Sort*} (f : ι → ℕ) :
    BddAbove (Set.range (f ·) : Set NNReal) ↔ BddAbove (Set.range f) := by
  rw [← bddAbove_natCast_image_iff, ← Set.range_comp]
  rfl

end Set

open Real

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSub` in the file
`Mathlib/Algebra/Order/Sub/Basic.lean`. See also `mul_tsub` and `tsub_mul`.
-/

theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _

/-- This lemma is needed for the `norm_cast` simp set. Outside of this use case `Nat.coe_sub`
should be used. -/
@[norm_cast]
protected theorem coe_sub_of_lt {a b : ℝ≥0} (h : a < b) :
    ((b - a : ℝ≥0) : ℝ) = b - a := NNReal.coe_sub h.le

end Sub

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

theorem iInf_mul (f : ι → ℝ≥0) (a : ℝ≥0) : iInf f * a = ⨅ i, f i * a := by
  rw [← coe_inj, NNReal.coe_mul, coe_iInf, coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _

theorem mul_iInf (f : ι → ℝ≥0) (a : ℝ≥0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using iInf_mul f a

theorem mul_iSup (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← coe_inj, NNReal.coe_mul, NNReal.coe_iSup, NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _

theorem iSup_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_iSup]
  simp_rw [mul_comm]

theorem iSup_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, iSup_mul]

theorem mul_iSup_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [mul_iSup]
  exact ciSup_le' H

theorem iSup_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [iSup_mul]
  exact ciSup_le' H

theorem iSup_mul_iSup_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun _ => mul_iSup_le <| H _

variable [Nonempty ι]

theorem le_mul_iInf {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
  rw [mul_iInf]
  exact le_ciInf H

theorem le_iInf_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
  rw [iInf_mul]
  exact le_ciInf H

theorem le_iInf_mul_iInf {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ iInf g * iInf h :=
  le_iInf_mul fun i => le_mul_iInf <| H i

@[simp, norm_cast] lemma natCast_iSup {ι : Sort*} (f : ι → ℕ) :
    ⨆ i, f i = (⨆ i, f i : NNReal) := by
  by_cases h : BddAbove (Set.range f)
  · apply eq_of_forall_ge_iff
    simp [ciSup_le_iff', ← Nat.le_floor_iff, *]
  · simp [*]

@[simp, norm_cast] lemma natCast_iInf {ι : Sort*} (f : ι → ℕ) :
    ⨅ i, f i = (⨅ i, f i : NNReal) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [iInf_empty]
  apply eq_of_forall_le_iff
  simp [le_ciInf_iff, ← Nat.ceil_le]

end Csupr

section rify

@[rify_simps] lemma toReal_eq (a b : ℝ≥0) : a = b ↔ (a : ℝ) = (b : ℝ) := by simp

@[rify_simps] lemma toReal_le (a b : ℝ≥0) : a ≤ b ↔ (a : ℝ) ≤ (b : ℝ) := by simp

@[rify_simps] lemma toReal_lt (a b : ℝ≥0) : a < b ↔ (a : ℝ) < (b : ℝ) := by simp

@[rify_simps] lemma toReal_ne (a b : ℝ≥0) : a ≠ b ↔ (a : ℝ) ≠ (b : ℝ) := by simp

end rify

@[simp]
theorem range_coe : range toReal = Ici 0 := Subtype.range_coe

@[simp]
theorem image_coe_Ici (x : ℝ≥0) : toReal '' Ici x = Ici ↑x := image_subtype_val_Ici_Ici ..

@[simp]
theorem image_coe_Iic (x : ℝ≥0) : toReal '' Iic x = Icc 0 ↑x := image_subtype_val_Ici_Iic ..

@[simp]
theorem image_coe_Ioi (x : ℝ≥0) : toReal '' Ioi x = Ioi ↑x := image_subtype_val_Ici_Ioi ..

@[simp]
theorem image_coe_Iio (x : ℝ≥0) : toReal '' Iio x = Ico 0 ↑x := image_subtype_val_Ici_Iio ..

@[simp]
theorem image_coe_Icc (x y : ℝ≥0) : toReal '' Icc x y = Icc ↑x ↑y :=
  image_subtype_val_Icc (s := Ici 0) ..

@[simp]
theorem image_coe_Ioc (x y : ℝ≥0) : toReal '' Ioc x y = Ioc ↑x ↑y :=
  image_subtype_val_Ioc (s := Ici 0) ..

@[simp]
theorem image_coe_Ico (x y : ℝ≥0) : toReal '' Ico x y = Ico ↑x ↑y :=
  image_subtype_val_Ico (s := Ici 0) ..

@[simp]
theorem image_coe_Ioo (x y : ℝ≥0) : toReal '' Ioo x y = Ioo ↑x ↑y :=
  image_subtype_val_Ioo (s := Ici 0) ..

@[simp]
theorem image_coe_uIcc (x y : ℝ≥0) : toReal '' uIcc x y = uIcc ↑x ↑y :=
  image_subtype_val_uIcc (s := Ici 0) ..

@[simp]
theorem image_coe_uIoc (x y : ℝ≥0) : toReal '' uIoc x y = uIoc ↑x ↑y :=
  image_subtype_val_uIoc (s := Ici 0) ..

@[simp]
theorem image_coe_uIoo (x y : ℝ≥0) : toReal '' uIoo x y = uIoo ↑x ↑y :=
  image_subtype_val_uIoo (s := Ici 0) ..

end NNReal
