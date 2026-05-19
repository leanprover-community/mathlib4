/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Submodule

import Mathlib.Data.Fintype.Order

/-!
# Normed rings

In this file we define (semi)normed rings. We also prove some theorems about these definitions.

A normed ring instance can be constructed from a given real absolute value on a ring via
`AbsoluteValue.toNormedRing`.
-/

@[expose] public section

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class IsNormedRing (α : Type*) [NormPseudoMetric α] [NonUnitalRing α] extends
    IsNormedAddGroup α where
  /-- The norm is submultiplicative. -/
  protected norm_mul_le : ∀ a b : α, norm (a * b) ≤ norm a * norm b

/-- missing doc -/
@[class_abbrev]
structure NonUnitalSeminormedRing (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toNonUnitalRing : NonUnitalRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NonUnitalSeminormedRing.mk

/-- missing doc -/
@[class_abbrev]
structure SeminormedRing (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toRing : Ring E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] SeminormedRing.mk

/-- missing doc -/
@[class_abbrev]
structure NonUnitalNormedRing (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toNonUnitalRing : NonUnitalRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NonUnitalNormedRing.mk

/-- missing doc -/
@[class_abbrev]
structure NormedRing (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toRing : Ring E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NormedRing.mk

/-- missing doc -/
@[class_abbrev]
structure NonUnitalSeminormedCommRing (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toNonUnitalCommRing : NonUnitalCommRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NonUnitalSeminormedCommRing.mk

/-- missing doc -/
@[class_abbrev]
structure NonUnitalNormedCommRing (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toNonUnitalCommRing : NonUnitalCommRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NonUnitalNormedCommRing.mk

/-- missing doc -/
@[class_abbrev]
structure SeminormedCommRing (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toCommRing : CommRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] SeminormedCommRing.mk

/-- missing doc -/
@[class_abbrev]
structure NormedCommRing (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toCommRing : CommRing E]
  [toIsNormedRing : IsNormedRing E]

attribute [instance] NormedCommRing.mk

instance PUnit.instIsNormedRing : IsNormedRing PUnit where
  norm_mul_le _ _ := by simp

section NormOneClass

/-- A mixin class with the axiom `‖1‖ = 1`. Many `NormedRing`s and all `NormedField`s satisfy this
axiom. -/
class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

section SeminormedAddCommGroup
variable [SeminormedAddCommGroup G] [One G] [NormOneClass G]

@[simp] lemma nnnorm_one : ‖(1 : G)‖₊ = 1 := NNReal.eq norm_one
@[simp] lemma enorm_one : ‖(1 : G)‖ₑ = 1 := by simp [enorm]

theorem NormOneClass.nontrivial : Nontrivial G :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp

end SeminormedAddCommGroup

end NormOneClass

instance ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩

instance Pi.normOneClass {ι : Type*} {α : ι → Type*} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α] {a a₁ a₂ b c : α}

/-- The norm is submultiplicative. -/
theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  IsNormedRing.norm_mul_le a b

theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := norm_mul_le a b

lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
  (norm_mul_le ..).trans <| mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

lemma nnnorm_mul_le_of_le {r₁ r₂ : ℝ≥0} (h₁ : ‖a₁‖₊ ≤ r₁) (h₂ : ‖a₂‖₊ ≤ r₂) :
    ‖a₁ * a₂‖₊ ≤ r₁ * r₂ := (nnnorm_mul_le ..).trans <| mul_le_mul' h₁ h₂

lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl

lemma nnnorm_mul₃_le : ‖a * b * c‖₊ ≤ ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
  nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β

/-- In a seminormed ring, the left-multiplication `AddMonoidHom` is bounded. -/
theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x

/-- In a seminormed ring, the right-multiplication `AddMonoidHom` is bounded. -/
theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
instance NonUnitalSubalgebra.instIsNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    IsNormedRing s where
  norm_mul_le a b := norm_mul_le a.1 b.1

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) NonUnitalSubalgebraClass.instIsNormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalSeminormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    IsNormedRing s where
  norm_mul_le a b := norm_mul_le a.1 b.1

instance ULift.instIsNormedRing : IsNormedRing (ULift α) where
  norm_mul_le x y := norm_mul_le x.down y.down

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.instIsNormedRing [NonUnitalSeminormedRing β] :
    IsNormedRing (α × β) where
  norm_mul_le x y := calc
    ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
    _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
    _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
      (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
    _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
    _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
      apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
    _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
    _ = ‖x‖ * ‖y‖ := rfl

instance MulOpposite.instIsNormedRing : IsNormedRing αᵐᵒᵖ where
  norm_mul_le := MulOpposite.rec' fun x ↦ MulOpposite.rec' fun y ↦
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α] {a b c : α}

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
instance Subalgebra.instIsNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : IsNormedRing s :=
  inferInstance

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
theorem SubalgebraClass.instIsNormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : IsNormedRing s :=
  inferInstance


theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.prod‖ ≤ (l.map norm).prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, List.prod_cons (a := ‖a‖)]
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.prod‖ ≤ (l.map norm).prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)

theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' this

theorem Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]

theorem Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]

lemma norm_natAbs (z : ℤ) :
    ‖(z.natAbs : α)‖ = ‖(z : α)‖ := by
  rcases z.natAbs_eq with hz | hz
  · rw [← Int.cast_natCast, ← hz]
  · rw [← Int.cast_natCast, ← norm_neg, ← Int.cast_neg, ← hz]

lemma nnnorm_natAbs (z : ℤ) :
    ‖(z.natAbs : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← NNReal.coe_inj, -Nat.cast_natAbs, norm_natAbs]

@[simp] lemma norm_intCast_abs (z : ℤ) :
    ‖((|z| : ℤ) : α)‖ = ‖(z : α)‖ := by
  simp [← norm_natAbs]

@[simp] lemma nnnorm_intCast_abs (z : ℤ) :
    ‖((|z| : ℤ) : α)‖₊ = ‖(z : α)‖₊ := by
  simp [← nnnorm_natAbs]

/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_right (nnnorm_pow_le' a n.succ_pos) _)

/-- If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`. -/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp only [pow_zero, nnnorm_one, le_rfl])
    fun k _hk => nnnorm_pow_le' a k.succ_pos

/-- If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

/-- If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`.
See also `norm_pow_le'`. -/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp only [pow_zero, norm_one, le_rfl])
    fun n _hn => norm_pow_le' a n.succ_pos

theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
lemma norm_sub_mul_le (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ :=
  calc
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
lemma norm_sub_mul_le' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ := by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
lemma nnnorm_sub_mul_le (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ := norm_sub_mul_le ha

/-- This inequality is particularly useful when `c = 1` and `‖a‖ = ‖b‖ = 1` as it then shows that
chord length is a metric on the unit complex numbers. -/
lemma nnnorm_sub_mul_le' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ := norm_sub_mul_le' hb

lemma norm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ ≤ 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ :=
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ ≤ ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ ≤ (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ ≤ (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring

lemma nnnorm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖₊ ≤ 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.val - 1‖₊ * ‖b.val - 1‖₊ := by
  simpa using norm_commutator_units_sub_one_le a b

/-- A homomorphism `f` between semi_normed_rings is bounded if there exists a positive
  constant `C` such that for all `x` in `α`, `norm (f x) ≤ C * norm x`. -/
def RingHom.IsBounded {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRing β]
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

end SeminormedRing

section NormedRing

variable [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)

theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos

end NormedRing

section NormedCommRing

/-- A subalgebra of a seminormed commutative ring is also a seminormed commutative ring, with the
restriction of the norm. -/
instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : IsNormedRing s :=
  inferInstance

/-- A subalgebra of a normed commutative ring is also a normed commutative ring, with the
restriction of the norm. -/
instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : IsNormedRing s :=
  inferInstance

/-- The restriction of a power-multiplicative function to a subalgebra is power-multiplicative. -/
theorem IsPowMul.restriction {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (A : Subalgebra R S) {f : S → ℝ} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa using hf_pm (↑x) hn

end NormedCommRing

instance Real.instIsNormedRing : IsNormedRing ℝ where
  norm_mul_le x y := (abs_mul x y).le

namespace NNReal

open NNReal

theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]

@[simp] lemma nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x := by ext; simp [nnnorm]
@[simp] lemma enorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ₑ = x := by simp [enorm]

end NNReal

/-- A restatement of `MetricSpace.tendsto_atTop` in terms of the norm. -/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/-- A variant of `NormedAddCommGroup.tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    [NoMaxOrder α] {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

section RingHomIsometric

variable {R₁ R₂ : Type*}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  norm_map : ∀ {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.norm_map

@[simp]
theorem RingHomIsometric.nnnorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ →+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖₊ = ‖x‖₊ :=
  NNReal.eq norm_map

@[simp]
theorem RingHomIsometric.enorm_map [SeminormedRing R₁] [SeminormedRing R₂] (σ : R₁ →+* R₂)
    [RingHomIsometric σ] (x : R₁) : ‖σ x‖ₑ = ‖x‖ₑ :=
  congrArg ENNReal.ofNNReal <| nnnorm_map σ x

variable [SeminormedRing R₁]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨rfl⟩

end RingHomIsometric

section NormMulClass

/-- A mixin class for strict multiplicativity of the norm, `‖a * b‖ = ‖a‖ * ‖b‖` (rather than
`≤` as in the definition of `NormedRing`). Many `NormedRing`s satisfy this stronger property,
including all `NormedDivisionRing`s and `NormedField`s. -/
class NormMulClass (α : Type*) [Norm α] [Mul α] : Prop where
  /-- The norm is multiplicative. -/
  protected norm_mul : ∀ (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖

@[simp] lemma norm_mul [Norm α] [Mul α] [NormMulClass α] (a b : α) :
    ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormMulClass.norm_mul a b

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [Mul α] [NormMulClass α] (a b : α)

@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq <| norm_mul a b

@[simp] lemma enorm_mul : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by simp [enorm]

end SeminormedAddCommGroup

section SeminormedRing

variable [SeminormedRing α] [NormOneClass α] [NormMulClass α]

/-- `norm` as a `MonoidWithZeroHom`. -/
@[simps]
def normHom : α →*₀ ℝ where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

/-- `nnnorm` as a `MonoidWithZeroHom`. -/
@[simps]
def nnnormHom : α →*₀ ℝ≥0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n

@[simp] lemma enorm_pow (a : α) (n : ℕ) : ‖a ^ n‖ₑ = ‖a‖ₑ ^ n := by simp [enorm]

protected theorem List.norm_prod (l : List α) : ‖l.prod‖ = (l.map norm).prod :=
  map_list_prod (normHom.toMonoidHom : α →* ℝ) _

protected theorem List.nnnorm_prod (l : List α) : ‖l.prod‖₊ = (l.map nnnorm).prod :=
  map_list_prod (nnnormHom.toMonoidHom : α →* ℝ≥0) _

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing α] [NormMulClass α] [NormOneClass α]

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖ = ∏ b ∈ s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖₊ = ∏ b ∈ s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end SeminormedCommRing

section NormedAddCommGroup
variable [NormedAddCommGroup α] [MulOneClass α] [NormMulClass α] [Nontrivial α]

/-- Deduce `NormOneClass` from `NormMulClass` under a suitable nontriviality hypothesis. Not
an instance, in order to avoid loops with `NormOneClass.nontrivial`. -/
lemma NormMulClass.toNormOneClass : NormOneClass α where
  norm_one := by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

end NormedAddCommGroup

section NormedRing
variable [NormedRing α] [NormMulClass α]

instance NormMulClass.isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

instance NormMulClass.toNoZeroDivisors : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero h := by
    simpa only [← norm_eq_zero (E := α), norm_mul, mul_eq_zero] using h

end NormedRing

end NormMulClass

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*) [FunLike F R S]

abbrev IsNormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) :
    letI := NormPseudoMetric.induced R S f
    IsNormedRing R :=
  letI := NormPseudoMetric.induced R S f
  { toIsNormedAddGroup := .induced R S f
    norm_mul_le x y := show ‖f _‖ ≤ _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    letI := NormPseudoMetric.induced R S f
    NormOneClass R :=
  letI := NormPseudoMetric.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormMulClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    letI := NormPseudoMetric.induced R S f
    NormMulClass R :=
  letI := NormPseudoMetric.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

instance toIsNormedRing [SeminormedRing R] [SubringClass S R] (s : S) : IsNormedRing s :=
  .induced s R (SubringClass.subtype s)

instance toNormOneClass [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s : S) :
    NormOneClass s :=
  .induced s R <| SubringClass.subtype _

instance toNormMulClass [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s : S) :
    NormMulClass s :=
  .induced s R <| SubringClass.subtype _

end SubringClass

namespace AbsoluteValue

/-- missing doc -/
@[implicit_reducible]
def toNormMetric {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormMetric R where
  norm := v
  dist x y := v (-x + y)
  dist_self x := by simp
  dist_comm x y := by rw [add_comm (-x), add_comm (-y), ← sub_eq_add_neg, v.map_sub, sub_eq_add_neg]
  dist_triangle x y z := by simpa [neg_add_eq_sub, add_comm (v (y - x))] using v.sub_le z y x
  edist_dist x y := rfl
  eq_of_dist_eq_zero := by
    intro x y hxy
    rw [add_comm, ← sub_eq_add_neg, AbsoluteValue.map_sub_eq_zero_iff] at hxy
    exact hxy.symm

/-- A real absolute value on a ring determines a `NormedRing` structure. -/
@[implicit_reducible]
noncomputable def toIsNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) :
    letI := v.toNormMetric
    IsNormedRing R :=
  letI := v.toNormMetric
  { dist_eq _ _ := rfl
    norm_mul_le x y := (v.map_mul x y).le }

end AbsoluteValue

namespace Real

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section mul

variable {R ι ι' : Type*} [Semiring R] [Finite ι] [Finite ι']

lemma iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg {F : Type*} [FunLike F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] (v : F) (x : ι → R) (y : ι' → R) :
    ⨆ a : ι × ι', v (x a.1 * y a.2) = (⨆ i, v (x i)) * ⨆ j, v (y j) := by
  rcases isEmpty_or_nonempty ι
  · simp
  rcases isEmpty_or_nonempty ι'
  · simp
  simp_rw [Real.iSup_mul_of_nonneg (iSup_nonneg fun i ↦ apply_nonneg v (y i)),
    Real.mul_iSup_of_nonneg (apply_nonneg v _), map_mul, Finite.ciSup_prod]

end mul

/-
Note: We cannot easily generalize this to targets other than `ℝ`, because we need
the fact that `⨆ i, f i = 0` when the indexing type is empty (`Real.iSup_of_isEmpty`).
-/

section prod

universe u v

variable {α R : Type*} [Fintype α] {ι : α → Type u} [∀ a, Finite (ι a)]

lemma iSup_prod_eq_prod_iSup_of_nonneg {f : (a : α) → ι a → ℝ} (hf₀ : ∀ a i, 0 ≤ f a i) :
    ⨆ (i : (a : α) → ι a), ∏ a, f a (i a) = ∏ a, ⨆ i, f a i := by
  rcases isEmpty_or_nonempty ((a : α) → ι a) with h | h
  · rw [iSup_of_isEmpty, eq_comm, Finset.prod_eq_zero_iff]
    obtain ⟨a, ha⟩ := isEmpty_pi.mp h
    exact ⟨a, by simp⟩
  refine le_antisymm ?_ ?_
  · exact ciSup_le fun i ↦ Finset.prod_le_prod (by simp [hf₀])
      fun a ha ↦ Finite.le_ciSup_of_le _ le_rfl
  · rw [Classical.nonempty_pi] at h
    have H a : ∃ i : ι a, f a i = ⨆ i, f a i := exists_eq_ciSup_of_finite
    choose i hi using H
    simp only [← hi]
    exact Finite.le_ciSup_of_le i le_rfl

lemma iSup_prod_eq_prod_iSup_of_nonnegHomClass {F : Type*} [FunLike F R ℝ]
    [NonnegHomClass F R ℝ] (v : F) {x : (a : α) → ι a → R} :
    ⨆ (i : (a : α) → ι a), ∏ a, v (x a (i a)) = ∏ a, ⨆ i, v (x a i) :=
  Real.iSup_prod_eq_prod_iSup_of_nonneg (f := fun a i ↦ v (x a i)) (fun _ _ ↦ apply_nonneg v _)

end prod

end Real
