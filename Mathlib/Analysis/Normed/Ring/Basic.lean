/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Subgroup
import Mathlib.Analysis.Normed.Group.Submodule

/-!
# Normed rings

In this file we define (semi)normed rings. We also prove some theorems about these definitions.

A normed ring instance can be constructed from a given real absolute value on a ring via
`AbsoluteValue.toNormedRing`.
-/

-- Guard against import creep.
assert_not_exists AddChar comap_norm_atTop DilationEquiv Finset.sup_mul_le_mul_sup_of_nonneg
  IsOfFinOrder Isometry.norm_map_of_map_one NNReal.isOpen_Ico_zero Rat.norm_cast_real
  RestrictScalars

variable {G α β ι : Type*}

open Filter
open scoped Topology NNReal

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[NonUnitalRing α] [SeminormedRing α]` instead."
  (since := "2025-04-14")]
structure NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  protected norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SeminormedRing (α : Type*) [NonUnitalRing α] extends Norm α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[NonUnitalRing α] [NormedRing α]` instead."
  (since := "2025-04-14")]
structure NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedRing (α : Type*) [NonUnitalRing α] extends Norm α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul_le : ∀ a b, norm (a * b) ≤ norm a * norm b

-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSeminormedRing [NonUnitalRing α] [β : NormedRing α] :
    SeminormedRing α :=
  { β with }

set_option linter.deprecated false in
/-- A non-unital seminormed commutative ring is a non-unital commutative ring endowed with a
seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[NonUnitalCommRing α] [SeminormedRing α]` instead."
  (since := "2025-04-14")]
structure NonUnitalSeminormedCommRing (α : Type*)
    extends NonUnitalSeminormedRing α, NonUnitalCommRing α where

set_option linter.deprecated false in
/-- A non-unital normed commutative ring is a non-unital commutative ring endowed with a
norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[NonUnitalCommRing α] [NormedRing α]` instead."
  (since := "2025-04-14")]
structure NonUnitalNormedCommRing (α : Type*) extends
    NonUnitalNormedRing α, NonUnitalCommRing α where

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[CommRing α] [SeminormedRing α]` instead."
  (since := "2025-04-14")]
structure SeminormedCommRing (α : Type*) extends CommRing α, SeminormedRing α where

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
@[deprecated "Use `[CommRing α] [NormedRing α]` instead."
  (since := "2025-04-14")]
structure NormedCommRing (α : Type*) extends CommRing α, NormedRing α where

instance PUnit.normedRing : NormedRing PUnit :=
  { PUnit.normedAddGroup with
    norm_mul_le _ _ := by simp }

section NormOneClass

/-- A mixin class with the axiom `‖1‖ = 1`. Many `NormedRing`s and all `NormedField`s satisfy this
axiom. -/
class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

section SeminormedAddCommGroup
variable [AddCommGroup G] [SeminormedAddGroup G] [One G] [NormOneClass G]

@[simp] lemma nnnorm_one : ‖(1 : G)‖₊ = 1 := NNReal.eq norm_one
@[simp] lemma enorm_one : ‖(1 : G)‖ₑ = 1 := by simp [enorm]

theorem NormOneClass.nontrivial : Nontrivial G :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp

end SeminormedAddCommGroup

end NormOneClass

-- see Note [lower instance priority]
instance (priority := 100) NormedRing.toNormedAddGroup [NonUnitalRing α] [NormedRing α] :
    NormedAddGroup α :=
  { ‹NormedRing α› with }

-- see Note [lower instance priority]
instance (priority := 100) SeminormedRing.toSeminormedAddGroup
    [NonUnitalRing α] [SeminormedRing α] : SeminormedAddGroup α :=
  { ‹SeminormedRing α› with }

instance ULift.normOneClass [AddCommGroup α] [SeminormedAddGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

instance Prod.normOneClass [AddCommGroup α] [SeminormedAddGroup α] [One α] [NormOneClass α]
    [AddCommGroup β] [SeminormedAddGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩

instance Pi.normOneClass {ι : Type*} {α : ι → Type*} [Nonempty ι] [Fintype ι]
    [∀ i, AddCommGroup (α i)] [∀ i, SeminormedAddGroup (α i)]
    [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

instance MulOpposite.normOneClass [AddCommGroup α] [SeminormedAddGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalRing α] [SeminormedRing α] {a a₁ a₂ b c : α}

/-- The norm is submultiplicative. -/
theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  SeminormedRing.norm_mul_le a b

theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := norm_mul_le a b

lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
  (norm_mul_le ..).trans <| mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

lemma nnnorm_mul_le_of_le {r₁ r₂ : ℝ≥0} (h₁ : ‖a₁‖₊ ≤ r₁) (h₂ : ‖a₂‖₊ ≤ r₂) :
    ‖a₁ * a₂‖₊ ≤ r₁ * r₂ := (nnnorm_mul_le ..).trans <| mul_le_mul' h₁ h₂

lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl

lemma nnnorm_mul₃_le : ‖a * b * c‖₊ ≤ ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
  nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

theorem one_le_norm_one (β) [Ring β] [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

theorem one_le_nnnorm_one (β) [Ring β] [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
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
instance NonUnitalSubalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalRing E] [SeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    SeminormedRing s :=
  { s.toSubmodule.seminormedAddGroup, s.toNonUnitalRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital seminormed ring is also a non-unital seminormed ring,
with the restriction of the norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) NonUnitalSubalgebraClass.seminormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalRing E] [SeminormedRing E]
    [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    SeminormedRing s :=
  { AddSubgroupClass.seminormedAddGroup s, NonUnitalSubringClass.toNonUnitalRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring, with the
restriction of the norm. -/
instance NonUnitalSubalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalRing E] [NormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A non-unital subalgebra of a non-unital normed ring is also a non-unital normed ring,
with the restriction of the norm. -/
instance (priority := 75) NonUnitalSubalgebraClass.normedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalRing E] [NormedRing E]
    [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.seminormedAddGroup with
    norm_mul_le x y := norm_mul_le x.down y.down }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.seminormedRing [NonUnitalRing β] [SeminormedRing β] :
    SeminormedRing (α × β) :=
  { seminormedAddGroup with
    norm_mul_le x y := calc
      ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
      _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
      _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
        (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
      _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
      _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
        apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
      _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
      _ = ‖x‖ * ‖y‖ := rfl }

instance MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where
  __ := instSeminormedAddGroup
  norm_mul_le := MulOpposite.rec' fun x ↦ MulOpposite.rec' fun y ↦
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [Ring α] [SeminormedRing α] {a b c : α}

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [Ring E] [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddGroup, s.toRing with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the
norm. -/
-- necessary to require `SMulMemClass S 𝕜 E` so that `𝕜` can be determined as an `outParam`
@[nolint unusedArguments]
instance (priority := 75) SubalgebraClass.seminormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [Ring E] [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : SeminormedRing s :=
  { AddSubgroupClass.seminormedAddGroup s, SubringClass.toRing s with
    norm_mul_le a b := norm_mul_le a.1 b.1 }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm. -/
instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [Ring E] [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the
norm. -/
instance (priority := 75) SubalgebraClass.normedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [Ring E] [NormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }


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

theorem Finset.norm_prod_le' {α : Type*} [CommRing α] [NormedRing α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' this

theorem Finset.nnnorm_prod_le' {α : Type*} [CommRing α] [NormedRing α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α) :
    ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]

theorem Finset.norm_prod_le {α : Type*} [CommRing α] [NormedRing α] [NormOneClass α]
    (s : Finset ι) (f : ι → α) :
    ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type*} [CommRing α] [NormedRing α] [NormOneClass α]
    (s : Finset ι) (f : ι → α) :
    ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]

/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' a n.succ_pos) _)

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
def RingHom.IsBounded {α : Type*} [Ring α] [SeminormedRing α]
    {β : Type*} [Ring β] [SeminormedRing β]
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalRing α] [NormedRing α]

instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddGroup with }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.normedRing [NonUnitalRing β] [NormedRing β] : NormedRing (α × β) :=
  { Prod.seminormedRing, Prod.normedAddGroup with }

instance MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNormedAddGroup

end NonUnitalNormedRing

section NormedRing

variable [Ring α] [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)

theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos

end NormedRing

section NormedCommRing

variable [CommRing α] [NormedRing α]

/-- The restriction of a power-multiplicative function to a subalgebra is power-multiplicative. -/
theorem IsPowMul.restriction {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    (A : Subalgebra R S) {f : S → ℝ} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa [SubsemiringClass.coe_pow] using hf_pm (↑x) hn

end NormedCommRing

instance Real.normedRing : NormedRing ℝ :=
  { Real.normedAddGroup with norm_mul_le x y := (abs_mul x y).le }

namespace NNReal

open NNReal

theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]

@[simp] lemma nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x := by ext; simp [nnnorm]
@[simp] lemma enorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ₑ = x := by simp [enorm]

end NNReal

/-- A restatement of `MetricSpace.tendsto_atTop` in terms of the norm. -/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {β : Type*} [AddGroup β] [SeminormedAddGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/-- A variant of `NormedAddCommGroup.tendsto_atTop` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    [NoMaxOrder α] {β : Type*} [AddGroup β] [SeminormedAddGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

section RingHomIsometric

variable {R₁ R₂ : Type*}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  is_iso : ∀ {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.is_iso

variable [Ring R₁] [SeminormedRing R₁]

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

variable [AddCommGroup α] [SeminormedAddGroup α] [Mul α] [NormMulClass α] (a b : α)

@[simp] lemma nnnorm_mul : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ := NNReal.eq <| norm_mul a b

@[simp] lemma enorm_mul : ‖a * b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by simp [enorm]

end SeminormedAddCommGroup

section SeminormedRing

variable [Ring α] [SeminormedRing α] [NormOneClass α] [NormMulClass α]

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

variable [CommRing α] [SeminormedRing α] [NormMulClass α] [NormOneClass α]

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖ = ∏ b ∈ s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖₊ = ∏ b ∈ s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end SeminormedCommRing

section NormedAddCommGroup
variable [AddGroup α] [NormedAddGroup α] [MulOneClass α] [NormMulClass α] [Nontrivial α]

/-- Deduce `NormOneClass` from `NormMulClass` under a suitable nontriviality hypothesis. Not
an instance, in order to avoid loops with `NormOneClass.nontrivial`. -/
lemma NormMulClass.toNormOneClass : NormOneClass α where
  norm_one := by
    obtain ⟨u, hu⟩ := exists_ne (0 : α)
    simpa [mul_eq_left₀ (norm_ne_zero_iff.mpr hu)] using (norm_mul u 1).symm

end NormedAddCommGroup

section NormedRing
variable [Ring α] [NormedRing α] [NormMulClass α]

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

/-- A non-unital ring homomorphism from a `NonUnitalRing` to a non-unital `SeminormedRing`
induces a `SeminormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev SeminormedRing.induced [NonUnitalRing R] [NonUnitalRing S] [SeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : SeminormedRing R :=
  { SeminormedAddGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul_le x y := show ‖f _‖ ≤ _ from (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

/-- An injective non-unital ring homomorphism from a `NonUnitalRing` to a non-unital
`NonUnitalNormedRing` induces a `NonUnitalNormedRing` structure on the domain.

See note [reducible non-instances] -/
abbrev NormedRing.induced [NonUnitalRing R] [NonUnitalRing S] [NormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedRing R :=
  { SeminormedRing.induced R S f, NormedAddGroup.induced R S f hf with }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [Ring S] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

/-- A ring homomorphism from a `Ring R` to a `SeminormedRing S` which induces the norm structure
`SeminormedRing.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormMulClass.induced {F : Type*} (R S : Type*) [Ring R] [Ring S] [SeminormedRing S]
    [NormMulClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormMulClass R (SeminormedRing.induced R S f).toNorm _ :=
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_mul x y := (congr_arg norm (map_mul f x y)).trans <| norm_mul _ _ }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

instance toSeminormedRing [Ring R] [SeminormedRing R] [SubringClass S R] (s : S) :
    SeminormedRing s :=
  SeminormedRing.induced s R (SubringClass.subtype s)

instance toNormedRing [Ring R] [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

instance toNormOneClass [Ring R] [SeminormedRing R] [NormOneClass R] [SubringClass S R] (s : S) :
    NormOneClass s :=
  .induced s R <| SubringClass.subtype _

instance toNormMulClass [Ring R] [SeminormedRing R] [NormMulClass R] [SubringClass S R] (s : S) :
    NormMulClass s :=
  .induced s R <| SubringClass.subtype _

end SubringClass

namespace AbsoluteValue

/-- A real absolute value on a ring determines a `NormedRing` structure. -/
noncomputable def toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing R where
  norm := v
  dist x y := v (x - y)
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul_le x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

end AbsoluteValue
