/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module analysis.normed.field.basic
! leanprover-community/mathlib commit f06058e64b7e8397234455038f3f8aec83aaba5a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Instances.Ennreal

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

open Filter Metric

open Topology BigOperators NNReal ENNReal uniformity Pointwise

/-- A non-unital seminormed ring is a not-necessarily-unital ring
endowed with a seminorm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalSemiNormedRing (α : Type _) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align non_unital_semi_normed_ring NonUnitalSemiNormedRing

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SemiNormedRing (α : Type _) extends Norm α, Ring α, PseudoMetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align semi_normed_ring SemiNormedRing

-- see Note [lower instance priority]
/-- A seminormed ring is a non-unital seminormed ring. -/
instance (priority := 100) SemiNormedRing.toNonUnitalSemiNormedRing [β : SemiNormedRing α] :
    NonUnitalSemiNormedRing α :=
  { β with }
#align semi_normed_ring.to_non_unital_semi_normed_ring SemiNormedRing.toNonUnitalSemiNormedRing

/-- A non-unital normed ring is a not-necessarily-unital ring
endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NonUnitalNormedRing (α : Type _) extends Norm α, NonUnitalRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align non_unital_normed_ring NonUnitalNormedRing

-- see Note [lower instance priority]
/-- A non-unital normed ring is a non-unital seminormed ring. -/
instance (priority := 100) NonUnitalNormedRing.toNonUnitalSemiNormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSemiNormedRing α :=
  { β with }
#align non_unital_normed_ring.to_non_unital_semi_normed_ring NonUnitalNormedRing.toNonUnitalSemiNormedRing

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedRing (α : Type _) extends Norm α, Ring α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b
#align normed_ring NormedRing

/-- A normed division ring is a division ring endowed with a seminorm which satisfies the equality
`‖x y‖ = ‖x‖ ‖y‖`. -/
class NormedDivisionRing (α : Type _) extends Norm α, DivisionRing α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b
#align normed_division_ring NormedDivisionRing

-- see Note [lower instance priority]
/-- A normed division ring is a normed ring. -/
instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul := fun a b => (NormedDivisionRing.norm_mul' a b).le }
#align normed_division_ring.to_normed_ring NormedDivisionRing.toNormedRing

-- see Note [lower instance priority]
/-- A normed ring is a seminormed ring. -/
instance (priority := 100) NormedRing.toSemiNormedRing [β : NormedRing α] : SemiNormedRing α :=
  { β with }
#align normed_ring.to_semi_normed_ring NormedRing.toSemiNormedRing

-- see Note [lower instance priority]
/-- A normed ring is a non-unital normed ring. -/
instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }
#align normed_ring.to_non_unital_normed_ring NormedRing.toNonUnitalNormedRing

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class SemiNormedCommRing (α : Type _) extends SemiNormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x
#align semi_normed_comm_ring SemiNormedCommRing

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `‖x y‖ ≤ ‖x‖ ‖y‖`. -/
class NormedCommRing (α : Type _) extends NormedRing α where
  mul_comm : ∀ x y : α, x * y = y * x
#align normed_comm_ring NormedCommRing

-- see Note [lower instance priority]
/-- A normed commutative ring is a seminormed commutative ring. -/
instance (priority := 100) NormedCommRing.toSemiNormedCommRing [β : NormedCommRing α] :
    SemiNormedCommRing α :=
  { β with }
#align normed_comm_ring.to_semi_normed_comm_ring NormedCommRing.toSemiNormedCommRing

instance : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with norm_mul := fun _ _ => by simp }

/-- A mixin class with the axiom `‖1‖ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class NormOneClass (α : Type _) [Norm α] [One α] : Prop where
  norm_one : ‖(1 : α)‖ = 1
#align norm_one_class NormOneClass

export NormOneClass (norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SeminormedAddCommGroup α] [One α] [NormOneClass α] : ‖(1 : α)‖₊ = 1 :=
  NNReal.eq norm_one
#align nnnorm_one nnnorm_one

theorem NormOneClass.nontrivial (α : Type _) [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    Nontrivial α :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp
#align norm_one_class.nontrivial NormOneClass.nontrivial

-- see Note [lower instance priority]
instance (priority := 100) SemiNormedCommRing.toCommRing [β : SemiNormedCommRing α] : CommRing α :=
  { β with }
#align semi_normed_comm_ring.to_comm_ring SemiNormedCommRing.toCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }
#align non_unital_normed_ring.to_normed_add_comm_group NonUnitalNormedRing.toNormedAddCommGroup

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSemiNormedRing.toSeminormedAddCommGroup
    [NonUnitalSemiNormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSemiNormedRing α› with }
#align non_unital_semi_normed_ring.to_seminormed_add_comm_group NonUnitalSemiNormedRing.toSeminormedAddCommGroup

instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] : NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩
#align prod.norm_one_class Prod.normOneClass

instance Pi.normOneClass {ι : Type _} {α : ι → Type _} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simp [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]⟩
#align pi.norm_one_class Pi.normOneClass

instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩
#align mul_opposite.norm_one_class MulOpposite.normOneClass

section NonUnitalSemiNormedRing

variable [NonUnitalSemiNormedRing α]

theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  NonUnitalSemiNormedRing.norm_mul _ _
#align norm_mul_le norm_mul_le

theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := by
  simpa only [← norm_toNNReal, ← Real.toNNReal_mul (norm_nonneg _)] using
    Real.toNNReal_mono (norm_mul_le _ _)
#align nnnorm_mul_le nnnorm_mul_le

theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)
#align one_le_norm_one one_le_norm_one

theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β
#align one_le_nnnorm_one one_le_nnnorm_one

theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le
#align filter.tendsto.zero_mul_is_bounded_under_le Filter.Tendsto.zero_mul_isBoundedUnder_le

theorem Filter.IsBoundedUnderLe.mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)
#align filter.is_bounded_under_le.mul_tendsto_zero Filter.IsBoundedUnderLe.mul_tendsto_zero

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x
#align mul_left_bound mulLeft_bound

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y =>
  by
  rw [mul_comm]
  convert norm_mul_le y x
#align mul_right_bound mulRight_bound

instance : NonUnitalSemiNormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup with norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

/-- Non-unital seminormed ring structure on the product of two non-unital seminormed rings,
  using the sup norm. -/
instance Prod.nonUnitalSemiNormedRing [NonUnitalSemiNormedRing β] :
    NonUnitalSemiNormedRing (α × β) :=
  { Prod.seminormedAddCommGroup with
    norm_mul := fun x y =>
      calc
        ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
        _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
        _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
          (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
        _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
        _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
          apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
        _ = ‖x‖ * ‖y‖ := rfl
         }
#align prod.non_unital_semi_normed_ring Prod.nonUnitalSemiNormedRing

/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSemiNormedRing {π : ι → Type _} [Fintype ι]
    [∀ i, NonUnitalSemiNormedRing (π i)] : NonUnitalSemiNormedRing (∀ i, π i) :=
  { Pi.seminormedAddCommGroup with
    norm_mul := fun x y =>
      NNReal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ‖x i * y i‖₊) ≤
              Finset.univ.sup ((fun i => ‖x i‖₊) * fun i => ‖y i‖₊) :=
            Finset.sup_mono_fun fun b hb => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ‖x i‖₊) * Finset.univ.sup fun i => ‖y i‖₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg _ (fun i _ => zero_le _) fun i _ => zero_le _
           }
#align pi.non_unital_semi_normed_ring Pi.nonUnitalSemiNormedRing

instance MulOpposite.nonUnitalSemiNormedRing : NonUnitalSemiNormedRing αᵐᵒᵖ :=
  { MulOpposite.seminormedAddCommGroup with
    norm_mul :=
      MulOpposite.rec' fun x =>
        MulOpposite.rec' fun y => (norm_mul_le y x).trans_eq (mul_comm _ _) }
#align mul_opposite.non_unital_semi_normed_ring MulOpposite.nonUnitalSemiNormedRing

end NonUnitalSemiNormedRing

section SemiNormedRing

variable [SemiNormedRing α]

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.semiNormedRing {𝕜 : Type _} {_ : CommRing 𝕜} {E : Type _} [SemiNormedRing E]
    {_ : Algebra 𝕜 E} (s : Subalgebra 𝕜 E) : SemiNormedRing s :=
  { s.toSubmodule.SeminormedAddCommGroup with norm_mul := fun a b => norm_mul_le a.1 b.1 }
#align subalgebra.semi_normed_ring Subalgebra.semiNormedRing

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Subalgebra.normedRing {𝕜 : Type _} {_ : CommRing 𝕜} {E : Type _} [NormedRing E]
    {_ : Algebra 𝕜 E} (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.SemiNormedRing with }
#align subalgebra.normed_ring Subalgebra.normedRing

theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl
#align nat.norm_cast_le Nat.norm_cast_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.Prod‖ ≤ (l.map norm).Prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, @List.prod_cons _ _ _ ‖a‖]
    refine' le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)
#align list.norm_prod_le' List.norm_prod_le'

theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.Prod‖₊ ≤ (l.map nnnorm).Prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
#align list.nnnorm_prod_le' List.nnnorm_prod_le'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.Prod‖ ≤ (l.map norm).Prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)
#align list.norm_prod_le List.norm_prod_le

theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.Prod‖₊ ≤ (l.map nnnorm).Prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]
#align list.nnnorm_prod_le List.nnnorm_prod_le

theorem Finset.norm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i in s, f i‖ ≤ ∏ i in s, ‖f i‖ :=
  by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' this
#align finset.norm_prod_le' Finset.norm_prod_le'

theorem Finset.nnnorm_prod_le' {α : Type _} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i in s, f i‖₊ ≤ ∏ i in s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]
#align finset.nnnorm_prod_le' Finset.nnnorm_prod_le'

theorem Finset.norm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i in s, f i‖ ≤ ∏ i in s, ‖f i‖ :=
  by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le
#align finset.norm_prod_le Finset.norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type _} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i in s, f i‖₊ ≤ ∏ i in s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]
#align finset.nnnorm_prod_le Finset.nnnorm_prod_le

/-- If `α` is a seminormed ring, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n` for `n > 0`.
See also `nnnorm_pow_le`. -/
theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, h => by simp only [pow_one]
  | n + 2, h => by
    simpa only [pow_succ _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' n.succ_pos) _)
#align nnnorm_pow_le' nnnorm_pow_le'

/-- If `α` is a seminormed ring with `‖1‖₊ = 1`, then `‖a ^ n‖₊ ≤ ‖a‖₊ ^ n`.
See also `nnnorm_pow_le'`.-/
theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp only [pow_zero, nnnorm_one]) fun k hk => nnnorm_pow_le' a k.succ_pos
#align nnnorm_pow_le nnnorm_pow_le

/-- If `α` is a seminormed ring, then `‖a ^ n‖ ≤ ‖a‖ ^ n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)
#align norm_pow_le' norm_pow_le'

/-- If `α` is a seminormed ring with `‖1‖ = 1`, then `‖a ^ n‖ ≤ ‖a‖ ^ n`. See also `norm_pow_le'`.-/
theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp only [pow_zero, norm_one]) fun n hn => norm_pow_le' a n.succ_pos
#align norm_pow_le norm_pow_le

theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩
#align eventually_norm_pow_le eventually_norm_pow_le

instance : SemiNormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.seminormedAddCommGroup with }

/-- Seminormed ring structure on the product of two seminormed rings,
  using the sup norm. -/
instance Prod.semiNormedRing [SemiNormedRing β] : SemiNormedRing (α × β) :=
  { Prod.nonUnitalSemiNormedRing, Prod.seminormedAddCommGroup with }
#align prod.semi_normed_ring Prod.semiNormedRing

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.semiNormedRing {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedRing (π i)] :
    SemiNormedRing (∀ i, π i) :=
  { Pi.nonUnitalSemiNormedRing, Pi.seminormedAddCommGroup with }
#align pi.semi_normed_ring Pi.semiNormedRing

instance MulOpposite.semiNormedRing : SemiNormedRing αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSemiNormedRing, MulOpposite.seminormedAddCommGroup with }
#align mul_opposite.semi_normed_ring MulOpposite.semiNormedRing

end SemiNormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSemiNormedRing, ULift.seminormedAddCommGroup with }

/-- Non-unital normed ring structure on the product of two non-unital normed rings,
using the sup norm. -/
instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.seminormedAddCommGroup with norm_mul := norm_mul_le }
#align prod.non_unital_normed_ring Prod.nonUnitalNormedRing

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type _} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.normedAddCommGroup with norm_mul := norm_mul_le }
#align pi.non_unital_normed_ring Pi.nonUnitalNormedRing

instance MulOpposite.nonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ :=
  { MulOpposite.normedAddCommGroup with norm_mul := norm_mul_le }
#align mul_opposite.non_unital_normed_ring MulOpposite.nonUnitalNormedRing

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)
#align units.norm_pos Units.norm_pos

theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos
#align units.nnnorm_pos Units.nnnorm_pos

instance : NormedRing (ULift α) :=
  { ULift.semiNormedRing, ULift.normedAddCommGroup with }

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { Prod.normedAddCommGroup with norm_mul := norm_mul_le }
#align prod.normed_ring Prod.normedRing

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type _} [Fintype ι] [∀ i, NormedRing (π i)] :
    NormedRing (∀ i, π i) :=
  { Pi.normedAddCommGroup with norm_mul := norm_mul_le }
#align pi.normed_ring Pi.normedRing

instance MulOpposite.normedRing : NormedRing αᵐᵒᵖ :=
  { MulOpposite.normedAddCommGroup with norm_mul := norm_mul_le }
#align mul_opposite.normed_ring MulOpposite.normedRing

end NormedRing

-- see Note [lower instance priority]
instance (priority := 100) semi_normed_ring_top_monoid [NonUnitalSemiNormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_tendsto_zero.2 <|
        by
        have : ∀ e : α × α, ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
          by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [mul_sub, sub_mul, sub_add_sub_cancel]
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
            
        refine' squeeze_zero (fun e => norm_nonneg _) this _
        convert
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        show tendsto _ _ _
        exact tendsto_const_nhds
        simp⟩
#align semi_normed_ring_top_monoid semi_normed_ring_top_monoid

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) semi_normed_top_ring [NonUnitalSemiNormedRing α] : TopologicalRing α
    where
#align semi_normed_top_ring semi_normed_top_ring

section NormedDivisionRing

variable [NormedDivisionRing α]

@[simp]
theorem norm_mul (a b : α) : ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormedDivisionRing.norm_mul' a b
#align norm_mul norm_mul

instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩
#align normed_division_ring.to_norm_one_class NormedDivisionRing.to_normOneClass

instance isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ)
    where
  abv_nonneg := norm_nonneg
  abv_eq_zero _ := norm_eq_zero
  abv_add := norm_add_le
  abv_mul := norm_mul
#align is_absolute_value_norm isAbsoluteValue_norm

@[simp]
theorem nnnorm_mul (a b : α) : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ :=
  NNReal.eq <| norm_mul a b
#align nnnorm_mul nnnorm_mul

/-- `norm` as a `monoid_with_zero_hom`. -/
@[simps]
def normHom : α →*₀ ℝ :=
  ⟨norm, norm_zero, norm_one, norm_mul⟩
#align norm_hom normHom

/-- `nnnorm` as a `monoid_with_zero_hom`. -/
@[simps]
def nnnormHom : α →*₀ ℝ≥0 :=
  ⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩
#align nnnorm_hom nnnormHom

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a
#align norm_pow norm_pow

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n
#align nnnorm_pow nnnorm_pow

protected theorem List.norm_prod (l : List α) : ‖l.Prod‖ = (l.map norm).Prod :=
  (normHom.toMonoidHom : α →* ℝ).map_list_prod _
#align list.norm_prod List.norm_prod

protected theorem List.nnnorm_prod (l : List α) : ‖l.Prod‖₊ = (l.map nnnorm).Prod :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_list_prod _
#align list.nnnorm_prod List.nnnorm_prod

@[simp]
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b
#align norm_div norm_div

@[simp]
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b
#align nnnorm_div nnnorm_div

@[simp]
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a
#align norm_inv norm_inv

@[simp]
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp
#align nnnorm_inv nnnorm_inv

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)
#align norm_zpow norm_zpow

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)
#align nnnorm_zpow nnnorm_zpow

theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) : dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) :=
  by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]
#align dist_inv_inv₀ dist_inv_inv₀

theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  by
  rw [← NNReal.coe_eq]
  simp [-NNReal.coe_eq, dist_inv_inv₀ hz hw]
#align nndist_inv_inv₀ nndist_inv_inv₀

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto ((· * ·) a) (comap norm atTop) (comap norm atTop) := by
  simpa only [tendsto_comap_iff, (· ∘ ·), norm_mul] using
    tendsto_const_nhds.mul_at_top (norm_pos_iff.2 ha) tendsto_comap
#align filter.tendsto_mul_left_cobounded Filter.tendsto_mul_left_cobounded

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. TODO: use `bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (fun x => x * a) (comap norm atTop) (comap norm atTop) := by
  simpa only [tendsto_comap_iff, (· ∘ ·), norm_mul] using
    tendsto_comap.at_top_mul (norm_pos_iff.2 ha) tendsto_const_nhds
#align filter.tendsto_mul_right_cobounded Filter.tendsto_mul_right_cobounded

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_hasContinuousInv₀ : HasContinuousInv₀ α :=
  by
  refine' ⟨fun r r0 => tendsto_iff_norm_tendsto_zero.2 _⟩
  have r0' : 0 < ‖r‖ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ‖e⁻¹ - r⁻¹‖ ≤ ‖r - e‖ / ‖r‖ / ε :=
    by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem εr]with e he
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
    calc
      ‖e⁻¹ - r⁻¹‖ = ‖r‖⁻¹ * ‖r - e‖ * ‖e‖⁻¹ := by
        rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, mul_sub, sub_mul, mul_assoc _ e,
          inv_mul_cancel r0, mul_inv_cancel e0, one_mul, mul_one]
      _ = ‖r - e‖ / ‖r‖ / ‖e‖ := by field_simp [mul_comm]
      _ ≤ ‖r - e‖ / ‖r‖ / ε :=
        div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le
      
  refine' squeeze_zero' (eventually_of_forall fun _ => norm_nonneg _) this _
  refine' (((continuous_const.sub continuous_id).norm.div_const _).div_const _).tendsto' _ _ _
  simp
#align normed_division_ring.to_has_continuous_inv₀ NormedDivisionRing.to_hasContinuousInv₀

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_topologicalDivisionRing : TopologicalDivisionRing α
    where
#align normed_division_ring.to_topological_division_ring NormedDivisionRing.to_topologicalDivisionRing

theorem norm_map_one_of_pow_eq_one [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 :=
  by
  rw [← pow_left_inj, ← norm_pow, ← map_pow, h, map_one, norm_one, one_pow]
  exacts[norm_nonneg _, zero_le_one, k.pos]
#align norm_map_one_of_pow_eq_one norm_map_one_of_pow_eq_one

theorem norm_one_of_pow_eq_one {x : α} {k : ℕ+} (h : x ^ (k : ℕ) = 1) : ‖x‖ = 1 :=
  norm_map_one_of_pow_eq_one (MonoidHom.id α) h
#align norm_one_of_pow_eq_one norm_one_of_pow_eq_one

end NormedDivisionRing

/-- A normed field is a field with a norm satisfying ‖x y‖ = ‖x‖ ‖y‖. -/
class NormedField (α : Type _) extends Norm α, Field α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b
#align normed_field NormedField

/-- A nontrivially normed field is a normed field in which there is an element of norm different
from `0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by
multiplication by the powers of any element, and thus to relate algebra and topology. -/
class NontriviallyNormedField (α : Type _) extends NormedField α where
  non_trivial : ∃ x : α, 1 < ‖x‖
#align nontrivially_normed_field NontriviallyNormedField

/-- A densely normed field is a normed field for which the image of the norm is dense in `ℝ≥0`,
which means it is also nontrivially normed. However, not all nontrivally normed fields are densely
normed; in particular, the `padic`s exhibit this fact. -/
class DenselyNormedField (α : Type _) extends NormedField α where
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y
#align densely_normed_field DenselyNormedField

section NormedField

/-- A densely normed field is always a nontrivially normed field.
See note [lower instance priority]. -/
instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α
    where non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩
#align densely_normed_field.to_nontrivially_normed_field DenselyNormedField.toNontriviallyNormedField

variable [NormedField α]

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }
#align normed_field.to_normed_division_ring NormedField.toNormedDivisionRing

-- see Note [lower instance priority]
instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }
#align normed_field.to_normed_comm_ring NormedField.toNormedCommRing

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b in s, f b‖ = ∏ b in s, ‖f b‖ :=
  (normHom.toMonoidHom : α →* ℝ).map_prod f s
#align norm_prod norm_prod

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b in s, f b‖₊ = ∏ b in s, ‖f b‖₊ :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_prod f s
#align nnnorm_prod nnnorm_prod

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial
#align normed_field.exists_one_lt_norm NormedField.exists_one_lt_norm

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩
#align normed_field.exists_lt_norm NormedField.exists_lt_norm

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩
#align normed_field.exists_norm_lt NormedField.exists_norm_lt

theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos
#align normed_field.exists_norm_lt_one NormedField.exists_norm_lt_one

variable {α}

@[instance]
theorem punctured_nhds_neBot (x : α) : NeBot (𝓝[≠] x) :=
  by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine' ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 <| norm_pos_iff.1 hb0, _⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel']
#align normed_field.punctured_nhds_ne_bot NormedField.punctured_nhds_neBot

@[instance]
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using punctured_nhds_ne_bot (0 : α)
#align normed_field.nhds_within_is_unit_ne_bot NormedField.nhdsWithin_isUnit_neBot

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h
#align normed_field.exists_lt_norm_lt NormedField.exists_lt_norm_lt

theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ := by
  exact_mod_cast exists_lt_norm_lt α r₁.prop h
#align normed_field.exists_lt_nnnorm_lt NormedField.exists_lt_nnnorm_lt

instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ))
    where dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    exact
      let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
      ⟨⟨‖z‖, z, rfl⟩, h⟩
#align normed_field.densely_ordered_range_norm NormedField.denselyOrdered_range_norm

instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0))
    where dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    exact
      let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
      ⟨⟨‖z‖₊, z, rfl⟩, h⟩
#align normed_field.densely_ordered_range_nnnorm NormedField.denselyOrdered_range_nnnorm

theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩
#align normed_field.dense_range_nnnorm NormedField.denseRange_nnnorm

end Densely

end NormedField

instance : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul := fun x y => (abs_mul x y).le }

noncomputable instance : NormedField ℝ :=
  { Real.normedAddCommGroup with norm_mul' := abs_mul }

noncomputable instance : DenselyNormedField ℝ
    where lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  simp [Real.toNNReal_of_nonneg, nnnorm, norm_of_nonneg, hx]
#align real.to_nnreal_mul_nnnorm Real.toNNReal_mul_nnnorm

theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  simp [Real.toNNReal_of_nonneg, nnnorm, norm_of_nonneg, hy]
#align real.nnnorm_mul_to_nnreal Real.nnnorm_mul_toNNReal

end Real

namespace NNReal

open NNReal

@[simp]
theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]
#align nnreal.norm_eq NNReal.norm_eq

@[simp]
theorem nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x :=
  NNReal.eq <| Real.norm_of_nonneg x.2
#align nnreal.nnnorm_eq NNReal.nnnorm_eq

end NNReal

@[simp]
theorem norm_norm [SeminormedAddCommGroup α] (x : α) : ‖‖x‖‖ = ‖x‖ :=
  Real.norm_of_nonneg (norm_nonneg _)
#align norm_norm norm_norm

@[simp]
theorem nnnorm_norm [SeminormedAddCommGroup α] (a : α) : ‖‖a‖‖₊ = ‖a‖₊ := by
  simpa [Real.nnnorm_of_nonneg (norm_nonneg a)]
#align nnnorm_norm nnnorm_norm

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [SemilatticeSup α] {β : Type _}
    [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iffₓ Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])
#align normed_add_comm_group.tendsto_at_top NormedAddCommGroup.tendsto_atTop

/-- A variant of `normed_add_comm_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem NormedAddCommGroup.tendsto_at_top' [Nonempty α] [SemilatticeSup α] [NoMaxOrder α]
    {β : Type _} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iffₓ Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])
#align normed_add_comm_group.tendsto_at_top' NormedAddCommGroup.tendsto_at_top'

instance : NormedCommRing ℤ :=
  {
    Int.normedAddCommGroup with
    norm_mul := fun m n => le_of_eq <| by simp only [norm, Int.cast_mul, abs_mul]
    mul_comm := mul_comm }

instance : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance : NormedField ℚ :=
  { Rat.normedAddCommGroup with
    norm_mul' := fun r₁ r₂ => by simp only [norm, Rat.cast_mul, abs_mul] }

instance : DenselyNormedField ℚ
    where lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by
      unfold norm
      rwa [abs_of_pos (h₀.trans_lt h.1)]⟩

section RingHomIsometric

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _}

/-- This class states that a ring homomorphism is isometric. This is a sufficient assumption
for a continuous semilinear map to be bounded and this is the main use for this typeclass. -/
class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  is_iso : ∀ {x : R₁}, ‖σ x‖ = ‖x‖
#align ring_hom_isometric RingHomIsometric

attribute [simp] RingHomIsometric.is_iso

variable [SemiNormedRing R₁] [SemiNormedRing R₂] [SemiNormedRing R₃]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨fun x => rfl⟩
#align ring_hom_isometric.ids RingHomIsometric.ids

end RingHomIsometric

/-! ### Induced normed structures -/


section Induced

variable {F : Type _} (R S : Type _)

/-- A non-unital ring homomorphism from an `non_unital_ring` to a `non_unital_semi_normed_ring`
induces a `non_unital_semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalSemiNormedRing.induced [NonUnitalRing R] [NonUnitalSemiNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSemiNormedRing R :=
  { SeminormedAddCommGroup.induced R S f with
    norm_mul := fun x y => by
      unfold norm
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }
#align non_unital_semi_normed_ring.induced NonUnitalSemiNormedRing.induced

/-- An injective non-unital ring homomorphism from an `non_unital_ring` to a
`non_unital_normed_ring` induces a `non_unital_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSemiNormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align non_unital_normed_ring.induced NonUnitalNormedRing.induced

/-- A non-unital ring homomorphism from an `ring` to a `semi_normed_ring` induces a
`semi_normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SemiNormedRing.induced [Ring R] [SemiNormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SemiNormedRing R :=
  { NonUnitalSemiNormedRing.induced R S f, SeminormedAddCommGroup.induced R S f with }
#align semi_normed_ring.induced SemiNormedRing.induced

/-- An injective non-unital ring homomorphism from an `ring` to a `normed_ring` induces a
`normed_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSemiNormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_ring.induced NormedRing.induced

/-- A non-unital ring homomorphism from a `comm_ring` to a `semi_normed_ring` induces a
`semi_normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SemiNormedCommRing.induced [CommRing R] [SemiNormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SemiNormedCommRing R :=
  { NonUnitalSemiNormedRing.induced R S f, SeminormedAddCommGroup.induced R S f with
    mul_comm := mul_comm }
#align semi_normed_comm_ring.induced SemiNormedCommRing.induced

/-- An injective non-unital ring homomorphism from an `comm_ring` to a `normed_ring` induces a
`normed_comm_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SemiNormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }
#align normed_comm_ring.induced NormedCommRing.induced

/-- An injective non-unital ring homomorphism from an `division_ring` to a `normed_ring` induces a
`normed_division_ring` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S] [NonUnitalRingHomClass F R S]
    (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf with
    norm_mul' := fun x y => by
      unfold norm
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }
#align normed_division_ring.induced NormedDivisionRing.induced

/-- An injective non-unital ring homomorphism from an `field` to a `normed_ring` induces a
`normed_field` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with }
#align normed_field.induced NormedField.induced

/-- A ring homomorphism from a `ring R` to a `semi_normed_ring S` which induces the norm structure
`semi_normed_ring.induced` makes `R` satisfy `‖(1 : R)‖ = 1` whenever `‖(1 : S)‖ = 1`. -/
theorem NormOneClass.induced {F : Type _} (R S : Type _) [Ring R] [SemiNormedRing S]
    [NormOneClass S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SemiNormedRing.induced R S f).toHasNorm _ :=
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }
#align norm_one_class.induced NormOneClass.induced

end Induced

namespace SubringClass

variable {S R : Type _} [SetLike S R]

instance toSemiNormedRing [SemiNormedRing R] [SubringClass S R] (s : S) : SemiNormedRing s :=
  SemiNormedRing.induced s R (SubringClass.subtype s)
#align subring_class.to_semi_normed_ring SubringClass.toSemiNormedRing

instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective
#align subring_class.to_normed_ring SubringClass.toNormedRing

instance toSemiNormedCommRing [SemiNormedCommRing R] [h : SubringClass S R] (s : S) :
    SemiNormedCommRing s :=
  { SubringClass.toSemiNormedRing s with mul_comm := mul_comm }
#align subring_class.to_semi_normed_comm_ring SubringClass.toSemiNormedCommRing

instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  { SubringClass.toNormedRing s with mul_comm := mul_comm }
#align subring_class.to_normed_comm_ring SubringClass.toNormedCommRing

end SubringClass

-- Guard again import creep.
assert_not_exists RestrictScalars

