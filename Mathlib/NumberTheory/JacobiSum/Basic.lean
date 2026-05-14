/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Jacobi Sums

This file defines the *Jacobi sum* of two multiplicative characters `χ` and `ψ` on a finite
commutative ring `R` with values in another commutative ring `R'`:

`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`

(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.

## References

We essentially follow
* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
  (Section 8.3)][IrelandRosen1990]

but generalize where appropriate.

This is based on Lean code written as part of the bachelor's thesis of Alexander Spahl.
-/

@[expose] public section

open Finset

/-!
### Jacobi sums: definition and first properties
-/

section Def

-- need `Fintype` instead of `Finite` to make `jacobiSum` computable.
variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/-- The *Jacobi sum* of two multiplicative characters on a finite commutative ring. -/
def jacobiSum (χ ψ : MulChar R R') : R' :=
  ∑ x : R, χ x * ψ (1 - x)

lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
  simp only [jacobiSum, mul_comm (χ _)]
  rw [← (Equiv.subLeft 1).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

/-- The Jacobi sum is compatible with ring homomorphisms. -/
lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' →+* R'') :
    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

end Def

/-!
### Jacobi sums over finite fields
-/

section CommRing

variable {F R : Type*} [CommRing F] [Nontrivial F] [Fintype F] [DecidableEq F] [CommRing R]

/-- The Jacobi sum of two multiplicative characters on a nontrivial finite commutative ring `F`
can be written as a sum over `F \ {0,1}`. -/
lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x ∈ univ \ {0,1}, χ x * ψ (1 - x) := by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
    neg_eq_zero]
  apply sum_eq_zero
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, χ.map_zero, neg_zero, add_zero, map_one,
    mul_one, forall_eq, add_neg_cancel, ψ.map_zero, mul_zero, and_self]

private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
                      ∑ x ∈ univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show ∀ x y : R, x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ, Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    sum_sdiff_eq_sub (subset_univ _), ← sub_zero (_ - _ + _), add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one, sub_zero, ψ.map_one, χ.map_one, sub_self, mul_zero, zero_mul, add_zero]

end CommRing

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [CommRing R]

/-- The Jacobi sum of twice the trivial multiplicative character on a finite field `F`
equals `#F-2`. -/
theorem jacobiSum_trivial_trivial :
    jacobiSum (MulChar.trivial F R) (MulChar.trivial F R) = Fintype.card F - 2 := by
  classical
  rw [jacobiSum_eq_sum_sdiff]
  have : ∀ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intro x hx
    rw [← map_mul, MulChar.trivial_apply, if_pos]
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, ne_eq, sub_eq_zero, @eq_comm _ _ x] using hx
  calc ∑ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ ∈ univ \ {0, 1}, 1 := sum_congr rfl this
  _ = #(univ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair zero_ne_one,
      Nat.cast_sub <| Nat.add_one_le_of_lt Fintype.one_lt_card, Nat.cast_two]

/-- If `1` is the trivial multiplicative character on a finite field `F`, then `J(1,1) = #F-2`. -/
theorem jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2 :=
  jacobiSum_trivial_trivial

variable [IsDomain R] -- needed for `MulChar.sum_eq_zero_of_ne_one`

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`, then `J(1,χ) = -1`. -/
theorem jacobiSum_one_nontrivial {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum 1 χ = -1 := by
  classical
  have : ∑ x ∈ univ \ {0, 1}, ((1 : MulChar F R) x - 1) * (χ (1 - x) - 1) = 0 := by
    apply Finset.sum_eq_zero
    simp +contextual only [mem_sdiff, mem_univ, mem_insert, mem_singleton,
      not_or, ← isUnit_iff_ne_zero, true_and, MulChar.one_apply, sub_self, zero_mul,
      implies_true]
  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
    add_zero, Fintype.card_eq_card_units_add_one (α := F), Nat.cast_add, Nat.cast_one,
    sub_add_cancel_left, this]

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`,
then `J(χ,χ⁻¹) = -χ(-1)`. -/
theorem jacobiSum_nontrivial_inv {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum χ χ⁻¹ = -χ (-1) := by
  classical
  rw [jacobiSum]
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_diff_singleton_add (mem_univ (1 : F)), sub_self, div_zero, χ.map_zero, add_zero]
  have : ∑ x ∈ univ \ {1}, χ (x / (1 - x)) = ∑ x ∈ univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ ↦ a / (1 - a)) (fun b _ ↦ b / (1 + b)) (fun x hx ↦ ?_)
      (fun y hy ↦ ?_) (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun _ _ ↦ rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm, mul_sub, mul_one,
        neg_one_mul, sub_neg_eq_add, right_eq_add, neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h ↦ hy <| eq_neg_of_add_eq_zero_right h, one_mul, right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm, ← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add] at hy
      simp [field]
  rw [this, ← add_eq_zero_iff_eq_neg, ← sum_eq_sum_diff_singleton_add (mem_univ (-1 : F))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` such that
`χφ` is nontrivial, then `g(χφ) * J(χ,φ) = g(χ) * g(φ)`. -/
theorem jacobiSum_mul_nontrivial {χ φ : MulChar F R} (h : χ * φ ≠ 1) (ψ : AddChar F R) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ := by
  classical
  rw [gaussSum_mul _ _ ψ, sum_eq_sum_diff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub, neg_eq_neg_one_mul x, map_mul, mul_left_comm (χ x) (φ (-1)),
      ← MulChar.mul_apply, ψ.map_zero_eq_one, mul_one]
  rw [← mul_sum _ _ (φ (-1)), MulChar.sum_eq_zero_of_ne_one h, mul_zero, add_zero]
  have sum_eq : ∀ t ∈ univ \ {0}, (∑ x : F, χ x * φ (t - x)) * ψ t =
      (∑ y : F, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at ht
    exact congrArg (· * ψ t) (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
  simp_rw [← sum_mul, sum_congr rfl sum_eq, ← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum, mul_right_comm]
  rw [← jacobiSum, ← sum_mul, gaussSum, sum_eq_sum_diff_singleton_add (mem_univ (0 : F)),
    (χ * φ).map_zero, zero_mul, add_zero]

end FiniteField

section field_field

variable {F F' : Type*} [Fintype F] [Field F] [Field F']

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` with values
in another field `F'` and such that `χφ` is nontrivial, then `J(χ,φ) = g(χ) * g(φ) / g(χφ)`. -/
theorem jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (h : (Fintype.card F : F') ≠ 0)
    {χ φ : MulChar F F'} (hχφ : χ * φ ≠ 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by
  rw [eq_div_iff <| gaussSum_ne_zero_of_nontrivial h hχφ hψ, mul_comm]
  exact jacobiSum_mul_nontrivial hχφ ψ

open AddChar MulChar in
/-- If `χ` and `φ` are multiplicative characters on a finite field `F` with values in another
field `F'` such that `χ`, `φ` and `χφ` are all nontrivial and `char F' ≠ char F`, then
`J(χ,φ) * J(χ⁻¹,φ⁻¹) = #F` (in `F'`). -/
lemma jacobiSum_mul_jacobiSum_inv (h : ringChar F' ≠ ringChar F) {χ φ : MulChar F F'} (hχ : χ ≠ 1)
    (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- Obtain primitive additive character `ψ : F → FF'`.
  let ψ := FiniteField.primitiveChar F F' h
  -- the target field of `ψ`
  let FF' := CyclotomicField ψ.n F'
  -- Consider `χ` and `φ` as characters `F → FF'`.
  let χ' := χ.ringHomComp (algebraMap F' FF')
  let φ' := φ.ringHomComp (algebraMap F' FF')
  have hinj := (algebraMap F' FF').injective
  apply hinj
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp]
  have Hχφ : χ' * φ' ≠ 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ
  have Hχφ' : χ'⁻¹ * φ'⁻¹ ≠ 1 := by
    rwa [← mul_inv, inv_ne_one]
  have Hχ : χ' ≠ 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ
  have Hφ : φ' ≠ 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hφ
  have Hcard : (Fintype.card F : FF') ≠ 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
    exact h <| (Algebra.ringChar_eq F' FF').trans <| CharP.ringChar_of_prime_eq_zero hp H
  have H := (gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim).trans_ne Hcard
  apply_fun (gaussSum (χ' * φ') ψ.char * gaussSum (χ' * φ')⁻¹ ψ.char⁻¹ * ·)
    using mul_right_injective₀ H
  simp only
  rw [mul_mul_mul_comm, jacobiSum_mul_nontrivial Hχφ, mul_inv, ← ringHomComp_inv,
    ← ringHomComp_inv, jacobiSum_mul_nontrivial Hχφ', map_natCast, ← mul_mul_mul_comm,
    gaussSum_mul_gaussSum_eq_card Hχ ψ.prim, gaussSum_mul_gaussSum_eq_card Hφ ψ.prim,
    ← mul_inv, gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim]

end field_field

section image

variable {F R : Type*} [Field F] [CommRing R] [IsDomain R]

open Algebra

section finite

variable [Finite F]

private
lemma MulChar.exists_apply_sub_one_eq_mul_sub_one {n : ℕ} [NeZero n] {χ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x ≠ 0) :
    ∃ z ∈ ℤ[μ], χ x - 1 = z * (μ - 1) := by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private
lemma MulChar.exists_apply_sub_one_mul_apply_sub_one {n : ℕ} [NeZero n] {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ n) (x : F) :
    ∃ z ∈ ℤ[μ], (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, ψ.map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [χ.map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.exists_apply_sub_one_eq_mul_sub_one hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ :=
    MulChar.exists_apply_sub_one_eq_mul_sub_one hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  rewrite [Hz₁, Hz₂, sq]
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_mul_mul_comm ..⟩

end finite

variable [Fintype F]

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` satisfying `χ^n = φ^n = 1`
and with values in an integral domain `R`, and `μ` is a primitive `n`th root of unity in `R`,
then the Jacobi sum `J(χ,φ)` is in `ℤ[μ] ⊆ R`. -/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : ℕ} [NeZero n] {χ φ : MulChar F R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ φ ∈ ℤ[μ] :=
  Subalgebra.sum_mem _ fun _ _ ↦ Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hφ hμ _)

/-- If `χ` and `ψ` are multiplicative characters of order dividing `n` on a finite field `F`
with values in an integral domain `R` and `μ` is a primitive `n`th root of unity in `R`,
then `J(χ,ψ) = -1 + z*(μ - 1)^2` for some `z ∈ ℤ[μ] ⊆ R`. (We assume that `#F ≡ 1 mod n`.)
Note that we do not state this as a divisibility in `R`, as this would give a weaker statement. -/
lemma exists_jacobiSum_eq_neg_one_add {n : ℕ} (hn : 2 < n) {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hn' : n ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ ℤ[μ], jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
  obtain ⟨q, hq⟩ := hn'
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq, Nat.cast_add, Nat.cast_mul, Hz₁]
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀, jacobiSum_one_nontrivial hψ₀, zero_mul, add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm, hψ₀, jacobiSum_one_nontrivial hχ₀, zero_mul, add_zero]
  · classical
    rw [jacobiSum_eq_aux, MulChar.sum_eq_zero_of_ne_one hχ₀, MulChar.sum_eq_zero_of_ne_one hψ₀, hq]
    have : NeZero n := ⟨by lia⟩
    have H := MulChar.exists_apply_sub_one_mul_apply_sub_one hχ hψ hμ
    have Hcs x := (H x).choose_spec
    refine ⟨-q * z₁ + ∑ x ∈ (univ \ {0, 1} : Finset F), (H x).choose, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ ↦ (Hcs x).1
    · conv => enter [1, 2, 2, x]; rw [(Hcs x).2]
      rw [← Finset.sum_mul, Nat.cast_add, Nat.cast_mul, Hz₁]
      ring

end image

section GaussSum

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

lemma gaussSum_pow_eq_prod_jacobiSum_aux (χ : MulChar F R) (ψ : AddChar F R) {n : ℕ}
    (hn₁ : 0 < n) (hn₂ : n < orderOf χ) :
    gaussSum χ ψ ^ n = gaussSum (χ ^ n) ψ * ∏ j ∈ Ico 1 n, jacobiSum χ (χ ^ j) := by
  induction n, hn₁ using Nat.le_induction with
  | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
  | succ n hn ih =>
      specialize ih <| lt_trans (Nat.lt_succ_self n) hn₂
      have gauss_rw : gaussSum (χ ^ n) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
        have hχn : χ * (χ ^ n) ≠ 1 :=
          pow_succ' χ n ▸ pow_ne_one_of_lt_orderOf n.add_one_ne_zero hn₂
        rw [mul_comm, ← jacobiSum_mul_nontrivial hχn, mul_comm, ← pow_succ']
      apply_fun (· * gaussSum χ ψ) at ih
      rw [mul_right_comm, ← pow_succ, gauss_rw] at ih
      rw [ih, Finset.prod_Ico_succ_top hn, mul_rotate, mul_assoc]

/-- If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`. -/
theorem gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 ≤ orderOf χ)
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ orderOf χ =
      χ (-1) * Fintype.card F * ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) := by
  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
  apply_fun (gaussSum χ ψ * ·) at this
  rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos (by lia)] at this
  have hχ₁ : χ ≠ 1 :=
    fun h ↦ ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [this, ← mul_assoc, gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

end GaussSum
