/-
Copyright (c) 2024 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Density
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Average over a finset

This file defines `Finset.expect`, the average (aka expectation) of a function over a finset.

## Notation

* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`. This is referred to
  as `expectWith` in lemma names.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

## Implementation notes

This definition is a special case of the general convex combination operator in a convex space.
However:
1. We don't yet have general convex spaces.
2. The uniform weights case is an overwhelmingly useful special case which should have its own API.

When convex spaces are finally defined, we should redefine `Finset.expect` in terms of that convex
combination operator.

## TODO

* Connect `Finset.expect` with the expectation over `s` in the probability theory sense.
* Give a formulation of Jensen's inequality in this language.
-/

open Finset Function
open Fintype (card)
open scoped Pointwise

variable {ι κ M N : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

/-- Average of a function over a finset. If the finset is empty, this is equal to zero. -/
def Finset.expect [AddCommMonoid M] [Module ℚ≥0 M] (s : Finset ι) (f : ι → M) : M :=
  (#s : ℚ≥0)⁻¹ • ∑ i ∈ s, f i

namespace BigOperators
open Batteries.ExtendedBinder Lean Meta

/--
* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

These support destructuring, for example `𝔼 ⟨i, j⟩ ∈ s ×ˢ t, f i j`.

Notation: `"𝔼" bigOpBinders* ("with" term)? "," term` -/
scoped syntax (name := bigexpect) "𝔼 " bigOpBinders ("with " term)? ", " term:67 : term

scoped macro_rules (kind := bigexpect)
  | `(𝔼 $bs:bigOpBinders $[with $p?]?, $v) => do
    let processed ← processBigOpBinders bs
    let i ← bigOpBindersPattern processed
    let s ← bigOpBindersProd processed
    match p? with
    | some p => `(Finset.expect (Finset.filter (fun $i ↦ $p) $s) (fun $i ↦ $v))
    | none => `(Finset.expect $s (fun $i ↦ $v))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr
open Batteries.ExtendedBinder

/-- Delaborator for `Finset.expect`. The `pp.funBinderTypes` option controls whether
to show the domain type when the expect is over `Finset.univ`. -/
@[scoped app_delab Finset.expect] def delabFinsetExpect : Delab :=
  whenPPOption getPPNotation <| withOverApp 6 <| do
  let #[_, _, _, _, s, f] := (← getExpr).getAppArgs | failure
  guard <| f.isLambda
  let ppDomain ← getPPOption getPPFunBinderTypes
  let (i, body) ← withAppArg <| withBindingBodyUnusedName fun i => do
    return (i, ← delab)
  if s.isAppOfArity ``Finset.univ 2 then
    let binder ←
      if ppDomain then
        let ty ← withNaryArg 0 delab
        `(bigOpBinder| $(.mk i):ident : $ty)
      else
        `(bigOpBinder| $(.mk i):ident)
    `(𝔼 $binder:bigOpBinder, $body)
  else
    let ss ← withNaryArg 4 <| delab
    `(𝔼 $(.mk i):ident ∈ $ss, $body)

end BigOperators

open scoped BigOperators

namespace Finset
section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

lemma expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /ℚ Fintype.card ι := by
  rw [expect, card_univ]

@[simp] lemma expect_empty (f : ι → M) : 𝔼 i ∈ ∅, f i = 0 := by simp [expect]
@[simp] lemma expect_singleton (f : ι → M) (i : ι) : 𝔼 j ∈ {i}, f j = f i := by simp [expect]
@[simp] lemma expect_const_zero (s : Finset ι) : 𝔼 _i ∈ s, (0 : M) = 0 := by simp [expect]

@[congr]
lemma expect_congr {t : Finset ι} (hst : s = t) (h : ∀ i ∈ t, f i = g i) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by rw [expect, expect, sum_congr hst h, hst]

lemma expectWith_congr (hst : s = t) (hpq : ∀ i ∈ t, p i ↔ q i) (h : ∀ i ∈ t, q i → f i = g i) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ t with q i, g i :=
  expect_congr (by rw [hst, filter_inj'.2 hpq]) <| by simpa using h

lemma expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, 𝔼 i ∈ s, f i j := by
  simpa only [expect, smul_sum] using sum_comm

lemma expect_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, 𝔼 j ∈ t, f i j = 𝔼 j ∈ t, 𝔼 i ∈ s, f i j := by
  rw [expect, expect, ← expect_sum_comm, ← expect_sum_comm, expect, expect, smul_comm, sum_comm]

lemma expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 :=
  (expect_congr rfl h).trans s.expect_const_zero

lemma exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact expect_eq_zero h

lemma expect_add_distrib (s : Finset ι) (f g : ι → M) :
    𝔼 i ∈ s, (f i + g i) = 𝔼 i ∈ s, f i + 𝔼 i ∈ s, g i := by
  simp [expect, sum_add_distrib]

lemma expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → M) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [expect_add_distrib, add_add_add_comm]

lemma expect_eq_single_of_mem (i : ι) (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = 0) :
    𝔼 i ∈ s, f i = f i /ℚ #s := by rw [expect, sum_eq_single_of_mem _ hi h]

lemma expect_ite_zero (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : M) :
    𝔼 i ∈ s, ite (p i) a 0 = ite (∃ i ∈ s, p i) (a /ℚ #s) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

section DecidableEq
variable [DecidableEq ι]

lemma expect_ite_mem (s t : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, (if i ∈ t then f i else 0) = (#(s ∩ t) / #s : ℚ≥0) • 𝔼 i ∈ s ∩ t, f i := by
  obtain hst | hst := (s ∩ t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

@[simp] lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    𝔼 j ∈ s, (if h : i = j then f j h else 0) = if i ∈ s then f i rfl /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → M) :
    𝔼 j ∈ s, (if h : j = i then f j h else 0) = if i ∈ s then f i rfl /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq (i : ι) (f : ι → M) :
    𝔼 j ∈ s, (if i = j then f j else 0) = if i ∈ s then f i /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]

@[simp] lemma expect_ite_eq' (i : ι) (f : ι → M) :
    𝔼 j ∈ s, (if j = i then f j else 0) = if i ∈ s then f i /ℚ #s else 0 := by
  split_ifs <;> simp [expect, *]

end DecidableEq

section bij
variable {t : Finset κ} {g : κ → M}

/-- Reorder an average.

The difference with `Finset.expect_bij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_nbij` is that the bijection is allowed to use membership of the
domain of the average, rather than being a non-dependent function. -/
lemma expect_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

/-- Reorder an average.

The difference with `Finset.expect_bij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_nbij'` is that the bijection and its inverse are allowed to use
membership of the domains of the averages, rather than being non-dependent functions. -/
lemma expect_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

/-- Reorder an average.

The difference with `Finset.expect_nbij'` is that the bijection is specified as a surjective
injection, rather than by an inverse function.

The difference with `Finset.expect_bij` is that the bijection is a non-dependent function, rather
than being allowed to use membership of the domain of the average. -/
lemma expect_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

/-- Reorder an average.

The difference with `Finset.expect_nbij` is that the bijection is specified with an inverse, rather
than as a surjective injection.

The difference with `Finset.expect_bij'` is that the bijection and its inverse are non-dependent
functions, rather than being allowed to use membership of the domains of the averages.

The difference with `Finset.expect_equiv` is that bijectivity is only required to hold on the
domains of the averages, rather than on the entire types. -/
lemma expect_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

/-- `Finset.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments. -/
lemma expect_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

/-- Expectation over a product set equals the expectation of the fiberwise expectations.

For rewriting in the reverse direction, use `Finset.expect_product'`. -/
lemma expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ → M) :
    𝔼 x ∈ s ×ˢ t, f x = 𝔼 i ∈ s, 𝔼 j ∈ t, f (i, j) := by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

/-- Expectation over a product set equals the expectation of the fiberwise expectations.

For rewriting in the reverse direction, use `Finset.expect_product`. -/
lemma expect_product' (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s ×ˢ t, f i.1 i.2 = 𝔼 i ∈ s, 𝔼 j ∈ t, f i j := by
  simp only [expect, card_product, sum_product', smul_sum, mul_inv, mul_smul, Nat.cast_mul]

@[simp]
lemma expect_image [DecidableEq ι] {m : κ → ι} (hm : (t : Set κ).InjOn m) :
    𝔼 i ∈ t.image m, f i = 𝔼 i ∈ t, f (m i) := by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

end bij

@[simp] lemma expect_inv_index [DecidableEq ι] [InvolutiveInv ι] (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ s⁻¹, f i = 𝔼 i ∈ s, f i⁻¹ := expect_image inv_injective.injOn

@[simp] lemma expect_neg_index [DecidableEq ι] [InvolutiveNeg ι] (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ -s, f i = 𝔼 i ∈ s, f (-i) := expect_image neg_injective.injOn

lemma _root_.map_expect {F : Type*} [FunLike F M N] [LinearMapClass F ℚ≥0 M N]
    (g : F) (f : ι → M) (s : Finset ι) :
    g (𝔼 i ∈ s, f i) = 𝔼 i ∈ s, g (f i) := by simp only [expect, map_smul, map_sum]

@[simp]
lemma card_smul_expect (s : Finset ι) (f : ι → M) : #s • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul ℚ≥0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero

@[simp] lemma _root_.Fintype.card_smul_expect [Fintype ι] (f : ι → M) :
    Fintype.card ι • 𝔼 i, f i = ∑ i, f i := Finset.card_smul_expect _ _

@[simp] lemma expect_const (hs : s.Nonempty) (a : M) : 𝔼 _i ∈ s, a = a := by
  rw [expect, sum_const, ← Nat.cast_smul_eq_nsmul ℚ≥0, inv_smul_smul₀]
  exact mod_cast hs.card_ne_zero

lemma smul_expect {G : Type*} [DistribSMul G M] [SMulCommClass G ℚ≥0 M] (a : G)
    (s : Finset ι) (f : ι → M) : a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i := by
  simp only [expect, smul_sum, smul_comm]

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup M] [Module ℚ≥0 M]

lemma expect_sub_distrib (s : Finset ι) (f g : ι → M) :
    𝔼 i ∈ s, (f i - g i) = 𝔼 i ∈ s, f i - 𝔼 i ∈ s, g i := by
  simp only [expect, sum_sub_distrib, smul_sub]

@[simp]
lemma expect_neg_distrib (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, -f i = -𝔼 i ∈ s, f i := by
  simp [expect]

end AddCommGroup

section Semiring
variable [Semiring M] [Module ℚ≥0 M]

@[simp] lemma card_mul_expect (s : Finset ι) (f : ι → M) :
    #s * 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by rw [← nsmul_eq_mul, card_smul_expect]

@[simp] lemma _root_.Fintype.card_mul_expect [Fintype ι] (f : ι → M) :
    Fintype.card ι * 𝔼 i, f i = ∑ i, f i := Finset.card_mul_expect _ _

lemma expect_mul [IsScalarTower ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    (𝔼 i ∈ s, f i) * a = 𝔼 i ∈ s, f i * a := by rw [expect, expect, smul_mul_assoc, sum_mul]

lemma mul_expect [SMulCommClass ℚ≥0 M M] (s : Finset ι) (f : ι → M) (a : M) :
    a * 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a * f i := by rw [expect, expect, mul_smul_comm, mul_sum]

lemma expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (s : Finset ι)
    (t : Finset κ) (f : ι → M) (g : κ → M) :
    (𝔼 i ∈ s, f i) * 𝔼 j ∈ t, g j = 𝔼 i ∈ s, 𝔼 j ∈ t, f i * g j := by
  simp_rw [expect_mul, mul_expect]

end Semiring

section CommSemiring
variable [CommSemiring M] [Module ℚ≥0 M] [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M]

lemma expect_pow (s : Finset ι) (f : ι → M) (n : ℕ) :
    (𝔼 i ∈ s, f i) ^ n = 𝔼 p ∈ Fintype.piFinset fun _ : Fin n ↦ s, ∏ i, f (p i) := by
  classical
  rw [expect, smul_pow, sum_pow', expect, Fintype.card_piFinset_const, inv_pow, Nat.cast_pow]

end CommSemiring

section Semifield
variable [Semifield M] [CharZero M]

lemma expect_boole_mul [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (i = j) (Fintype.card ι : M) 0 * f j = f i := by
  simp_rw [expect_univ, ite_mul, zero_mul, sum_ite_eq, if_pos (mem_univ _)]
  rw [← @NNRat.cast_natCast M, ← NNRat.smul_def, inv_smul_smul₀]
  simp [Fintype.card_ne_zero]

lemma expect_boole_mul' [Fintype ι] [Nonempty ι] [DecidableEq ι] (f : ι → M) (i : ι) :
    𝔼 j, ite (j = i) (Fintype.card ι : M) 0 * f j = f i := by
  simp_rw [@eq_comm _ _ i, expect_boole_mul]

lemma expect_eq_sum_div_card (s : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, f i = (∑ i ∈ s, f i) / #s := by
  rw [expect, NNRat.smul_def, div_eq_inv_mul, NNRat.cast_inv, NNRat.cast_natCast]

lemma _root_.Fintype.expect_eq_sum_div_card [Fintype ι] (f : ι → M) :
    𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Finset.expect_eq_sum_div_card _ _

lemma expect_div (s : Finset ι) (f : ι → M) (a : M) : (𝔼 i ∈ s, f i) / a = 𝔼 i ∈ s, f i / a := by
  simp_rw [div_eq_mul_inv, expect_mul]

end Semifield

@[simp] lemma expect_apply {α : Type*} {π : α → Type*} [∀ a, CommSemiring (π a)]
    [∀ a, Module ℚ≥0 (π a)] (s : Finset ι) (f : ι → ∀ a, π a) (a : α) :
    (𝔼 i ∈ s, f i) a = 𝔼 i ∈ s, f i a := by simp [expect]

end Finset

namespace algebraMap
variable [Semifield M] [CharZero M] [Semifield N] [CharZero N] [Algebra M N]

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : N) :=
  map_expect (algebraMap _ _) _ _

end algebraMap

namespace Fintype
variable [Fintype ι] [Fintype κ]

section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M]

/-- `Fintype.expect_bijective` is a variant of `Finset.expect_bij` that accepts
`Function.Bijective`.

See `Function.Bijective.expect_comp` for a version without `h`. -/
lemma expect_bijective (e : ι → κ) (he : Bijective e) (f : ι → M) (g : κ → M)
    (h : ∀ i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i :=
  expect_nbij e (fun _ _ ↦ mem_univ _) (fun i _ ↦ h i) he.injective.injOn <| by
    simpa using he.surjective

/-- `Fintype.expect_equiv` is a specialization of `Finset.expect_bij` that automatically fills in
most arguments.

See `Equiv.expect_comp` for a version without `h`. -/
lemma expect_equiv (e : ι ≃ κ) (f : ι → M) (g : κ → M) (h : ∀ i, f i = g (e i)) :
    𝔼 i, f i = 𝔼 i, g i := expect_bijective _ e.bijective f g h

lemma expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = a := Finset.expect_const univ_nonempty _

lemma expect_ite_zero (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : M) :
    𝔼 i, ite (p i) a 0 = ite (∃ i, p i) (a /ℚ Fintype.card ι) 0 := by
  simp [univ.expect_ite_zero p (by simpa using h)]

variable [DecidableEq ι]

@[simp] lemma expect_ite_mem (s : Finset ι) (f : ι → M) :
    𝔼 i, (if i ∈ s then f i else 0) = s.dens • 𝔼 i ∈ s, f i := by
  simp [Finset.expect_ite_mem, dens]

lemma expect_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl /ℚ card ι := by simp

lemma expect_dite_eq' (i : ι) (f : ∀ j, j = i → M) :
    𝔼 j, (if h : j = i then f j h else 0) = f i rfl /ℚ card ι := by simp

lemma expect_ite_eq (i : ι) (f : ι → M) :
    𝔼 j, (if i = j then f j else 0) = f i /ℚ card ι := by simp

lemma expect_ite_eq' (i : ι) (f : ι → M) :
    𝔼 j, (if j = i then f j else 0) = f i /ℚ card ι := by simp

end AddCommMonoid

section Semiring
variable [Semiring M] [Module ℚ≥0 M]

lemma expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : M) = 1 := expect_const _

lemma expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (f : ι → M)
    (g : κ → M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j :=
  Finset.expect_mul_expect ..

end Semiring
end Fintype
