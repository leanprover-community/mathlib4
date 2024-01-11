/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Powerset

#align_import algebra.big_operators.ring from "leanprover-community/mathlib"@"b2c89893177f66a48daf993b7ba5ef7cddeff8c9"

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/


universe u v w

open BigOperators

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {b : β} {f g : α → β}

section CommMonoid

variable [CommMonoid β]

open Classical

theorem prod_pow_eq_pow_sum {x : β} {f : α → ℕ} :
    ∀ {s : Finset α}, ∏ i in s, x ^ f i = x ^ ∑ x in s, f x := by
  apply Finset.induction
  · simp
  · intro a s has H
    rw [Finset.prod_insert has, Finset.sum_insert has, pow_add, H]
#align finset.prod_pow_eq_pow_sum Finset.prod_pow_eq_pow_sum

end CommMonoid

section Semiring

variable [NonUnitalNonAssocSemiring β]

theorem sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
  map_sum (AddMonoidHom.mulRight b) _ s
#align finset.sum_mul Finset.sum_mul

theorem mul_sum : (b * ∑ x in s, f x) = ∑ x in s, b * f x :=
  map_sum (AddMonoidHom.mulLeft b) _ s
#align finset.mul_sum Finset.mul_sum

theorem sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (f₁ : ι₁ → β)
    (f₂ : ι₂ → β) :
    ((∑ x₁ in s₁, f₁ x₁) * ∑ x₂ in s₂, f₂ x₂) = ∑ p in s₁ ×ˢ s₂, f₁ p.1 * f₂ p.2 := by
  rw [sum_product, sum_mul, sum_congr rfl]
  intros
  rw [mul_sum]
#align finset.sum_mul_sum Finset.sum_mul_sum

end Semiring

section Semiring

theorem dvd_sum [NonUnitalSemiring β]
    {b : β} {s : Finset α} {f : α → β} (h : ∀ x ∈ s, b ∣ f x) : b ∣ ∑ x in s, f x :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx
#align finset.dvd_sum Finset.dvd_sum

variable [NonAssocSemiring β]

theorem sum_mul_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, f x * ite (a = x) 1 0) = ite (a ∈ s) (f a) 0 := by simp
#align finset.sum_mul_boole Finset.sum_mul_boole

theorem sum_boole_mul [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, ite (a = x) 1 0 * f x) = ite (a ∈ s) (f a) 0 := by simp
#align finset.sum_boole_mul Finset.sum_boole_mul

end Semiring

theorem sum_div [DivisionSemiring β] {s : Finset α} {f : α → β} {b : β} :
    (∑ x in s, f x) / b = ∑ x in s, f x / b := by simp only [div_eq_mul_inv, sum_mul]
#align finset.sum_div Finset.sum_div

section CommSemiring

variable [CommSemiring β]

/-- The product over a sum can be written as a sum over the product of sets, `Finset.Pi`.
  `Finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
theorem prod_sum {δ : α → Type*} [DecidableEq α] [∀ a, DecidableEq (δ a)] {s : Finset α}
    {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a → β} :
    (∏ a in s, ∑ b in t a, f a b) = ∑ p in s.pi t, ∏ x in s.attach, f x.1 (p x.1 x.2) := by
  induction' s using Finset.induction with a s ha ih
  · rw [pi_empty, sum_singleton]
    rfl
  · have h₁ : ∀ x ∈ t a, ∀ y ∈ t a, x ≠ y →
      Disjoint (image (Pi.cons s a x) (pi s t)) (image (Pi.cons s a y) (pi s t)) := by
      intro x _ y _ h
      simp only [disjoint_iff_ne, mem_image]
      rintro _ ⟨p₂, _, eq₂⟩ _ ⟨p₃, _, eq₃⟩ eq
      have : Pi.cons s a x p₂ a (mem_insert_self _ _)
              = Pi.cons s a y p₃ a (mem_insert_self _ _) := by rw [eq₂, eq₃, eq]
      rw [Pi.cons_same, Pi.cons_same] at this
      exact h this
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_biUnion h₁]
    refine' sum_congr rfl fun b _ => _
    have h₂ : ∀ p₁ ∈ pi s t, ∀ p₂ ∈ pi s t, Pi.cons s a b p₁ = Pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Pi.cons_injective ha eq
    rw [sum_image h₂, mul_sum]
    refine' sum_congr rfl fun g _ => _
    rw [attach_insert, prod_insert, prod_image]
    · simp only [Pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (Pi.cons_ne (by rintro rfl; exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.eq ∘ Subtype.mk.inj
    · simpa only [mem_image, mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, exists_prop, exists_eq_right] using ha
#align finset.prod_sum Finset.prod_sum

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
theorem prod_add [DecidableEq α] (f g : α → β) (s : Finset α) :
    ∏ a in s, (f a + g a) = ∑ t in s.powerset, (∏ a in t, f a) * ∏ a in s \ t, g a := by
  classical
  calc
    ∏ a in s, (f a + g a) =
        ∏ a in s, ∑ p in ({True, False} : Finset Prop), if p then f a else g a := by simp
    _ = ∑ p in (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 :=
      prod_sum
    _ = ∑ t in s.powerset, (∏ a in t, f a) * ∏ a in s \ t, g a :=
      sum_bij'
        (fun f _ ↦ s.filter fun a ↦ ∃ h : a ∈ s, f a h)
        (fun t _ a _ => a ∈ t)
        (by simp)
        (by simp [Classical.em])
        (by simp_rw [mem_filter, Function.funext_iff, eq_iff_iff, mem_pi, mem_insert]; tauto)
        (by simp_rw [ext_iff, @mem_filter _ _ (id _), mem_powerset]; tauto)
        (fun a _ ↦ by
          simp only [prod_ite, filter_attach', prod_map, Function.Embedding.coeFn_mk,
            Subtype.map_coe, id_eq, prod_attach, filter_congr_decidable]
          congr 2 with x
          simp only [mem_filter, mem_sdiff, not_and, not_exists, and_congr_right_iff]
          tauto)
#align finset.prod_add Finset.prod_add

/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered {ι R : Type*} [CommSemiring R] [LinearOrder ι] (s : Finset ι)
    (f g : ι → R) :
    ∏ i in s, (f i + g i) =
      (∏ i in s, f i) +
        ∑ i in s,
          g i * (∏ j in s.filter (· < i), (f j + g j)) * ∏ j in s.filter fun j => i < j, f j := by
  refine' Finset.induction_on_max s (by simp) _
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha', prod_insert ha', sum_insert ha', filter_insert, if_neg (lt_irrefl a),
    filter_true_of_mem ha, ihs, add_mul, mul_add, mul_add, add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_one]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_lt⟩
  · rw [mul_sum]
    refine' sum_congr rfl fun i hi => _
    rw [filter_insert, if_neg (ha i hi).not_lt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'
#align finset.prod_add_ordered Finset.prod_add_ordered

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
theorem prod_sub_ordered {ι R : Type*} [CommRing R] [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i in s, (f i - g i) =
      (∏ i in s, f i) -
        ∑ i in s,
          g i * (∏ j in s.filter (· < i), (f j - g j)) * ∏ j in s.filter fun j => i < j, f j := by
  simp only [sub_eq_add_neg]
  convert prod_add_ordered s f fun i => -g i
  simp
#align finset.prod_sub_ordered Finset.prod_sub_ordered

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions.  -/
theorem prod_one_sub_ordered {ι R : Type*} [CommRing R] [LinearOrder ι] (s : Finset ι)
    (f : ι → R) : ∏ i in s, (1 - f i) = 1 - ∑ i in s, f i * ∏ j in s.filter (· < i), (1 - f j) := by
  rw [prod_sub_ordered]
  simp
#align finset.prod_one_sub_ordered Finset.prod_one_sub_ordered

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `Finset`
gives `(a + b)^s.card`.-/
theorem sum_pow_mul_eq_add_pow {α R : Type*} [CommSemiring R] (a b : R) (s : Finset α) :
    (∑ t in s.powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card := by
  classical
  rw [← prod_const, prod_add]
  refine' Finset.sum_congr rfl fun t ht => _
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]
#align finset.sum_pow_mul_eq_add_pow Finset.sum_pow_mul_eq_add_pow

@[norm_cast]
theorem prod_natCast (s : Finset α) (f : α → ℕ) : ↑(∏ x in s, f x : ℕ) = ∏ x in s, (f x : β) :=
  map_prod (Nat.castRingHom β) f s
#align finset.prod_nat_cast Finset.prod_natCast

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

theorem prod_range_cast_nat_sub (n k : ℕ) :
    ∏ i in range k, (n - i : R) = (∏ i in range k, (n - i) : ℕ) := by
  rw [prod_natCast]
  rcases le_or_lt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp
#align finset.prod_range_cast_nat_sub Finset.prod_range_cast_nat_sub

end CommRing

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive
      "A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all subsets
      of `s`, and over all subsets of `s` to which one adds `x`."]
theorem prod_powerset_insert [DecidableEq α] [CommMonoid β] {s : Finset α} {x : α} (h : x ∉ s)
    (f : Finset α → β) :
    (∏ a in (insert x s).powerset, f a) =
      (∏ a in s.powerset, f a) * ∏ t in s.powerset, f (insert x t) := by
  rw [powerset_insert, Finset.prod_union, Finset.prod_image]
  · intro t₁ h₁ t₂ h₂ heq
    rw [← Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h), ←
      Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), heq]
  · rw [Finset.disjoint_iff_ne]
    intro t₁ h₁ t₂ h₂
    rcases Finset.mem_image.1 h₂ with ⟨t₃, _h₃, H₃₂⟩
    rw [← H₃₂]
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h)
#align finset.prod_powerset_insert Finset.prod_powerset_insert
#align finset.sum_powerset_insert Finset.sum_powerset_insert

/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`card s = k`, for `k = 1, ..., card s`. -/
@[to_additive
      "A sum over `powerset s` is equal to the double sum over sets of subsets of `s` with
      `card s = k`, for `k = 1, ..., card s`"]
theorem prod_powerset [CommMonoid β] (s : Finset α) (f : Finset α → β) :
    ∏ t in powerset s, f t = ∏ j in range (card s + 1), ∏ t in powersetCard j s, f t := by
  rw [powerset_card_disjiUnion, prod_disjiUnion]
#align finset.prod_powerset Finset.prod_powerset
#align finset.sum_powerset Finset.sum_powerset

theorem sum_range_succ_mul_sum_range_succ [NonUnitalNonAssocSemiring β] (n k : ℕ) (f g : ℕ → β) :
    ((∑ i in range (n + 1), f i) * ∑ i in range (k + 1), g i) =
      (((∑ i in range n, f i) * ∑ i in range k, g i) + f n * ∑ i in range k, g i) +
          (∑ i in range n, f i) * g k +
        f n * g k := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]
#align finset.sum_range_succ_mul_sum_range_succ Finset.sum_range_succ_mul_sum_range_succ

end Finset
