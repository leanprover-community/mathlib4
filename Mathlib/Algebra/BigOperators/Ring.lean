/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.big_operators.ring from "leanprover-community/mathlib"@"b2c89893177f66a48daf993b7ba5ef7cddeff8c9"

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

open Fintype

variable {ι α β γ : Type*} {κ : ι → Type*} {s s₁ s₂ : Finset ι} {i : ι} {a : α} {f g : ι → α}

#align monoid_hom.map_prod map_prod
#align add_monoid_hom.map_sum map_sum
#align mul_equiv.map_prod map_prod
#align add_equiv.map_sum map_sum
#align ring_hom.map_list_prod map_list_prod
#align ring_hom.map_list_sum map_list_sum
#align ring_hom.unop_map_list_prod unop_map_list_prod
#align ring_hom.map_multiset_prod map_multiset_prod
#align ring_hom.map_multiset_sum map_multiset_sum
#align ring_hom.map_prod map_prod
#align ring_hom.map_sum map_sum

namespace Finset

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne α]

lemma natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    ((filter p s).card : α) = ∑ a ∈ s, if p a then (1 : α) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
#align finset.nat_cast_card_filter Finset.natCast_card_filter

@[simp] lemma sum_boole (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then 1 else 0 : α) = (s.filter p).card :=
  (natCast_card_filter _ _).symm
#align finset.sum_boole Finset.sum_boole

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring α]

lemma sum_mul (s : Finset ι) (f : ι → α) (a : α) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s
#align finset.sum_mul Finset.sum_mul

lemma mul_sum (s : Finset ι) (f : ι → α) (a : α) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := map_sum (AddMonoidHom.mulLeft a) _ s
#align finset.mul_sum Finset.mul_sum

lemma sum_mul_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j := by
  simp_rw [sum_mul, ← mul_sum]
#align finset.sum_mul_sum Finset.sum_mul_sum

lemma _root_.Commute.sum_right [NonUnitalNonAssocSemiring α] (s : Finset ι) (f : ι → α) (b : α)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i ∈ s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi
#align commute.sum_right Commute.sum_right

lemma _root_.Commute.sum_left [NonUnitalNonAssocSemiring α] (s : Finset ι) (f : ι → α) (b : α)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i ∈ s, f i) b :=
  ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm
#align commute.sum_left Commute.sum_left

lemma sum_range_succ_mul_sum_range_succ (m n : ℕ) (f g : ℕ → α) :
    (∑ i ∈ range (m + 1), f i) * ∑ i ∈ range (n + 1), g i =
      (∑ i ∈ range m, f i) * ∑ i ∈ range n, g i +
        f m * ∑ i ∈ range n, g i + (∑ i ∈ range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]
#align finset.sum_range_succ_mul_sum_range_succ Finset.sum_range_succ_mul_sum_range_succ

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring α]

lemma dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx
#align finset.dvd_sum Finset.dvd_sum

end NonUnitalSemiring

section NonAssocSemiring
variable [NonAssocSemiring α] [DecidableEq ι]

lemma sum_mul_boole (s : Finset ι) (f : ι → α) (i : ι) :
    ∑ j ∈ s, f j * ite (i = j) 1 0 = ite (i ∈ s) (f i) 0 := by simp
#align finset.sum_mul_boole Finset.sum_mul_boole

lemma sum_boole_mul (s : Finset ι) (f : ι → α) (i : ι) :
    ∑ j ∈ s, ite (i = j) 1 0 * f j = ite (i ∈ s) (f i) 0 := by simp
#align finset.sum_boole_mul Finset.sum_boole_mul

end NonAssocSemiring

section CommSemiring
variable [CommSemiring α]

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq {s : Finset ι} {i : ι} {f g h : ι → α} (hi : i ∈ s)
    (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    (∏ i ∈ s, g i) + ∏ i ∈ s, h i = ∏ i ∈ s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa
#align finset.prod_add_prod_eq Finset.prod_add_prod_eq

section DecidableEq
variable [DecidableEq ι]

/-- The product over a sum can be written as a sum over the product of sets, `Finset.Pi`.
  `Finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
lemma prod_sum (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    ∏ a ∈ s, ∑ b ∈ t a, f a b = ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2) := by
  classical
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
    refine sum_congr rfl fun b _ => ?_
    have h₂ : ∀ p₁ ∈ pi s t, ∀ p₂ ∈ pi s t, Pi.cons s a b p₁ = Pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Pi.cons_injective ha eq
    rw [sum_image h₂, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [attach_insert, prod_insert, prod_image]
    · simp only [Pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (Pi.cons_ne (by rintro rfl; exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.eq ∘ Subtype.mk.inj
    · simpa only [mem_image, mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, exists_prop, exists_eq_right] using ha
#align finset.prod_sum Finset.prod_sum

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`Fintype.piFinset`. `Finset.prod_sum` is an alternative statement when the product is not
over `univ`. -/
lemma prod_univ_sum [Fintype ι] (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → α) :
    ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i) := by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]
#align finset.prod_univ_sum Finset.prod_univ_sum

lemma sum_prod_piFinset {κ : Type*} [Fintype ι] (s : Finset κ) (g : ι → κ → α) :
    ∑ f ∈ piFinset fun _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s, g i j := by
  rw [← prod_univ_sum]

lemma sum_pow' (s : Finset ι) (f : ι → α) (n : ℕ) :
    (∑ a ∈ s, f a) ^ n = ∑ p ∈ piFinset fun _i : Fin n ↦ s, ∏ i, f (p i) := by
  convert @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i ↦ s) fun _i d ↦ f d; simp

/-- The product of `f a + g a` over all of `s` is the sum over the powerset of `s` of the product of
`f` over a subset `t` times the product of `g` over the complement of `t`  -/
theorem prod_add (f g : ι → α) (s : Finset ι) :
    ∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i := by
  classical
  calc
    ∏ i ∈ s, (f i + g i) =
        ∏ i ∈ s, ∑ p ∈ ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p ∈ (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a ∈ s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
    _ = ∑ t ∈ s.powerset, (∏ a ∈ t, f a) * ∏ a ∈ s \ t, g a :=
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

end DecidableEq

/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered [LinearOrder ι] [CommSemiring α] (s : Finset ι) (f g : ι → α) :
    ∏ i ∈ s, (f i + g i) =
      (∏ i ∈ s, f i) +
        ∑ i ∈ s,
          g i * (∏ j ∈ s.filter (· < i), (f j + g j)) * ∏ j ∈ s.filter fun j => i < j, f j := by
  refine Finset.induction_on_max s (by simp) ?_
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
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert, if_neg (ha i hi).not_lt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'
#align finset.prod_add_ordered Finset.prod_add_ordered

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `Finset`
gives `(a + b)^s.card`. -/
theorem sum_pow_mul_eq_add_pow (a b : α) (s : Finset ι) :
    (∑ t ∈ s.powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card := by
  classical
  rw [← prod_const, prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]
#align finset.sum_pow_mul_eq_add_pow Finset.sum_pow_mul_eq_add_pow

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : α) :
    ∑ s : Finset ι, a ^ s.card * b ^ (Fintype.card ι - s.card) = (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _
#align fintype.sum_pow_mul_eq_add_pow Fintype.sum_pow_mul_eq_add_pow

@[norm_cast]
theorem prod_natCast (s : Finset ι) (f : ι → ℕ) : ↑(∏ i ∈ s, f i : ℕ) = ∏ i ∈ s, (f i : α) :=
  map_prod (Nat.castRingHom α) f s
#align finset.prod_nat_cast Finset.prod_natCast

end CommSemiring

section CommRing
variable [CommRing α]

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
lemma prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → α) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s,
          g i * (∏ j ∈ s.filter (· < i), (f j - g j)) * ∏ j ∈ s.filter fun j => i < j, f j := by
  simp only [sub_eq_add_neg]
  convert prod_add_ordered s f fun i => -g i
  simp
#align finset.prod_sub_ordered Finset.prod_sub_ordered

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions.  -/
theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s.filter (· < i), (1 - f j) := by
  rw [prod_sub_ordered]
  simp
#align finset.prod_one_sub_ordered Finset.prod_one_sub_ordered

theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ range k, (n - i : α) = (∏ i ∈ range k, (n - i) : ℕ) := by
  rw [prod_natCast]
  rcases le_or_lt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp
#align finset.prod_range_cast_nat_sub Finset.prod_range_natCast_sub

@[deprecated (since := "2024-05-27")] alias prod_range_cast_nat_sub := prod_range_natCast_sub


end CommRing

section DivisionSemiring
variable [DivisionSemiring α]

lemma sum_div (s : Finset ι) (f : ι → α) (a : α) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]
#align finset.sum_div Finset.sum_div

end DivisionSemiring
end Finset

open Finset

namespace Fintype
variable {ι κ α : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ] [CommSemiring α]

lemma sum_pow (f : ι → α) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → ι, ∏ i, f (p i) := by
  simp [sum_pow']

lemma sum_mul_sum (f : ι → α) (g : κ → α) : (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j :=
  Finset.sum_mul_sum _ _ _ _

lemma prod_add (f g : ι → α) : ∏ a, (f a + g a) = ∑ t, (∏ a ∈ t, f a) * ∏ a ∈ tᶜ, g a := by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

end Fintype

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [Nat.div_mul_cancel (hf _ hs)]

@[simp, norm_cast]
lemma cast_list_sum [AddMonoidWithOne β] (s : List ℕ) : (↑s.sum : β) = (s.map (↑)).sum :=
  map_list_sum (castAddMonoidHom β) _
#align nat.cast_list_sum Nat.cast_list_sum

@[simp, norm_cast]
lemma cast_list_prod [Semiring β] (s : List ℕ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_list_prod (castRingHom β) _
#align nat.cast_list_prod Nat.cast_list_prod

@[simp, norm_cast]
lemma cast_multiset_sum [AddCommMonoidWithOne β] (s : Multiset ℕ) :
    (↑s.sum : β) = (s.map (↑)).sum :=
  map_multiset_sum (castAddMonoidHom β) _
#align nat.cast_multiset_sum Nat.cast_multiset_sum

@[simp, norm_cast]
lemma cast_multiset_prod [CommSemiring β] (s : Multiset ℕ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom β) _
#align nat.cast_multiset_prod Nat.cast_multiset_prod

@[simp, norm_cast]
lemma cast_sum [AddCommMonoidWithOne β] (s : Finset α) (f : α → ℕ) :
    ↑(∑ x ∈ s, f x : ℕ) = ∑ x ∈ s, (f x : β) :=
  map_sum (castAddMonoidHom β) _ _
#align nat.cast_sum Nat.cast_sum

@[simp, norm_cast]
lemma cast_prod [CommSemiring β] (f : α → ℕ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : β) = ∏ i ∈ s, (f i : β) :=
  map_prod (castRingHom β) _ _
#align nat.cast_prod Nat.cast_prod

end Nat

namespace Int

@[simp, norm_cast]
lemma cast_list_sum [AddGroupWithOne β] (s : List ℤ) : (↑s.sum : β) = (s.map (↑)).sum :=
  map_list_sum (castAddHom β) _
#align int.cast_list_sum Int.cast_list_sum

@[simp, norm_cast]
lemma cast_list_prod [Ring β] (s : List ℤ) : (↑s.prod : β) = (s.map (↑)).prod :=
  map_list_prod (castRingHom β) _
#align int.cast_list_prod Int.cast_list_prod

@[simp, norm_cast]
lemma cast_multiset_sum [AddCommGroupWithOne β] (s : Multiset ℤ) :
    (↑s.sum : β) = (s.map (↑)).sum :=
  map_multiset_sum (castAddHom β) _
#align int.cast_multiset_sum Int.cast_multiset_sum

@[simp, norm_cast]
lemma cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset ℤ) :
    (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _
#align int.cast_multiset_prod Int.cast_multiset_prod

@[simp, norm_cast]
lemma cast_sum [AddCommGroupWithOne β] (s : Finset α) (f : α → ℤ) :
    ↑(∑ x ∈ s, f x : ℤ) = ∑ x ∈ s, (f x : β) :=
  map_sum (castAddHom β) _ _
#align int.cast_sum Int.cast_sum

@[simp, norm_cast]
lemma cast_prod {R : Type*} [CommRing R] (f : α → ℤ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) :=
  map_prod (Int.castRingHom R) _ _
#align int.cast_prod Int.cast_prod

end Int
