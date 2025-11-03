/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

assert_not_exists Field

open Fintype

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

namespace Finset

lemma prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι → M) :
    ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x := by
  simpa using (s.1.map f).prod_map_neg

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

lemma natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    (#{x ∈ s | p x} : R) = ∑ a ∈ s, if p a then (1 : R) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]

@[simp] lemma sum_boole (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then 1 else 0 : R) = #{x ∈ s | p x} :=
  (natCast_card_filter _ _).symm

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

lemma sum_mul (s : Finset ι) (f : ι → R) (a : R) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s

lemma mul_sum (s : Finset ι) (f : ι → R) (a : R) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := map_sum (AddMonoidHom.mulLeft a) _ s

lemma sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j := by
  simp_rw [sum_mul, ← mul_sum]

lemma _root_.Fintype.sum_mul_sum [Fintype ι] [Fintype κ] (f : ι → R) (g : κ → R) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j :=
  Finset.sum_mul_sum _ _ _ _

lemma _root_.Commute.sum_right (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i ∈ s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi

lemma _root_.Commute.sum_left (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i ∈ s, f i) b :=
  ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm

lemma sum_range_succ_mul_sum_range_succ (m n : ℕ) (f g : ℕ → R) :
    (∑ i ∈ range (m + 1), f i) * ∑ i ∈ range (n + 1), g i =
      (∑ i ∈ range m, f i) * ∑ i ∈ range n, g i +
        f m * ∑ i ∈ range n, g i + (∑ i ∈ range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {f : ι → R} {a : R}

lemma dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

end NonUnitalSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [DecidableEq ι]

lemma sum_mul_boole (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, f j * ite (i = j) 1 0 = ite (i ∈ s) (f i) 0 := by simp

lemma sum_boole_mul (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, ite (i = j) 1 0 * f j = ite (i ∈ s) (f i) 0 := by simp

end NonAssocSemiring

section CommSemiring
variable [CommSemiring R]

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq {s : Finset ι} {i : ι} {f g h : ι → R} (hi : i ∈ s)
    (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    (∏ i ∈ s, g i) + ∏ i ∈ s, h i = ∏ i ∈ s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

section DecidableEq
variable [DecidableEq ι]

/-- The product over a sum can be written as a sum over the product of sets, `Finset.Pi`.
  `Finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
lemma prod_sum {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) :
    ∏ a ∈ s, ∑ b ∈ t a, f a b = ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : ∀ x ∈ t a, ∀ y ∈ t a, x ≠ y →
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

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`Fintype.piFinset`. `Finset.prod_sum` is an alternative statement when the product is not
over `univ`. -/
lemma prod_univ_sum {κ : ι → Type*} [Fintype ι] (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) :
    ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i) := by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]

lemma sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι → κ → R) :
    ∑ f ∈ piFinset fun _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s, g i j := by
  rw [← prod_univ_sum]

lemma sum_pow' (s : Finset κ) (f : κ → R) (n : ℕ) :
    (∑ a ∈ s, f a) ^ n = ∑ p ∈ piFinset fun _i : Fin n ↦ s, ∏ i, f (p i) := by
  convert @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i ↦ s) fun _i d ↦ f d; simp

/-- The product of `f a + g a` over all of `s` is the sum over the powerset of `s` of the product of
`f` over a subset `t` times the product of `g` over the complement of `t` -/
theorem prod_add (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i := by
  classical
  calc
    ∏ i ∈ s, (f i + g i) =
        ∏ i ∈ s, ∑ p ∈ ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p ∈ (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a ∈ s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
    _ = ∑ t ∈ s.powerset, (∏ a ∈ t, f a) * ∏ a ∈ s \ t, g a :=
      sum_bij'
        (fun f _ ↦ {a ∈ s | ∃ h : a ∈ s, f a h})
        (fun t _ a _ => a ∈ t)
        (by simp)
        (by simp [Classical.em])
        (by simp_rw [mem_filter, funext_iff, eq_iff_iff, mem_pi, mem_insert]; tauto)
        (by simp_rw [Finset.ext_iff, @mem_filter _ _ (id _), mem_powerset]; tauto)
        (fun a _ ↦ by
          simp only [prod_ite, filter_attach', prod_map, Function.Embedding.coeFn_mk,
            Subtype.map_coe, id_eq, prod_attach]
          congr 2 with x
          simp only [mem_filter, mem_sdiff, not_and, not_exists, and_congr_right_iff]
          tauto)

end DecidableEq

theorem prod_one_add {f : ι → R} (s : Finset ι) :
    ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  classical simp only [add_comm (1 : R), prod_add, prod_const_one, mul_one]

theorem prod_add_one {f : ι → R} (s : Finset ι) :
    ∏ i ∈ s, (f i + 1) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  classical simp only [prod_add, prod_const_one, mul_one]

/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i + g i) =
      (∏ i ∈ s, f i) +
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j + g j)) * ∏ j ∈ s with i < j, f j := by
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
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_gt⟩
  · rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert, if_neg (ha i hi).not_gt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'

/-- Summing `a ^ #t * b ^ (n - #t)` over all finite subsets `t` of a finset `s`
gives `(a + b) ^ #s`. -/
theorem sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) :
    (∑ t ∈ s.powerset, a ^ #t * b ^ (#s - #t)) = (a + b) ^ #s := by
  classical
  rw [← prod_const, prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const, prod_const, ← card_sdiff_of_subset (mem_powerset.1 ht)]

/-- Summing `a^#s * b^(n-#s)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _

@[norm_cast]
theorem prod_natCast (s : Finset ι) (f : ι → ℕ) : ↑(∏ i ∈ s, f i : ℕ) = ∏ i ∈ s, (f i : R) :=
  map_prod (Nat.castRingHom R) f s

end CommSemiring

section CommRing
variable [CommRing R]

/-- The product of `f i - g i` over all of `s` is the sum over the powerset of `s` of the product of
`g` over a subset `t` times the product of `f` over the complement of `t` times `(-1) ^ #t`. -/
lemma prod_sub [DecidableEq ι] (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, (-1) ^ #t * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i := by
  simp [sub_eq_neg_add, prod_add, prod_neg, mul_right_comm]

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
lemma prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j - g j)) * ∏ j ∈ s with i < j, f j := by
  simp only [sub_eq_add_neg]
  convert prod_add_ordered s f fun i => -g i
  simp

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions. -/
theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 - f j) := by
  rw [prod_sub_ordered]
  simp

theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ range k, (n - i : R) = (∏ i ∈ range k, (n - i) : ℕ) := by
  rw [prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp

end CommRing
end Finset

open Finset

namespace Fintype
variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

lemma sum_pow (f : ι → R) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → ι, ∏ i, f (p i) := by
  simp [sum_pow']

variable [DecidableEq ι]

/-- A product of sums can be written as a sum of products. -/
lemma prod_sum {κ : ι → Type*} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → R) :
    ∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i) := Finset.prod_univ_sum _ _

lemma prod_add (f g : ι → R) : ∏ a, (f a + g a) = ∑ t, (∏ a ∈ t, f a) * ∏ a ∈ tᶜ, g a := by
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
lemma cast_list_sum [AddMonoidWithOne R] (s : List ℕ) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddMonoidHom R) _

@[simp, norm_cast]
lemma cast_list_prod [Semiring R] (s : List ℕ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
lemma cast_multiset_sum [AddCommMonoidWithOne R] (s : Multiset ℕ) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddMonoidHom R) _

@[simp, norm_cast]
lemma cast_multiset_prod [CommSemiring R] (s : Multiset ℕ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
lemma cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι → ℕ) :
    ↑(∑ x ∈ s, f x : ℕ) = ∑ x ∈ s, (f x : R) :=
  map_sum (castAddMonoidHom R) _ _

@[simp, norm_cast]
lemma cast_prod [CommSemiring R] (f : ι → ℕ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) :=
  map_prod (castRingHom R) _ _

end Nat

namespace Int
variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

@[simp, norm_cast]
lemma cast_list_sum [AddGroupWithOne R] (s : List ℤ) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddHom R) _

@[simp, norm_cast]
lemma cast_list_prod [Ring R] (s : List ℤ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
lemma cast_multiset_sum [AddCommGroupWithOne R] (s : Multiset ℤ) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddHom R) _

@[simp, norm_cast]
lemma cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset ℤ) :
    (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
lemma cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι → ℤ) :
    ↑(∑ x ∈ s, f x : ℤ) = ∑ x ∈ s, (f x : R) :=
  map_sum (castAddHom R) _ _

@[simp, norm_cast]
lemma cast_prod {R : Type*} [CommRing R] (f : ι → ℤ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) :=
  map_prod (Int.castRingHom R) _ _

end Int
