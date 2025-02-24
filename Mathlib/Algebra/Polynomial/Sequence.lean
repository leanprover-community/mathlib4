/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
import Mathlib.Algebra.Ring.Regular
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Basis.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

open Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

instance [Semiring R] [IsCancelAdd R] : IsCancelAdd (Polynomial R) := by
  refine @AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _ _ (.mk fun p q r h ↦ ?_)
  ext n
  simp_rw [ext_iff, coeff_add] at h
  exact (add_right_inj _).1 (h n)

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  /-- The `i`'th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`'th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦  ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
@[simp]
lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := natDegree_eq_of_degree_eq_some <| S.degree_eq i

/-- No polynomial in the sequence is zero. -/
@[simp]
lemma ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp <| by simp [S.degree_eq i]

/-- `S i` has strictly monotone degree. -/
lemma degree_strictMono : StrictMono <| degree ∘ S := fun _ _  ↦ by simp

/-- `S i` has strictly monotone natural degree. -/
lemma natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _  ↦ by simp

end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ :=
  eq_top_iff'.mpr fun P ↦ by
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases p_ne_zero : P = 0
    · simp [p_ne_zero]

    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n

    let head := P.leadingCoeff • u • S n
    let tail := P - head

    have head_mem_span : head ∈ span R (Set.range S) := by
      have in_span : S n ∈ span R (Set.range S) := subset_span (by simp)
      have smul_span := smul_mem (span R (Set.range S)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span

    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    refine sub_mem_iff_left _ head_mem_span |>.mp <| ih tail.natDegree ?_ _ rfl

    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular _ <| IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right

    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff

    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n).isRegular.right
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
        ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq

    have head_nonzero : head ≠ 0 := by
      by_cases n_eq_zero : n = 0
      · rw [n_eq_zero, ← coeff_natDegree, natDegree_eq] at rightinv
        dsimp [head]
        rwa [n_eq_zero, eq_C_of_natDegree_eq_zero <| S.natDegree_eq 0,
          smul_C, smul_eq_mul, map_mul, ← C_mul, rightinv, smul_C, smul_eq_mul,
          mul_one, C_eq_zero, leadingCoeff_eq_zero]
      · apply head.ne_zero_of_degree_gt
        rw [← head_degree_eq]
        exact natDegree_pos_iff_degree_pos.mp (by omega)

    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree, degree_eq_natDegree head_nonzero] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rwa [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]

    refine natDegree_lt_iff_degree_lt tail_eq_zero |>.mpr ?_
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

section NoZeroDivisors

variable [NoZeroDivisors R]

section Test

open Finsupp

variable {R : Type*} [Semiring R] [NoZeroDivisors R]

lemma _root_.Polynomial.leadingCoeff_smul (p : Polynomial R) {k : R} (h : k ≠ 0) :
    (k • p).leadingCoeff = k * p.leadingCoeff := by
  rw [← coeff_natDegree, ← coeff_natDegree, natDegree_smul _ h, coeff_smul, smul_eq_mul]

variable {R : Type*} [Semiring R] [IsRightCancelMulZero R]

instance : NoZeroDivisors R where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    rw [← zero_mul b] at h
    obtain rfl | hb := eq_or_ne b 0
    · simp
    · exact Or.inl (mul_right_cancel₀ hb h)

class IsRightCancelSMulZero (R M : Type*) [SMul R M] [Zero M] : Prop where
  smul_right_cancel_of_ne_zero : ∀ {a b : R}, ∀ {c : M}, c ≠ 0 → a • c = b • c → a = b

instance : IsRightCancelSMulZero R (Polynomial R) where
  smul_right_cancel_of_ne_zero := by
    intro a b p hp h
    apply mul_right_cancel₀ (b := p.leadingCoeff)
    · rwa [p.leadingCoeff_ne_zero]
    obtain rfl | ha := eq_or_ne a 0 <;> obtain rfl | hb := eq_or_ne b 0
    · simp
    · rw [← leadingCoeff_smul _ hb, ← h]
      simp
    · rw [← leadingCoeff_smul _ ha, h]
      simp
    · rw [← leadingCoeff_smul _ ha, ← leadingCoeff_smul _ hb, h]

variable (S : Sequence R)

lemma _root_.Finset.Nonempty.sup_id_mem {α : Type*} [LinearOrder α] [OrderBot α] {s : Finset α}
    (hs : s.Nonempty) : s.sup id ∈ s := by
  rw [← Finset.mem_coe, ← Set.image_id s.toSet]
  exact Finset.sup_mem_of_nonempty hs

lemma _root_.Finset.lt_sup_of_mem_erase {α : Type*} [LinearOrder α] [OrderBot α]
    {s : Finset α} {a : α} (h : a ∈ s.erase (s.sup id)) : a < s.sup id :=
  lt_iff_le_and_ne.2 ⟨id_eq a ▸ Finset.le_sup (Finset.erase_subset _ _ h), Finset.ne_of_mem_erase h⟩


lemma _root_.Finsupp.erase_apply_of_ne {α M : Type*} [DecidableEq α] [Zero M] {a b : α} (h : a ≠ b)
    (f : α →₀ M) : f.erase a b = f b := by
  rw [erase_apply, if_neg h.symm]

@[simp]
lemma _root_.Finsupp.linearCombination_support_empty {α M R : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (v : α → M) {l : α →₀ R} (hl : l.support = ∅) :
    l.linearCombination R v = 0 := by
  simp [Finsupp.support_eq_empty.1 hl]

theorem leadingCoeff_add_of_natDegree_lt {R : Type*} [Semiring R] (p q : Polynomial R)
    (h : natDegree p < natDegree q) : leadingCoeff (p + q) = leadingCoeff q :=
  leadingCoeff_add_of_degree_lt (degree_lt_degree h)

theorem leadingCoeff_add_of_natDegree_lt' {R : Type*} [Semiring R] (p q : Polynomial R)
    (h : natDegree q < natDegree p) : leadingCoeff (p + q) = leadingCoeff p :=
  leadingCoeff_add_of_degree_lt' (degree_lt_degree h)

variable {a b : ℕ →₀ R}

lemma natDegree_linearCombination : (a.linearCombination R S).natDegree = a.support.sup id := by
  obtain ha | ha := Finset.eq_empty_or_nonempty a.support
  · simp [ha]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have : a.support.sup id = a.support.sup (fun i ↦ ((a i) • (S i)).natDegree) := by
    refine Finset.sup_congr rfl fun i hi ↦ ?_
    rw [natDegree_smul _ (Finsupp.mem_support_iff.1 hi)]
    simp
  rw [this]
  apply Polynomial.natDegree_sum_eq_of_disjoint
  rintro i ⟨-, hi⟩ j ⟨-, hj⟩ hij
  simp only [ne_eq, Function.comp_apply]
  rw [natDegree_smul _ (smul_ne_zero_iff.1 hi).1, natDegree_smul _ (smul_ne_zero_iff.1 hj).1]
  simpa

lemma leadingCoeff_linearCombination : (a.linearCombination R S).leadingCoeff =
    (a (a.support.sup id)) * (S (a.support.sup id)).leadingCoeff := by
  obtain ha | ha := Finset.eq_empty_or_nonempty a.support
  · simp [Finsupp.support_eq_empty.1 ha]
  rw [linearCombination_apply, ← add_sum_erase _ (a.support.sup id),
    leadingCoeff_add_of_degree_lt', leadingCoeff_smul]
  · exact Finsupp.mem_support_iff.1 ha.sup_id_mem
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff ?_).2 fun i hi ↦ ?_)
    · rw [degree_eq_natDegree, natDegree_smul]
      · exact WithBot.bot_lt_coe _
      · exact Finsupp.mem_support_iff.1 ha.sup_id_mem
      · exact smul_ne_zero (Finsupp.mem_support_iff.1 ha.sup_id_mem) (S.ne_zero _)
    rw [degree_eq_natDegree, degree_eq_natDegree, natDegree_smul, S.natDegree_eq,
      natDegree_smul, S.natDegree_eq]
    · norm_cast
      rw [Finsupp.support_erase] at hi
      exact Finset.lt_sup_of_mem_erase hi
    · exact Finsupp.mem_support_iff.1 ha.sup_id_mem
    · exact Finsupp.mem_support_iff.1 hi
    · exact smul_ne_zero (Finsupp.mem_support_iff.1 ha.sup_id_mem) (S.ne_zero _)
    · exact smul_ne_zero (Finsupp.mem_support_iff.1 hi) (S.ne_zero _)
  · exact ha.sup_id_mem

lemma support_eq_empty_iff (h : a.linearCombination R S = b.linearCombination R S) :
    a.support = ∅ ↔ b.support = ∅ := by
  suffices ∀ (a b : ℕ →₀ R), a.linearCombination R S = b.linearCombination R S →
    a.support = ∅ → b.support = ∅ from ⟨this a b h, this b a h.symm⟩
  intro a b h ha
  rw [linearCombination_support_empty S ha] at h
  by_contra!
  rw [← Finset.nonempty_iff_ne_empty] at this
  have := (leadingCoeff_linearCombination S (a := b)).symm
  rw [← h, leadingCoeff_zero, mul_eq_zero] at this
  obtain h' | h' := this
  · exact Finsupp.mem_support_iff.1 this.sup_id_mem h'
  · exact leadingCoeff_ne_zero.2 (S.ne_zero _) h'

lemma support_nonempty_iff (h : a.linearCombination R S = b.linearCombination R S) :
    a.support.Nonempty ↔ b.support.Nonempty := by
  simp_rw [Finset.nonempty_iff_ne_empty]
  exact (support_eq_empty_iff S h).ne

lemma support_sup_eq (h : a.linearCombination R S = b.linearCombination R S) :
    a.support.sup id = b.support.sup id := by
  obtain ha | ha := Finset.eq_empty_or_nonempty a.support
  · rw [ha, (support_eq_empty_iff S h).1 ha]
  · rw [← natDegree_linearCombination S, ← natDegree_linearCombination S, h]

lemma apply_support_sup_eq (h : a.linearCombination R S = b.linearCombination R S) :
    a (a.support.sup id) = b (b.support.sup id) := by
  obtain ha | ha := Finset.eq_empty_or_nonempty a.support
  · rw [Finsupp.support_eq_empty.1 ha,
      Finsupp.support_eq_empty.1 <| (support_eq_empty_iff S h).1 ha]
  apply mul_right_cancel₀ (leadingCoeff_ne_zero.2 (S.ne_zero (a.support.sup id)))
  nth_rw 3 [support_sup_eq S h]
  rw [← leadingCoeff_linearCombination, ← leadingCoeff_linearCombination, h]

variable [IsCancelAdd R]

lemma erase_linearCombination_eq (h : a.linearCombination R S = b.linearCombination R S) :
    (a.erase (a.support.sup id)).linearCombination R S =
    (b.erase (b.support.sup id)).linearCombination R S := by
  obtain has | has := Finset.eq_empty_or_nonempty a.support
  · simp [has, (support_eq_empty_iff S h).1 has]
  have h' := h
  rw [linearCombination_apply, linearCombination_apply,
    ←  Finsupp.add_sum_erase a (a.support.sup id), ←  Finsupp.add_sum_erase b (b.support.sup id),
    ← linearCombination_apply, ← linearCombination_apply] at h
  · apply add_left_cancel (a := b (b.support.sup id) • S (b.support.sup id))
    nth_rw 1 [← apply_support_sup_eq S h', ← support_sup_eq S h']
    exact h
  · exact ((support_nonempty_iff S h').1 has).sup_id_mem
  · exact has.sup_id_mem

lemma Finset.not_mem_of_sup_lt {α : Type*} [SemilatticeSup α] [OrderBot α] {s : Finset α}
    {a : α} (ha : s.sup id < a) : a ∉ s :=
  fun h ↦ lt_irrefl a <| lt_of_le_of_lt (id_eq a ▸ Finset.le_sup h) ha

lemma linearIndependent {R : Type*} [Semiring R] [IsCancelAdd R] [IsRightCancelMulZero R]
    (S : Sequence R) : LinearIndependent R S := by
  intro a b h
  generalize n_def : a.support.sup id = n
  induction n using Nat.case_strong_induction_on generalizing a b with
  | hz =>
    obtain has | has := Finset.eq_empty_or_nonempty a.support
    · rw [Finsupp.support_eq_empty.1 has,
        Finsupp.support_eq_empty.1 <| support_eq_empty_iff S h |>.1 has]
    have a_sup := n_def
    have b_supp := support_sup_eq S h ▸ n_def
    have b_sup := b_supp
    have hbs := (support_nonempty_iff S h).1 has
    rw [← bot_eq_zero, Finset.sup_eq_bot_iff] at n_def b_supp
    have as : a.support = {0} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨a_sup ▸ has.sup_id_mem, n_def⟩
    have bs : b.support = {0} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨b_sup ▸ hbs.sup_id_mem, b_supp⟩
    rw [linearCombination_apply, Finsupp.sum, linearCombination_apply, Finsupp.sum, as, bs,
      Finset.sum_singleton, Finset.sum_singleton] at h
    ext i
    obtain rfl | hi := eq_or_ne i 0
    · exact IsRightCancelSMulZero.smul_right_cancel_of_ne_zero (S.ne_zero 0) h
    · rw [Finsupp.not_mem_support_iff.1, Finsupp.not_mem_support_iff.1] <;> simp_all
  | hi n hind =>
    ext i
    obtain hi | hi := le_or_lt i (n + 1)
    · obtain hi | rfl := le_iff_lt_or_eq.1 hi
      · suffices a.erase (a.support.sup id) = b.erase (a.support.sup id) by
          rw [← erase_apply_of_ne hi.ne.symm, ← erase_apply_of_ne (f := b) hi.ne.symm,
            ← n_def, this]
        refine hind ((a.erase (a.support.sup id)).support.sup id) ?_ ?_ rfl
        · rw [Nat.le_iff_lt_add_one, ← n_def, Finset.sup_lt_iff]
          · intro j hj
            rw [Finsupp.support_erase] at hj
            exact Finset.lt_sup_of_mem_erase hj
          · simp [n_def]
        · nth_rw 2 [support_sup_eq S h]
          exact erase_linearCombination_eq S h
      · rw [← n_def]
        nth_rw 2 [support_sup_eq S h]
        exact apply_support_sup_eq S h
    · rw [Finsupp.not_mem_support_iff.1, Finsupp.not_mem_support_iff.1]
      · rw [← n_def, support_sup_eq S h] at hi
        exact Finset.not_mem_of_sup_lt hi
      · rw [← n_def] at hi
        exact Finset.not_mem_of_sup_lt hi

end Test

/-- Polynomials in a polynomial sequence are linearly independent. -/
lemma linearIndependent' :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  by_cases hsupzero : s.sup (fun i ↦ (g i • S i).degree) = ⊥
  · have le_sup := Finset.le_sup hi (f := fun i ↦ (g i • S i).degree)
    exact (smul_eq_zero_iff_left (S.ne_zero i)).mp <| degree_eq_bot.mp (eq_bot_mono le_sup hsupzero)
  have hpairwise : {i | i ∈ s ∧ g i • S i ≠ 0}.Pairwise (Ne on fun i ↦ (g i • S i).degree) := by
    intro x ⟨_, hx⟩ y ⟨_, hy⟩ xney
    have zgx : g x ≠ 0 := (smul_ne_zero_iff.mp hx).1
    have zgy : g y ≠ 0 := (smul_ne_zero_iff.mp hy).1
    have rx : IsRightRegular (S x).leadingCoeff := isRegular_of_ne_zero (by simp) |>.right
    have ry : IsRightRegular (S y).leadingCoeff := isRegular_of_ne_zero (by simp) |>.right
    simp [degree_smul_of_isRightRegular_leadingCoeff, rx, ry, zgx, zgy, xney]
  obtain ⟨n, hn⟩ : ∃ n, (s.sup fun i ↦ (g i • S i).degree) = n := exists_eq'
  refine degree_ne_bot.mp ?_ eqzero |>.elim
  have hsum := degree_sum_eq_of_disjoint _ s hpairwise
  exact hsum.trans hn |>.trans_ne <| (ne_of_ne_of_eq (hsupzero ·.symm) hn).symm

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`'th basis vector is the `i`'th polynomial in the sequence. -/
@[simp]
lemma basis_eq_self  (i : ℕ) : S.basis hCoeff i = S i := Basis.mk_apply _ _ _

/-- Basis elements have strictly monotone degree. -/
lemma basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _  ↦ by simp

/-- Basis elements have strictly monotone natural degree. -/
lemma basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _  ↦ by simp

end NoZeroDivisors

end Ring

end Sequence

end Polynomial
