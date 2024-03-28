/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.ToFinsupp
import Mathlib.Data.Polynomial.Degree.Lemmas


/-!

# Lists as polynomials

Constructing polynomials by providing an explicit list of coefficients.

## Main definitions

- `ofList l`: a `l : List R` defines a `Polynomial R` by setting the coefficients, from least to
  greatest
- `toList p`: a `p : Polynomial R` defines a `List R` as its coefficients, from least to greatest,
  up to and including its `p.natDegree`
- `embed_list`: all lists that do not terminate in a `0 : R` can be embedded into `Polynomial R`
  via `ofList`

## Main theorems

- `ofList_toList`: constructing a polynomial from a polynomial's coefficients is the identity
- `toList_ofList`: lists that do not terminate in a `0 : R` can be reconstructed from the
  polynomials they induce
- `surjective_ofList`: every `p : Polynomial R` has at least one `List R` such that
  the list can form the polynomial, and the list's length is the `p.natDegree - 1`.

-/

open scoped Classical
noncomputable section

namespace List

variable {α : Type _}

theorem getD_ofFn (d : α) {n : ℕ} (f : Fin n → α) (i : ℕ) :
    getD (ofFn f) i d = if hi : i < n then f ⟨i, hi⟩ else d := by
  split_ifs with h
  · rw [List.getD_eq_nthLe, List.nthLe_ofFn']
    simpa using h
  · rw [getD_eq_default]
    simpa using h

end List

namespace Polynomial

variable {R S : Type _} [Semiring R] (l : List R)

section

/-- A `l : List R` over a `Semiring R` defines a polynomial with the elements as coefficients.
A generalization of `polynomial.ofList_lt`. -/
def ofList : Polynomial R :=
  ofFinsupp l.toFinsupp

@[simp]
theorem coeff_ofList (i : ℕ) : (ofList l).coeff i = l.getD i 0 :=
  rfl

@[simp]
theorem ofList_nil [DecidablePred fun i : ℕ => List.getD ([] : List R) i 0 ≠ 0] :
    ofList ([] : List R) = 0 :=
  rfl

@[simp]
theorem ofList_cons (x : R) (xs : List R) [DecidablePred fun i : ℕ => List.getD (x::xs) i 0 ≠ 0]
    [DecidablePred fun i : ℕ => List.getD xs i 0 ≠ 0] : ofList (x::xs) = C x + X * ofList xs := by
  ext (_ | i) <;> simp [coeff_C]

@[simp]
theorem ofList_concat (x : R) (xs : List R) :
    ofList (xs ++ [x]) = ofList xs + monomial xs.length x := by
  induction' xs with y xs IH generalizing x
  · classical
    rw [add_comm]
    convert ofList_cons x [] using 2
    simp
  · simp [IH, mul_add, add_assoc]

@[simp]
theorem ofList_append (xs ys : List R) :
    ofList (xs ++ ys) = ofList xs + X ^ xs.length * ofList ys := by
  induction' ys using List.reverseRecOn with ys y IH generalizing xs
  · simp
  · simp_rw [← List.append_assoc]
    simp only [ofList_concat, IH, add_comm, List.length_append, add_assoc, mul_add,
      X_pow_mul_monomial]
    abel

-- decidable_eq here is too powerful, we don't have a pfilter
@[simp]
theorem support_ofList {R} [Semiring R] (l : List R) :
    (ofList l).support = (l.enum.toFinset.filter fun p : ℕ × R => p.2 ≠ 0).image Prod.fst := by
  ext i
  simp only [List.mem_iff_nthLe, mem_support_iff, coeff_ofList, Ne.def, Finset.mem_image,
    Finset.mem_filter, List.mem_toFinset, exists_prop, Prod.exists, exists_and_right,
    exists_eq_right]
  constructor
  · intro h
    have hi : i < l.length := by
      contrapose! h
      exact List.getD_eq_default _ _ h
    refine' ⟨l.nthLe i hi, ⟨⟨i, _, _⟩, _⟩⟩
    · simpa [List.enum_length] using hi
    · exact List.nthLe_enum _ _ _
    · rwa [← List.getD_eq_nthLe _ 0 hi]
  · rintro ⟨x, ⟨⟨n, hn, h⟩, hx⟩⟩
    rw [List.nthLe_enum, Prod.mk.inj_iff] at h
    rcases h with ⟨rfl, h⟩
    rw [List.enum_length] at hn
    rwa [List.getD_eq_nthLe _ 0 hn, h]

theorem ofList_eq_sum_map_monomial_enum :
    ofList l = (l.enum.map fun p : ℕ × R => monomial p.1 p.2).sum := by
  induction' l using List.reverseRecOn with xs x IH
  · simp
  · simp [List.enum_append, List.enumFrom_cons, IH, ← C_mul_X_pow_eq_monomial]

theorem ofList_eq_zero_iff {l : List R} [DecidablePred fun i : ℕ => List.getD l i 0 ≠ 0] :
    ofList l = 0 ↔ ∀ x : R, x ∈ l → x = 0 := by
  simp_rw [List.mem_iff_nthLe]
  constructor
  · simp (config := { contextual := true }) [← l.getD_eq_nthLe 0, ← coeff_ofList]
  · intro h
    ext n
    cases' le_or_lt l.length n with hn hn
    · simp [l.getD_eq_default _ hn]
    · rw [coeff_ofList, l.getD_eq_nthLe _ hn, coeff_zero, h (l.nthLe n hn)]
      exact ⟨_, _, rfl⟩

theorem natDegree_ofList_le : natDegree (ofList l) ≤ l.length := by
  induction' l using List.reverseRecOn with xs x IH
  · simp
  classical
  simp only [ofList_append, ofList_cons, ofList_nil, MulZeroClass.mul_zero, add_zero,
    X_pow_mul_C, List.length_append, List.length_singleton]
  refine (natDegree_add_le _ _).trans ?_
  rw [max_le_iff]
  exact ⟨Nat.le_succ_of_le IH, Nat.le_succ_of_le (natDegree_C_mul_X_pow_le _ _)⟩

theorem natDegree_ofList_lt (h : l ≠ []) : natDegree (ofList l) < l.length := by
  induction' l using List.reverseRecOn with xs x IH
  · exact absurd rfl h
  classical
  simp only [ofList_append, ofList_cons, ofList_nil, MulZeroClass.mul_zero, add_zero,
    X_pow_mul_C, List.length_append, List.length_singleton]
  refine' (natDegree_add_le _ _).trans_lt _
  rw [max_lt_iff]
  refine' ⟨_, Nat.lt_succ_of_le (natDegree_C_mul_X_pow_le _ _)⟩
  cases xs
  · simp
  · exact Nat.lt_succ_of_lt (IH (List.cons_ne_nil _ _))

theorem degree_ofList_lt : degree (ofList l) < l.length := by
  by_cases h : ofList l = 0
  · simpa [h] using WithBot.bot_lt_coe _
  · rw [← natDegree_lt_iff_degree_lt h]
    refine' natDegree_ofList_lt _ _
    contrapose! h
    simp [ofList_eq_zero_iff, h]

theorem natDegree_ofList_of_getLast_ne_zero (h : ∀ hl : l ≠ [], l.getLast hl ≠ 0) :
    natDegree (ofList l) = l.length - 1 := by
  induction' l using List.reverseRecOn with xs x IH
  · simp
  classical
  specialize h _
  · rw [← List.concat_eq_append']
    exact List.concat_ne_nil _ _
  cases xs
  · simp
  have hx : x ≠ 0 := by simpa using h
  simp only [ofList_append, ofList_cons x, ofList_nil, MulZeroClass.mul_zero, add_zero,
    X_pow_mul_C, List.length_append, List.length_singleton, Nat.add_succ_sub_one]
  rw [natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ hx]
  exact natDegree_ofList_lt _ (List.cons_ne_nil _ _)

theorem natDegree_ofList_of_getD_length_sub_one_ne_zero (h : l.getD (l.length - 1) 0 ≠ 0) :
    natDegree (ofList l) = l.length - 1 := by
  refine' natDegree_ofList_of_getLast_ne_zero _ _
  intro hl
  rwa [List.getLast_eq_nthLe, ← List.getD_eq_nthLe _ (0 : R)]

theorem ofList_inj_on (l' : List R) [DecidablePred fun i : ℕ => List.getD l' i 0 ≠ 0]
    (hl : l.getD (l.length - 1) 0 ≠ 0) (hl' : l'.getD (l'.length - 1) 0 ≠ 0)
    (h : ofList l = ofList l') : l = l' := by
  refine' List.ext_nthLe _ _
  · cases' l with hd tl
    · simp at hl
    cases' l' with hd' tl'
    · simp at hl'
    suffices (hd::tl).length - 1 = (hd'::tl').length - 1 by refine' Nat.pred_inj _ _ this <;> simp
    rw [← natDegree_ofList_of_getLast_ne_zero, ← natDegree_ofList_of_getLast_ne_zero, h]
    · intro
      rwa [List.getLast_eq_nthLe, ← List.getD_eq_nthLe (hd'::tl') 0]
    · intro
      rwa [List.getLast_eq_nthLe, ← List.getD_eq_nthLe (hd::tl) 0]
  · intro n hn hn'
    rw [← List.getD_eq_nthLe l 0, ← List.getD_eq_nthLe l' 0, ← coeff_ofList, ← coeff_ofList, h]

end

/-- Auxiliary construction of lists that do not have `0` as the last element, which are arguments
to `polynomial.embed_list`. -/
def List.dropTerminalZeros [DecidablePred fun x : R => x = 0] (l : List R) :
    { l : List R // l = [] ∨ l.getD (l.length - 1) 0 ≠ 0 } :=
  ⟨l.rdropWhile (· = 0),
    by
    induction' l using List.reverseRecOn with xs x IH
    · simp
    · simp only [List.rdropWhile_concat]
      split_ifs with h
      · simp [-List.rdropWhile_eq_nil_iff, IH]
      · simp only [decide_eq_true_eq] at h
        rw [List.getD_eq_nthLe, List.nthLe_append_right] <;> simp [h]⟩

/-- The list of coefficients of `p : Polynomial R`, from least to greatest power.
The zero polynomial produces `[]`.  -/
def toList (p : Polynomial R) : List R :=
  List.ofFn fun i : Fin (p.natDegree + 1) => p.coeff i

@[simp]
theorem toList_zero : toList (0 : Polynomial R) = [0] :=
  rfl

@[simp]
theorem length_toList (p : Polynomial R) : (toList p).length = p.natDegree + 1 :=
  List.length_ofFn _

theorem toList_ne_nil (p : Polynomial R) : toList p ≠ [] :=
  List.ne_nil_of_length_eq_succ (length_toList _)

theorem getD_toList (p : Polynomial R) (d : R) (n : ℕ) :
    (toList p).getD n d = if n ≤ p.natDegree then p.coeff n else d := by
  simp only [toList, List.ofFn_succ, Fin.val_zero, Fin.val_succ]
  cases n
  · simp
  split_ifs with hn
  · rw [List.getD_cons_succ, List.getD_eq_nthLe] <;> simp [Nat.lt_of_succ_le hn]
  · rw [List.getD_cons_succ, List.getD_eq_default]
    simpa [Nat.lt_succ_iff] using hn

@[simp]
theorem getLast_toList (p : Polynomial R) (hp : toList p ≠ [] := toList_ne_nil p) :
    List.getLast (toList p) hp = p.leadingCoeff := by
  rw [List.getLast_eq_nthLe, ← List.getD_eq_nthLe _ (0 : R), getD_toList]
  simp

variable [DecidablePred fun x : R => x ≠ 0]

/-- `ofList` is the left inverse to `toList`. -/
theorem ofList_toList (p : Polynomial R) : ofList (toList p) = p := by
  ext
  simp (config := { contextual := true }) [getD_toList, coeff_eq_zero_of_natDegree_lt]

theorem leftInverse_ofList_toList : Function.LeftInverse (fun l : List R => ofList l) toList :=
  ofList_toList

/-- `toList` is the partial left inverse to `ofList`. -/
theorem toList_ofList (l : List R) (hl : l.getD (l.length - 1) 0 ≠ 0) : toList (ofList l) = l := by
  refine' ofList_inj_on _ _ _ hl (ofList_toList _)
  have : 1 ≤ l.length := by
    cases l
    · simp at hl
    · simp; omega
  rw [getD_toList]
  simp [natDegree_ofList_of_getD_length_sub_one_ne_zero _ hl, hl, tsub_add_cancel_of_le this]

theorem surjective_ofList (p : Polynomial R) :
    ∃ l : List R, p = ofList l ∧ p.natDegree = l.length - 1 :=
  ⟨toList p, (ofList_toList _).symm, by simp⟩

/-- The lists over `Semiring R` that do not have `0` as the last element embed into `R[X]`. -/
def embedList : { l : List R // l = [] ∨ l.getD (l.length - 1) 0 ≠ 0 } ↪ Polynomial R
    where
  toFun l := ofList l
  inj' := by
    rintro ⟨l, rfl | hl⟩ ⟨l', rfl | hl'⟩ h <;> simp only [Subtype.mk.injEq] at *
    · by_cases H : l' = []
      · exact H.symm
      simp only [ofList_eq_zero_iff, @eq_comm _ _ (ofList _), Subtype.coe_mk, ofList_nil] at h
      exfalso
      refine hl' ?_
      apply h
      rw [List.getD_eq_nthLe]
      refine List.nthLe_mem l' (List.length l' - 1) ?_
      apply Nat.pred_lt
      simp [List.length_eq_zero, H]
    · by_cases H : l = []
      · exact H
      simp only [ofList_eq_zero_iff, @eq_comm _ _ (ofList _), Subtype.coe_mk, ofList_nil] at h
      exfalso
      refine hl ?_
      apply h
      rw [List.getD_eq_nthLe]
      refine List.nthLe_mem l (List.length l - 1) ?_
      apply Nat.pred_lt
      simp [List.length_eq_zero, H]
    · exact ofList_inj_on _ _ hl hl' h

end Polynomial
