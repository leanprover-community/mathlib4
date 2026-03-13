/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.Order
public import Mathlib.Algebra.MvPolynomial.CharacteristicSet.Initial

/-!
# Reduction relation

This file defines the **reduction** relation between multivariate polynomials,
a fundamental concept in the Characteristic Set Method.

## Main definitions

* `MvPolynomial.reducedTo q p`:
  A polynomial `q` is *reduced* with respect to `p` if either `q = 0` or
  the degree of `q` in `p`'s main variable is strictly less than the degree of `p`.
  If `p` is a constant (i.e., `max_vars p = ⊥`), then no non-zero `q` is reduced w.r.t. `p`.

* `MvPolynomial.reducedToSet q a`:
  A polynomial `q` is reduced with respect to a set `a` if it is reduced
  with respect to every element of `a`.

-/

@[expose] public section

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ] {p q r : MvPolynomial σ R}

namespace MvPolynomial

section Reduced

/-- `q` is reduced with respect to `p`if `q = 0` or
if the degree of `q` in the main variable of `p` is strictly less than the degree of `p`.

Note: if `p` is a constant, then no non-zero `q` is reduced with respect to `p`. -/
def reducedTo (q p : MvPolynomial σ R) : Prop :=
  if q = 0 then True
  else
    match p.vars.max with
    | ⊥ => False
    | some c => q.degreeOf c < p.degreeOf c

theorem zero_reducedTo (p : MvPolynomial σ R) : (0 : MvPolynomial σ R).reducedTo p := trivial

theorem not_reducedTo_of_bot_max_vars (hq : q ≠ 0) : p.vars.max = ⊥ → ¬q.reducedTo p :=
  fun hp ↦ by simp only [reducedTo, hq, reduceIte, hp, not_false_eq_true]

theorem max_vars_ne_bot_of_reducedTo (hq : q ≠ 0) : q.reducedTo p → p.vars.max ≠ ⊥ :=
  fun hp con ↦ not_reducedTo_of_bot_max_vars hq con hp

theorem reducedTo_iff {c : σ} (hp : p.vars.max = c) (hq : q ≠ 0) :
    q.reducedTo p ↔ q.degreeOf c < p.degreeOf c := by simp only [reducedTo, hq, reduceIte, hp]

noncomputable instance : DecidableRel (@reducedTo R σ _ _ _) := fun q p ↦
  if hq : q = 0 then isTrue <| hq ▸ zero_reducedTo p
  else
    match hp : p.vars.max with
    | ⊥ => isFalse <| not_reducedTo_of_bot_max_vars hq hp
    | some _ => decidable_of_iff _ (reducedTo_iff hp hq).symm

theorem reducedTo_of_max_vars_lt (h : q.vars.max < p.vars.max) : q.reducedTo p := by
  if hq : q = 0 then exact hq ▸ zero_reducedTo p
  else
    rcases WithBot.ne_bot_iff_exists.mp <| LT.lt.ne_bot h with ⟨c, hc⟩
    apply (reducedTo_iff hc.symm hq).mpr
    rewrite [(iff_not_comm.mpr mem_vars_iff_degreeOf_ne_zero).mpr <|
      Finset.notMem_of_max_lt_coe (hc ▸ h)]
    exact Nat.pos_of_ne_zero <| degreeOf_max_vars_ne_zero hc.symm

theorem reducedTo_congr_right : p ≈ q → (r.reducedTo p ↔ r.reducedTo q) := fun h ↦
  have (p q : MvPolynomial σ R) (h : p ≈ q) : r.reducedTo p → r.reducedTo q := by
    have : p.vars.max = q.vars.max ∧ p.mainDegree = q.mainDegree := equiv_iff.mp h
    simp only [reducedTo, if_true_left]
    intro hr1 hr2
    match hc : q.vars.max with
    | none => simp [hr2, hc ▸ this.1] at hr1
    | some c =>
      have hc' := hc ▸ this.1
      simp [hr2, hc', mainDegree_of_max_vars_isSome hc' ▸ this.2] at hr1
      simp only [mainDegree_of_max_vars_isSome hc ▸ hr1]
  ⟨this p q h, this q p h.symm⟩

theorem reducedTo_iff_gt_of_max_vars_eq (hq : q ≠ 0) (h : q.vars.max = p.vars.max) :
    q.reducedTo p ↔ q < p where
  mp hl :=
    match hp : p.vars.max with
    | ⊥ => absurd hl <| not_reducedTo_of_bot_max_vars hq hp
    | some c => lt_def.mpr <| Or.inr ⟨h, by
      rw [mainDegree_of_max_vars_isSome hp, mainDegree_of_max_vars_isSome <| h.trans hp]
      exact (reducedTo_iff hp hq).mp hl⟩
  mpr hr :=
    have : q.mainDegree < p.mainDegree := (lt_iff_not_imp.mp hr <| Eq.not_lt h).2
    match hp : p.vars.max with
    | ⊥ => by
      rewrite [mainDegree_eq_zero_iff.mpr hp, mainDegree_eq_zero_iff.mpr (h ▸ hp)] at this
      exact absurd this <| Nat.not_lt_zero 0
    | some c => by
      rw [mainDegree_of_max_vars_isSome hp, mainDegree_of_max_vars_isSome (h ▸ hp)] at this
      exact (reducedTo_iff hp hq).mpr this

theorem not_reduceTo_self (h : p ≠ 0) : ¬p.reducedTo p :=
  mt (reducedTo_iff_gt_of_max_vars_eq h rfl).mp (lt_irrefl p)

theorem max_vars_lt_of_reducedTo_of_le (h1 : q ≠ 0) (h2 : p ≤ q) (h3 : q.reducedTo p) :
    p.vars.max < q.vars.max := by
  by_contra con
  have con : q.vars.max = p.vars.max :=
    le_antisymm (not_lt.mp con) (max_vars_le_of_le h2)
  have := (reducedTo_iff_gt_of_max_vars_eq h1 con).mp h3
  exact absurd h2 <| not_le_iff_gt.mpr this

theorem lt_of_reducedTo_of_le (h1 : q ≠ 0) (h2 : p ≤ q) (h3 : q.reducedTo p) : p < q :=
  lt_of_max_vars_lt <| max_vars_lt_of_reducedTo_of_le h1 h2 h3

variable {α : Type*} [Membership (MvPolynomial σ R) α] {p q : MvPolynomial σ R} {a : α}

/-- `q` is reduced with respect to a set `a`
if it is reduced with respect to all elements of `a`. -/
def reducedToSet (q : MvPolynomial σ R) (a : α) : Prop := ∀ p ∈ a, q.reducedTo p

noncomputable instance : @DecidableRel _ (List (MvPolynomial σ R)) reducedToSet :=
  fun _ ↦ List.decidableBAll _

theorem reducedToSet_def : q.reducedToSet a ↔ ∀ p ∈ a, q.reducedTo p := Iff.rfl

theorem zero_reducedToSet : (0 : MvPolynomial σ R).reducedToSet a := fun _ _ ↦ zero_reducedTo _

section Initial

theorem initial_reducedTo : q.reducedTo p → q.initial.reducedTo p := fun h ↦ by
  by_cases hq : q = 0
  · rewrite [hq, initial_zero]
    exact zero_reducedTo p
  by_cases hp : p.vars.max = ⊥
  · exact absurd h <| not_reducedTo_of_bot_max_vars hq hp
  by_cases hqi : q.initial = 0
  · exact hqi ▸ zero_reducedTo p
  have ⟨c, hc⟩ :=  WithBot.ne_bot_iff_exists.mp hp
  apply (reducedTo_iff hc.symm hqi).mpr
  have h := (reducedTo_iff hc.symm hq).mp h
  exact lt_of_le_of_lt (degreeOf_initial_le q c) h

theorem initial_reducedTo_self (hp : p.vars.max ≠ ⊥) : p.initial.reducedTo p :=
  reducedTo_of_max_vars_lt <| max_vars_initial_lt hp

theorem initial_reducedToSet {α : Type*} [Membership (MvPolynomial σ R) α] {p : MvPolynomial σ R}
    {a : α} : p.reducedToSet a → p.initial.reducedToSet a :=
  fun h q hq1 ↦ initial_reducedTo (h q hq1)

end Initial

section TriangularSet

open TriangularSet

variable {S T : TriangularSet σ R} {p q : MvPolynomial σ R}

theorem reducedToSet_empty (q : MvPolynomial σ R) : q.reducedToSet (∅ : TriangularSet σ R) :=
  fun p hp ↦ absurd hp (notMem_empty p)

theorem reducedToSet_iff : q.reducedToSet S ↔ ∀ i < S.length, q.reducedTo (S i) :=
  Iff.trans Iff.rfl S.forall_mem_iff_forall_index

noncomputable instance instDecidableRelReducedToSet :
    @DecidableRel _ (TriangularSet σ R) reducedToSet :=
  fun _ S ↦ @decidable_of_iff _ _ reducedToSet_iff.symm (S.length.decidableBallLT _)

theorem reducedToSet_congr_right : S ≈ T → (q.reducedToSet S ↔ q.reducedToSet T) := fun h ↦ by
  have := TriangularSet.equiv_iff.mp h
  rw [reducedToSet_iff, reducedToSet_iff, ← this.1, forall_congr']
  refine fun i ↦ imp_congr_right fun _ ↦ reducedTo_congr_right <| this.2 i

/--
Key Lemma for the Basic Set Algorithm:
If `p` is non-zero and reduced with respect to `S`, then modifying `S`
by appending `p` (using `takeConcat`) strictly decreases the order of the triangular set.
This order decrease is what guarantees the termination of the characteristic set computation.
-/
theorem _root_.TriangularSet.takeConcat_lt_of_reducedToSet
    (p_ne_zero : p ≠ 0) (hp : p.reducedToSet S) : S.takeConcat p < S := by
  unfold takeConcat
  rewrite [reducedToSet_iff] at hp
  split_ifs with hS hc
  · exact hS ▸ single_lt_empty p_ne_zero
  · refine gt_single_of_first_gt p_ne_zero ?_
    rcases lt_or_eq_of_le hc with h | h
    · exact MvPolynomial.lt_of_max_vars_lt h
    apply (MvPolynomial.reducedTo_iff_gt_of_max_vars_eq p_ne_zero h).mp
    exact hp 0 <| length_ge_one_iff.mpr hS
  let k := Nat.find <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have hk : k ≤ S.length ∧ (S (k - 1)).vars.max < p.vars.max ∧
      (p.vars.max ≤ (S k).vars.max ∨ k = S.length) :=
    Nat.find_spec <| exists_index_mainVar_between_of_mainVar_first_lt <| lt_of_not_ge hc
  have length_tk : (S.take k).length = k := min_eq_left hk.1
  change (S.take k).concat p _ < S
  by_cases keq : k = S.length
  · refine TriangularSet.lt_def.mpr <| Or.inr ?_
    rewrite [length_concat, length_tk]
    refine ⟨keq ▸ lt_add_one S.length, fun i hi ↦ ?_⟩
    rw [concat_apply, length_tk, keq, take_length, if_pos hi]
  refine TriangularSet.lt_def.mpr <| Or.inl ?_
  simp only [length_concat, concat_apply, length_tk]
  refine ⟨k, lt_add_one k, ?_, fun i hi ↦ by rw [take_apply, if_pos hi, if_pos hi]⟩
  rewrite [if_neg <| Nat.lt_irrefl k, if_pos rfl]
  by_cases max_vars_lt' : p.vars.max < (S k).vars.max
  · exact MvPolynomial.lt_of_max_vars_lt max_vars_lt'
  have : p.vars.max ≤ (S k).vars.max := (or_iff_left keq).mp hk.2.2
  have : p.vars.max = (S k).vars.max := eq_of_le_of_ge this <| le_of_not_gt max_vars_lt'
  have := MvPolynomial.reducedTo_iff_gt_of_max_vars_eq p_ne_zero this
  exact this.mp <| hp k <| Nat.lt_of_le_of_ne hk.1 keq

end TriangularSet
end Reduced
end MvPolynomial
