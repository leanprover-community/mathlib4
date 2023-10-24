/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Sub.Defs

/-! # Partial HasAntidiagonal for functions with finite support

Let `μ` be an AddCommMonoid.

In `Mathlib.Data.Finset.Antidiagonal` is defined a TypeClass
`HasAntidiagonal μ` which provides a function `μ → Finset (μ × μ)
which maps `n : μ` to a `Finset` of pairs `(a,b)`
such that `a + b = n`.

These functions apply to (ι →₀ ℕ), more generally to (ι →₀ μ)
under the additional assumption `OrderedSub μ` that make it
a canonically ordered add monoid.
In fact, we just need an AddMonoid with a compatible order,
finite Iic, such that if a + b = n, then a, b ≤ n,
and any other bound would be OK.

In this file, we provide an analogous definition for ι → μ,
with an explicit finiteness conditions on the support

* we define `Fin.hasAntidiagonal d`

* For `s : Finset ι`, we define `Finset.piAntidiagonal s n` as the `Finset (ι → μ)`
of functions with support in `s` whose sum is equal to `n`.

-/

namespace Finset

open scoped BigOperators

open Function

class HasPiAntidiagonal (μ : Type*) [AddCommMonoid μ]
  {ι : Type*} (s : Finset ι) where
  /-- The piAntidiagonal function -/
  piAntidiagonal : μ → Finset (ι → μ)
  /-- A function belongs to `piAntidiagonal n` iff its support is contained in s and the sum of its components is equal to `n` -/
  mem_piAntidiagonal {n} {f} : f ∈ piAntidiagonal n ↔ f.support ≤ s ∧ s.sum f = n

section HasAntidiagonal

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ]

variable {ι : Type*} [DecidableEq ι]

/-- `finAntidiagonal d n` is the type of d-tuples with sum n -/
def finAntidiagonal : (d : ℕ) → μ → Finset (Fin d → μ)
  | 0 => fun n => ite (n = 0) {const _ (0 : μ)} ∅
  | d + 1 => fun n => Finset.biUnion (antidiagonal n)
      (fun ab => (finAntidiagonal d ab.2).map {
        toFun := fun f => Fin.cons (ab.1) f
        inj' := fun f g h => by
          simp only [Fin.cons_eq_cons, true_and] at h
          exact h })

/-- `finAntidiagonal d n` is the type of d-tuples with sum n -/
lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d → μ) :
    f ∈ finAntidiagonal d n ↔ univ.sum f = n := by
  revert n f
  induction d with
  | zero => exact fun n f => (by
      simp only [Nat.zero_eq, finAntidiagonal, Pi.const_zero, Matrix.zero_empty, univ_eq_empty, sum_empty]
      by_cases hn : n = 0
      · rw [if_pos hn, hn]
        simp only [mem_singleton, eq_iff_true_of_subsingleton]
      · rw [if_neg hn]
        simp only [not_mem_empty, false_iff]
        intro hn'; apply hn; rw [← hn'])
  | succ d ih => exact fun n f => (by
      simp only [finAntidiagonal, mem_biUnion, mem_map, Embedding.coeFn_mk, Prod.exists, exists_and_right]
      constructor
      · rintro ⟨a, b, hab, g, hg, hf⟩
        rw [ih b g] at hg
        rw [mem_antidiagonal] at hab
        rw [← hf, Fin.sum_cons, hg, hab]
      · intro hf
        rw [← Fin.cons_self_tail f, Fin.sum_cons] at hf
        use f 0
        use ∑ i : Fin d, Fin.tail f i
        constructor
        · rw [mem_antidiagonal]
          exact hf
        use Fin.tail f
        constructor
        · rw [ih]
        · apply Fin.cons_self_tail)

/-- HasPiAntidiagonal for `Fin d` and `Finset.univ` -/
def _root_.Fin.hasPiAntidiagonal_univ (d : ℕ) : HasPiAntidiagonal μ (Finset.univ : Finset (Fin d)) := {
  piAntidiagonal := finAntidiagonal d
  mem_piAntidiagonal := fun {n} {f} => by
    rw [mem_finAntidiagonal]
    simp only [coe_univ, Set.le_eq_subset, Set.subset_univ, true_and] }

/-- HasPiAntidiagonal for a `Fintype` -/
noncomputable def _root_.Fintype.hasPiAntidiagonal_univ (ι : Type*) [Fintype ι] : HasPiAntidiagonal μ (Finset.univ : Finset ι) := {
  piAntidiagonal := by
    have e : Finset (ι → μ) ≃ Finset (Fin (Fintype.card ι) → μ) :=
      Equiv.finsetCongr (Equiv.piCongrLeft' _ (Fintype.equivFin ι))
    intro n
    refine e.symm (finAntidiagonal _ n)
  mem_piAntidiagonal := fun {n} {f} => by
    simp only [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, mem_map_equiv, Equiv.symm_symm, coe_univ,
      Set.le_eq_subset, Set.subset_univ, true_and]
    rw [mem_finAntidiagonal]
    simp only [Equiv.piCongrLeft'_apply]
    let h := Finset.sum_map Finset.univ ((Fintype.equivFin ι).symm.toEmbedding) f
    simp only [map_univ_equiv, Equiv.coe_toEmbedding] at h
    rw [h] }

/-- general construction of HasPiAntidiagonal

It is noncomputable because it uses an unknown parametrization of `s` as well as `Function.extend` -/
noncomputable
def hasPiAntidiagonal' (ι : Type*) (s : Finset ι) :
    HasPiAntidiagonal μ s := by
  haveI : HasPiAntidiagonal μ (attach s) := sorry
  exact {
  piAntidiagonal := fun n => by
    have : Function.Injective (fun f => Function.extend (Subtype.val : s → ι) f (0 : ι → μ))
    · intro f g h
      ext i
      rw [Function.funext_iff] at h
      specialize h i.val
      simp only [Subtype.coe_injective.extend_apply _ _ _] at h
      exact h
    · exact ((Fintype.hasPiAntidiagonal_univ s).piAntidiagonal n).map ⟨_, this⟩
  mem_piAntidiagonal := fun {n} {f} => by
    simp only [mem_map, Embedding.coeFn_mk, Set.le_eq_subset, support_subset_iff, ne_eq, mem_coe]
    constructor
    · rintro ⟨g, hg, hgf⟩
      rw [(Fintype.hasPiAntidiagonal_univ _).mem_piAntidiagonal] at hg
      constructor
      · intro i
        rw [← hgf, not_imp_comm]
        intro hi
        rw [Function.extend_apply']
        simp only [Pi.zero_apply]
        rintro ⟨a, ha⟩
        apply hi
        rw [← ha]
        exact a.prop
      · rw [← hgf, ← hg.2, ← Finset.sum_attach]
        apply Finset.sum_congr rfl
        intros
        rw [Subtype.coe_injective.extend_apply]
    · rintro ⟨hfs, hf⟩
      use fun i => f ↑i
      constructor
      · rw [(Fintype.hasPiAntidiagonal_univ _).mem_piAntidiagonal]
        simp only [univ_eq_attach, Set.le_eq_subset, support_subset_iff, ne_eq,
          mem_coe, mem_attach, implies_true, Subtype.forall, true_and]
        rw [Finset.sum_attach]
        exact hf
      · ext i
        by_cases hi : i ∈ s
        · rw [Subtype.coe_injective.extend_apply _ _ ⟨i, hi⟩]
        · rw [Function.extend_apply']
          simp only [Pi.zero_apply]
          by_contra hi'
          apply hi
          exact (hfs i (ne_comm.mp hi'))
          rintro ⟨j, rfl⟩
          apply hi
          exact j.prop }

end HasAntidiagonal

/- Probably what follows can be proved using what precedes -/
section pi

variable {μ : Type*} [CanonicallyOrderedAddCommMonoid μ]
  [LocallyFiniteOrder μ] [DecidableEq μ]

variable {ι : Type*} [DecidableEq ι]

/-- The Finset of functions `ι → μ` whose support is contained in `s : Finset ι`
  and whose sum is `n` -/
def piAntidiagonal (s : Finset ι) (n : μ) : Finset (ι → μ) :=
  Finset.filter (fun f => s.sum f = n)
    ((s.pi fun _ => Iic n).map
      ⟨fun f i => if h : i ∈ s then f i h else 0,
        fun f g h => by ext i hi; simpa only [dif_pos hi] using congr_fun h i⟩)

@[simp]
theorem mem_piAntidiagonal (s : Finset ι) (n : μ) (f : ι → μ) :
    f ∈ piAntidiagonal s n ↔ s.sum f = n ∧ ∀ (i) (_ : i ∉ s), f i = 0 := by
  rw [piAntidiagonal, mem_filter, and_comm, and_congr_right]
  intro h
  simp only [mem_map, exists_prop, Function.Embedding.coeFn_mk, mem_pi]
  constructor
  · rintro ⟨_, _, rfl⟩ _ hi
    dsimp only
    rw [dif_neg hi]
  · intro hf
    refine' ⟨fun i _ => f i, fun i hi => _, _⟩
    · rw [mem_Iic, ← h]
      apply single_le_sum _ hi
      simp only [zero_le, implies_true]
    · ext x
      dsimp only
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm]
      exact hf x

variable (μ)

-- useless
def Pi.AddSubmonoid_ofSupport (s : Set ι) : AddSubmonoid (ι → μ) := {
  carrier := { f | f.support ≤ s}
  add_mem' := fun {a} {b} ha hb => by
    simp only [Set.le_eq_subset, support_subset_iff, ne_eq, Set.mem_setOf_eq] at ha hb ⊢
    intro i h
    simp only [Pi.add_apply, add_eq_zero_iff, not_and] at h
    by_cases hi : a i = 0
    · exact hb i (h hi)
    · exact ha i hi
  zero_mem' := by
    simp only [Set.le_eq_subset, support_subset_iff, ne_eq, Set.mem_setOf_eq, Pi.zero_apply, not_true,
      IsEmpty.forall_iff, implies_true] }

variable {μ}

-- Should this be promoted into a HasAntidiagonal instance?
theorem piAntidiagonal_equiv_antidiagonal [HasAntidiagonal μ] (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (piAntidiagonal univ n) =
      Finset.HasAntidiagonal.antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding,
    Function.Embedding.coeFn_mk, ← Equiv.eq_symm_apply]
  simp [mem_piAntidiagonal, add_comm, Finset.HasAntidiagonal.mem_antidiagonal]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff, ← forall_and, funext_iff]
  apply forall_congr'
  intro i
  simp only [← or_imp, em (i ∈ s), forall_true_left, Pi.zero_apply]

theorem piAntidiagonal_empty (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [sum_empty, not_mem_empty, not_false_iff, forall_true_left]
  split_ifs with hn
  simp only [hn, mem_singleton, funext_iff, eq_self_iff_true, true_and_iff, Pi.zero_apply]
  simp only [not_mem_empty, iff_false_iff]
  intro h'; exact hn h'.1.symm

theorem piAntidiagonal_insert [HasAntidiagonal μ] [DecidableEq (ι → μ)]
    (n : μ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    piAntidiagonal (insert a s) n =
      (Finset.HasAntidiagonal.antidiagonal n).biUnion
        fun p : μ × μ =>
          (piAntidiagonal s p.snd).image (fun f => Function.update f a p.fst) := by
  ext f
  rw [mem_piAntidiagonal, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, mem_piAntidiagonal, Prod.exists]
    use f a, s.sum f
    constructor
    · rw [mem_antidiagonal]
    rw [mem_image]
    use Function.update f a 0
    constructor
    · rw [mem_piAntidiagonal s (s.sum f)]
      constructor
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_apply]; rw [if_neg]; intro hia; apply h; rw [← hia]; exact hi
      intro i hi; rw [Function.update_apply]; split_ifs with hia
      rfl
      apply h₁; simp only [mem_insert, not_or]; exact ⟨hia, hi⟩
    · ext i
      rw [Function.update_apply (update f a 0), Function.update_apply]
      split_ifs with hia
      rw [hia]
      rfl
  · simp only [mem_insert, Finset.HasAntidiagonal.mem_antidiagonal, mem_image, exists_prop,
      Prod.exists, forall_exists_index, and_imp, mem_piAntidiagonal]
    rintro d e rfl g hg hg' rfl
    constructor
    · simp only [Function.update_same]
      apply congr_arg₂ _ rfl
      rw [← hg]
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_noteq _]
      intro hia; apply h; simpa only [hia] using hi
    · intro i hi; rw [not_or] at hi
      rw [Function.update_noteq hi.1]
      exact hg' i hi.2

end pi

end Finset
