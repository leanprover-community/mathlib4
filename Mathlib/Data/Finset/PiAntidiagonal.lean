/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Sub.Defs

import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Partial HasAntidibgonal for functions with finite support

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

* For `s : Finset ι`,  we define `Finset.piAntidiagonal s n`
  as the `Finset (ι → μ)` of functions with support in `s`
  whose sum is equal to `n`.
  Given `HasAntidiagonal μ`, this is indeed a Finset

-/

def Set.InjOn.embedding {α β : Type*} {f : α → β}  {s : Finset α}
    (hs : Set.InjOn f s) : s ↪ β := { inj' := hs.injective }

def Finset.map_of_injOn {α β : Type*} (f : α → β)
    (s : Finset α) (hs : Set.InjOn f s) : Finset β  :=
  s.attach.map { inj' := hs.injective }

namespace Finset

open scoped BigOperators

open Function
/-
class HasPiAntidiagonal (ι : Type*) [Fintype ι] (μ : Type*) [AddCommMonoid μ] where
  /-- The piAntidiagonal function -/
  piAntidiagonal : μ → Finset (ι → μ)
  /-- A function belongs to `piAntidiagonal n` iff the sum of its values is equal to `n` -/
  mem_piAntidiagonal {n} {f} : f ∈ piAntidiagonal n ↔ univ.sum f = n

export HasPiAntidiagonal (piAntidiagonal mem_piAntidiagonal)

/-- piAntidiagonal instance for ℕ, using `Finset.Nat.andidiagonalTuple` -/
instance (k : ℕ) : HasPiAntidiagonal (Fin k) ℕ where
  piAntidiagonal n := Finset.Nat.antidiagonalTuple k n
  mem_piAntidiagonal := Finset.Nat.mem_antidiagonalTuple

namespace HasPiAntidiagonal

open Finset

variable {ι : Type*} [Fintype ι] (μ : Type*) [CanonicallyOrderedAddCommMonoid μ]
  [HasPiAntidiagonal ι μ]

theorem piAntidiagonal_zero :
    piAntidiagonal (0 : μ) = {(0 : ι → μ)} := by
  ext f
  simp only [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff, mem_univ, forall_true_left, funext_iff, Pi.zero_apply]

theorem piAntidiagonal_empty [IsEmpty ι] [DecidableEq μ] (n : μ) :
    piAntidiagonal n = if n = 0 then  {(0 : ι → μ)} else ∅ := by
  ext f
  split_ifs with hn
  · simp only [hn, piAntidiagonal_zero]
  · simp only [mem_piAntidiagonal, univ_eq_empty, sum_empty, not_mem_empty, iff_false]
    exact ne_comm.mp hn

section HasPiAntidiagonal

variable {ι : Type*} [DecidableEq ι]

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ]

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
      simp only [Nat.zero_eq, finAntidiagonal, Pi.const_zero,
        Matrix.zero_empty, univ_eq_empty, sum_empty]
      by_cases hn : n = 0
      · rw [if_pos hn, hn]
        simp only [mem_singleton, eq_iff_true_of_subsingleton]
      · rw [if_neg hn]
        simp only [not_mem_empty, false_iff]
        intro hn'; apply hn; rw [← hn'])
  | succ d ih => exact fun n f => (by
      simp only [finAntidiagonal, mem_biUnion, mem_map, Embedding.coeFn_mk,
        Prod.exists, exists_and_right]
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

end HasPiAntidiagonal
end HasPiAntidiagonal-/

/-
section HasPiAntidiagonal'

/- TODO :
* update what follows for `HasPiAntidiagonal`
* check that it is enough for application to products of powers series
* (ifthat works), provide the instance when μ = ℕ  using `Nat.AntidiagonalTuple`
-/

class HasPiAntidiagonal' (ι : Type*) (μ : Type*) [AddCommMonoid μ] where
  /-- The piAntidiagonal function -/
  piAntidiagonal : Finset ι → μ → Finset (ι → μ)
  /-- A function belongs to `piAntidiagonal n`
    iff its support is contained in s and the sum of its components is equal to `n` -/
  mem_piAntidiagonal {s} {n} {f} :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ s.sum f = n

namespace HasPiAntidiagonal'

variable {ι μ : Type*}

section

variable [AddCommMonoid μ] [HasAntidiagonal μ] [HasPiAntidiagonal' ι μ]

theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [coe_empty, Set.le_eq_subset, Set.subset_empty_iff,
    Function.support_eq_empty_iff, Finset.sum_empty, and_true, mem_singleton]

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [coe_empty, Set.le_eq_subset, Set.subset_empty_iff,
    Function.support_eq_empty_iff, Finset.sum_empty, and_true,
    not_mem_empty, iff_false, not_and]
  exact fun _ => ne_comm.mp hn

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq (ι → μ)]
    {a : ι} {s : Finset ι} (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
          (piAntidiagonal s p.snd).attach.map
          (Set.InjOn.embedding (f := fun f x => if (x = a) then p.fst else f x)
          (fun f hf g hg => by
            simp only [mem_coe, mem_piAntidiagonal] at hf hg
            simp only [funext_iff]
            intro h' x
            specialize h' x
            by_cases hx : x = a
            · rw [hx, nmem_support.mp (fun H => h (hf.1 H)), nmem_support.mp (fun H => h (hg.1 H))]
            · simpa only [if_neg hx] using h'))) := by
  ext f
  rw [mem_piAntidiagonal, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨hsupp, hsum⟩
    simp only [mem_antidiagonal, mem_map, mem_attach, true_and, Subtype.exists, Prod.exists]
    refine' ⟨f a, s.sum f, hsum, fun i => if i = a then 0 else f i, _, _⟩
    · rw [mem_piAntidiagonal]
      refine' ⟨_, _⟩
      · simp only [Set.le_eq_subset, support_subset_iff, ne_eq, ite_eq_left_iff, not_forall,
        exists_prop, mem_coe, and_imp]
        intro x hx
        rw [not_imp_comm]
        intro hx'
        rw [← nmem_support]
        apply Set.not_mem_subset hsupp
        simp only [coe_insert, mem_coe, Set.mem_insert_iff]
        exact not_or_intro hx hx'
      · rw [sum_ite]
        have : filter (fun x => x ≠ a) s = s := by
          apply filter_true_of_mem
          rintro i hi rfl
          apply h hi
        simp [this]
    · ext x
      simp only [Set.InjOn.embedding, Embedding.coeFn_mk, Set.restrict_apply]
      split_ifs with hx
      · rw [hx]
      · rfl
  · simp only [mem_insert, Function.Embedding.coeFn_mk, mem_map, mem_antidiagonal, Prod.exists,
      exists_prop, mem_piAntidiagonal, not_or]
    rintro ⟨p, q, rfl, ⟨g, hg⟩, _, rfl⟩
    refine' ⟨_, _⟩
    · intro x hx
      simp only [Set.InjOn.embedding, Embedding.coeFn_mk, Set.restrict_apply, mem_support, ne_eq] at hx
      simp only [mem_piAntidiagonal] at hg
      simp only [coe_insert, mem_coe, Set.mem_insert_iff]
      by_cases hx' : x = a
      · left; exact hx'
      · right
        rw [if_neg hx'] at hx
        apply hg.1
        rw [mem_support]
        exact hx
    · simp only [Set.InjOn.embedding, Embedding.coeFn_mk, Set.restrict_apply, ite_true]
      apply congr_arg₂ _ rfl
      rw [mem_piAntidiagonal] at hg
      rw [← hg.2]
      apply Finset.sum_congr rfl
      intro x hx
      rw [if_neg (ne_of_mem_of_not_mem hx h)]

end

section CanonicallyOrderedAddCommMonoid

variable [CanonicallyOrderedAddCommMonoid μ] [HasPiAntidiagonal' ι μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι → μ)} := by
  ext f
  simp only [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff]
  simp only [Set.le_eq_subset, support_subset_iff, ne_eq, mem_coe, not_imp_comm]
  constructor
  · rintro ⟨hsupp, hsum⟩
    ext x
    by_cases hx : x ∈ s
    · exact hsum x hx
    · exact hsupp x hx
  · intro hf
    simp only [hf, Pi.zero_apply, implies_true, and_self]

end CanonicallyOrderedAddCommMonoid

end HasPiAntidiagonal'
end HasPiAntidiagonal'-/

section HasPiAntidiagonal''
-- Using Finsupp

class HasPiAntidiagonal'' (ι : Type*) (μ : Type*) [AddCommMonoid μ] where
  /-- The piAntidiagonal function -/
  piAntidiagonal : Finset ι → μ → Finset (ι →₀ μ)
  /-- A function belongs to `piAntidiagonal s n`
    iff its support is contained in s and the sum of its components is equal to `n` -/
  mem_piAntidiagonal {s} {n} {f} :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ s.sum f = n

export HasPiAntidiagonal'' (piAntidiagonal mem_piAntidiagonal)

namespace HasPiAntidiagonal''

section Fin

variable {μ : Type*} [AddCommMonoid μ] [DecidableEq μ] [HasAntidiagonal μ]

/-- `finAntidiagonal d n` is the type of d-tuples with sum n -/
noncomputable def finAntidiagonal : (d : ℕ) → μ → Finset (Fin d →₀ μ)
  | 0 => fun n => ite (n = 0) {0} ∅
  | d + 1 => fun n => by
    exact Finset.biUnion (antidiagonal n)
      (fun ab => (finAntidiagonal d ab.2).map {
        toFun := fun f => Finsupp.cons (ab.1) f
        inj' := fun f g h => by
          simp only at h
          rw [← Finsupp.tail_cons ab.1 f, ← Finsupp.tail_cons ab.1 g, h]})

/-- `finAntidiagonal d n` is the type of d-tuples with sum n -/
lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal d n ↔ univ.sum f = n := by
  revert n f
  induction d with
  | zero => exact fun n f => (by
      simp only [Nat.zero_eq, finAntidiagonal, Pi.const_zero,
        Matrix.zero_empty, univ_eq_empty, sum_empty]
      by_cases hn : n = 0
      · rw [if_pos hn, hn, mem_singleton, eq_iff_true_of_subsingleton, true_iff]
      · rw [if_neg hn]
        simp only [not_mem_empty, false_iff, Ne.symm hn])
  | succ d ih => exact fun n f => by (
      simp only [finAntidiagonal, mem_biUnion, mem_map, Embedding.coeFn_mk,
        Prod.exists, exists_and_right]
      constructor
      · rintro ⟨a, b, hab, g, hg, hf⟩
        rw [ih b g] at hg
        rw [← Finsupp.sum_fintype f (fun _ y => y) (fun _ => rfl), ← hf, Finsupp.sum_cons,
          Finsupp.sum_fintype _ _ (fun _ => rfl), hg, mem_antidiagonal.mp hab]
      · intro hf
        use f 0, Finsupp.sum (Finsupp.tail f) (fun _ e => e)
        constructor
        · rw [← Finsupp.sum_fintype f (fun _ y => y) (fun _ => rfl),
            ← Finsupp.cons_tail f, Finsupp.sum_cons] at hf
          exact mem_antidiagonal.mpr hf
        refine' ⟨Finsupp.tail f, _, Finsupp.cons_tail f⟩
        · rw [Finsupp.sum_of_support_subset _ (subset_univ _) _ (fun _ _ => rfl), ih])


/-- `finAntidiagonal' s d n` -- TODO -/
noncomputable def finAntidiagonal' (d : ℕ) (s : Finset (Fin d))  (n :  μ) :
    Finset (Fin d →₀ μ) :=
  (finAntidiagonal d n).filter (fun f => f.support ⊆ s)

lemma mem_finAntidiagonal' (d) (s) (n : μ) (f) :
    f ∈ finAntidiagonal' d s n ↔ (f.support ⊆ s ∧ Finset.sum univ f = n) := by
  unfold finAntidiagonal'
  rw [mem_filter, mem_finAntidiagonal, and_comm]

end Fin


section

variable {ι μ : Type*}

variable [AddCommMonoid μ] [HasAntidiagonal μ] [HasPiAntidiagonal'' ι μ]

theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, sum_empty, and_true, mem_singleton, Finset.subset_empty]
  exact Finsupp.support_eq_empty

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, Finset.subset_empty, Finsupp.support_eq_empty, sum_empty]
  simp only [not_mem_empty, iff_false, not_and]
  exact fun _ => ne_comm.mp hn

theorem piAntidiagonal_empty [DecidableEq μ] (n : μ) :
    piAntidiagonal (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn
  · rw [hn]
    apply piAntidiagonal_empty_of_zero
  · apply piAntidiagonal_empty_of_ne_zero hn

theorem mem_piAntidiagonal_insert [DecidableEq ι] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι →₀ μ} :
    f ∈ piAntidiagonal (insert a s) n ↔
      ∃ m ∈ antidiagonal n, ∃ (g : ι →₀ μ),
        f = Finsupp.update g a m.1 ∧ g ∈ piAntidiagonal s m.2 := by
  simp only [mem_piAntidiagonal, le_eq_subset, mem_antidiagonal, Prod.exists]
  constructor
  · rintro ⟨hsupp, hsum⟩
    use (f a)
    use (s.sum f)
    rw [Finset.sum_insert h] at hsum
    simp only [hsum, true_and]
    use Finsupp.erase a f
    constructor
    · ext x
      by_cases hx : x = a
      · rw [hx]
        simp only [Finsupp.coe_update, update_same]
      · unfold Finsupp.update
        simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.support_erase, Finsupp.coe_mk]
        unfold update
        rw [dif_neg hx]
        unfold Finsupp.erase
        simp only [Finsupp.coe_mk]
        rw [if_neg hx]
    constructor
    · intro x hx
      rw [Finsupp.mem_support_iff] at hx
      suffices hx' : x ∈ insert a s
      rw [mem_insert] at hx'
      cases' hx' with hx' hx'
      · exfalso
        apply hx
        rw [hx']
        simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.erase_same]
      · exact hx'
      apply hsupp
      rw [Finsupp.mem_support_iff]
      intro hx'
      apply hx
      unfold Finsupp.erase
      simp only [Finsupp.coe_mk, ite_eq_left_iff]
      exact fun _ => hx'
    · apply Finset.sum_congr rfl
      intro x hx
      unfold Finsupp.erase
      simp only [Finsupp.coe_mk, ite_eq_left_iff, if_neg (ne_of_mem_of_not_mem hx h)]
  · rintro ⟨n1, n2, hn, g, hf, hgsupp, hgsum⟩
    constructor
    · intro x
      simp only [hf, Finsupp.mem_support_iff, Finset.mem_insert]
      simp only [Finsupp.coe_update, ne_eq]
      by_cases hx : x = a
      · simp only [hx, ne_eq, not_true, true_or, implies_true]
      · rw [update, dif_neg hx]
        intro hx
        right
        apply hgsupp
        rw [Finsupp.mem_support_iff]
        exact hx
    · rw [Finset.sum_insert h, ← hn]
      apply congr_arg₂
      · simp only [hf, Finsupp.coe_update, update_same]
      · rw [← hgsum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [hf]
        unfold Finsupp.update
        simp only [Finsupp.coe_mk]
        unfold update
        rw [dif_neg (ne_of_mem_of_not_mem hx h)]

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq μ] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
          (piAntidiagonal s p.snd).attach.map
          (Set.InjOn.embedding (f := fun f => Finsupp.update f a p.fst)
          (fun f hf g hg => by
            simp only [mem_coe, mem_piAntidiagonal] at hf hg
            simp only [FunLike.ext_iff]
            apply forall_imp
            intro x
            by_cases hx : x = a
            · intro _
              have : g x = 0
              · rw [← Finsupp.not_mem_support_iff, hx]
                exact fun hx' => h (hg.1 hx')
              rw [this]
              · rw [← Finsupp.not_mem_support_iff, hx]
                exact fun hx' => h (hf.1 hx')
            · simp only [Finsupp.coe_update, ne_eq, update, dif_neg hx]
              exact id))) := by
  ext f
  rw [mem_piAntidiagonal_insert h, mem_biUnion]
  apply exists_congr
  rintro ⟨n1, n2⟩
  apply and_congr_right'
  simp only [mem_map, mem_attach, true_and, Subtype.exists]
  apply exists_congr
  intro g
  constructor
  · rintro ⟨hf, hg⟩
    use hg
    rw [hf]
    apply symm
    ext x
    unfold Set.InjOn.embedding
    simp
  · rintro ⟨hg, hf⟩
    constructor
    · ext x
      rw [← hf]
      unfold Set.InjOn.embedding
      simp
    · exact hg

end

section CanonicallyOrderedAddCommMonoid

variable {ι μ : Type*} [CanonicallyOrderedAddCommMonoid μ] [HasPiAntidiagonal'' ι μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp only [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff]
  simp only [Finset.le_eq_subset]
  constructor
  · rintro ⟨hsupp, hsum⟩
    ext x
    by_cases hx : x ∈ f.support
    · exact hsum x (hsupp hx)
    · simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hx
  · intro hf
    simp [hf]

end CanonicallyOrderedAddCommMonoid

section Test -- not conclusive for the moment

open MvPowerSeries

variable {α : Type*} [CommSemiring α]
  {σ : Type*} [DecidableEq σ]
  {ι : Type*} [DecidableEq ι]

theorem coeff_prod [HasPiAntidiagonal'' ι (σ →₀ ℕ)]
    (f : ι → MvPowerSeries σ α) (d : σ →₀ ℕ) (s : Finset ι) :
    coeff α d (∏ j in s, f j) =
      ∑ l in piAntidiagonal s d,
        ∏ i in s, coeff α (l i) (f i) := by
  revert d
  induction s using Finset.induction_on with
  | empty =>
    intro d
    simp only [prod_empty, sum_const, nsmul_eq_mul, mul_one]
    classical
    rw [coeff_one]
    simp only [piAntidiagonal_empty]
    split_ifs with hd
    · simp only [card_singleton, Nat.cast_one]
    · simp only [card_empty, Nat.cast_zero]
  | @insert a s ha ih =>
    intro d
    rw [piAntidiagonal_insert ha]
    rw [prod_insert ha, coeff_mul, sum_biUnion]
    . apply Finset.sum_congr rfl
      · rintro ⟨u, v⟩ huv
        simp only [mem_antidiagonal] at huv
        simp only [Set.InjOn.embedding, sum_map, Embedding.coeFn_mk, Set.restrict_apply,
          Finsupp.coe_update, ne_eq, update_same]
        rw [ih, mul_sum]
        rw [← Finset.sum_attach]
        apply Finset.sum_congr rfl
        rintro ⟨x, hx⟩ _
        rw [Finset.prod_insert ha]
        apply congr_arg₂
        · apply congr_arg
          simp only [update_same]
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_noteq]
          intro hi'; apply ha; simpa [hi'] using hi
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, mem_antidiagonal]
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      rw [onFun_apply, disjoint_left]
      intro k hk hl
      simp only [mem_map, mem_attach, true_and, Subtype.exists] at hk hl
      obtain ⟨k, hk, rfl⟩ := hk
      obtain ⟨l, hl, hkl⟩ := hl
      simp only [mem_piAntidiagonal] at hk hl
      apply h
      simp only [Prod.mk.inj_iff]
      suffices : u = u'
      apply And.intro this
      rw [this, ← huv'] at huv
      simpa only [add_right_inj] using huv
      apply symm
      simp only [Set.InjOn.embedding, Embedding.coeFn_mk, Set.restrict_apply] at hkl
      rw [FunLike.ext_iff] at hkl
      simpa only [Finsupp.coe_update, update_same] using hkl a

variable (s : Finset ι)

example : Fintype s := by exact FinsetCoe.fintype s

end Test

variable {ι : Type*} [DecidableEq ι]

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ]

/-- HasPiAntidiagonal for `Fin d` and `Finset.univ` -/
noncomputable def _root_.Fin.hasPiAntidiagonal_univ (d : ℕ) :
    HasPiAntidiagonal'' (Fin d) μ /- (Finset.univ : Finset (Fin d)) -/ := {
  piAntidiagonal := fun s => finAntidiagonal d
  mem_piAntidiagonal := fun {s} {n} {f} => by
    simp only
    rw [mem_finAntidiagonal]
    simp only [coe_univ, Set.le_eq_subset, Set.subset_univ, true_and]
    sorry }

/-- HasPiAntidiagonal for a `Fintype` -/
noncomputable def _root_.Fintype.hasPiAntidiagonal_univ (ι : Type*) [Fintype ι] :
    HasPiAntidiagonal'' (Finset.univ : Finset ι) μ := {
  piAntidiagonal := by
    have e : Finset (ι → μ) ≃ Finset (Fin (Fintype.card ι) → μ) :=
      Equiv.finsetCongr (Equiv.piCongrLeft' _ (Fintype.equivFin ι))
    intro n
    sorry --refine e.symm (finAntidiagonal _ n)
  mem_piAntidiagonal := fun {n} {f} => by
    simp only [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, mem_map_equiv,
      Equiv.symm_symm, coe_univ, Set.le_eq_subset, Set.subset_univ, true_and]
    sorry
    /- rw [mem_finAntidiagonal]
    simp only [Equiv.piCongrLeft'_apply]
    let h := Finset.sum_map Finset.univ ((Fintype.equivFin ι).symm.toEmbedding) f
    simp only [map_univ_equiv, Equiv.coe_toEmbedding] at h
    rw [h] -/ }

/-- general construction of HasPiAntidiagonal

It is noncomputable because it uses an unknown parametrization of `s`
  as well as `Function.extend` -/
noncomputable
def hasPiAntidiagonal' (ι : Type*) (s : Finset ι) :
    HasPiAntidiagonal'' s μ := by
  haveI : HasPiAntidiagonal'' (attach s) μ := sorry
  exact {
  piAntidiagonal := fun n => by
    have : Function.Injective (fun f => Function.extend (Subtype.val : s → ι) f (0 : ι → μ))
    · intro f g h
      ext i
      rw [Function.funext_iff] at h
      specialize h i.val
      simp only [Subtype.coe_injective.extend_apply _ _ _] at h
      exact h
    · sorry --exact ((Fintype.hasPiAntidiagonal_univ s).piAntidiagonal n).map ⟨_, this⟩
  mem_piAntidiagonal := fun {s} {n} {f} => by
    simp only [mem_map, Embedding.coeFn_mk, Set.le_eq_subset, support_subset_iff, ne_eq, mem_coe]
    constructor
    · sorry/- rintro ⟨g, hg, hgf⟩
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
        rw [Subtype.coe_injective.extend_apply] -/
    · rintro ⟨hfs, hf⟩
      sorry/- use fun i => f ↑i
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
          exact j.prop -/ }

end HasPiAntidiagonal''
end HasPiAntidiagonal''
end Finset
--end HasAntidiagonal

#exit

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
    simp only [Set.le_eq_subset, support_subset_iff, ne_eq, Set.mem_setOf_eq,
      Pi.zero_apply, not_true, IsEmpty.forall_iff, implies_true] }

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

end HasPiAntidiagonal''

end Finset
