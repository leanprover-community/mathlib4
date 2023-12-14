/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta
-/

import Mathlib.Data.Finset.Antidiagonal
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Logic.Embedding.Set

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

section InjOn

variable {α β : Type*} {f : α → β}  {s : Set α} (hs : Set.InjOn f s)
/-
/-- The embedding associated with an map which is injective on a subset -/
def Set.InjOn.embedding : s ↪ β := { inj' := hs.injective }

@[simp]
lemma Set.InjOn.embedding_apply {a : s} : hs.embedding a = f a := rfl
-/

def Finset.map_of_injOn {s : Finset α} (hs : Set.InjOn f s) :
    Finset β  := s.attach.map { inj' := hs.injective }

#find_home! Finset.map_of_injOn
end InjOn

namespace Finset

open scoped BigOperators

open Function

section HasPiAntidiagonal

/-- The HasPiAntidiagonal class -/
class HasPiAntidiagonal (ι : Type*) (μ : Type*) [AddCommMonoid μ] where
  /-- The piAntidiagonal function -/
  piAntidiagonal : Finset ι → μ → Finset (ι →₀ μ)
  /-- A function belongs to `piAntidiagonal s n`
    iff its support is contained in s and the sum of its components is equal to `n` -/
  mem_piAntidiagonal {s} {n} {f} :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ Finsupp.sum f (fun _ x => x) = n

export HasPiAntidiagonal (piAntidiagonal mem_piAntidiagonal)


namespace HasPiAntidiagonal

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

lemma mem_finAntidiagonal (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal d n ↔ Finsupp.sum f (fun _ x => x) = n := by
  revert n f
  induction d with
  | zero => exact fun n f => (by
      simp only [Nat.zero_eq, finAntidiagonal, Pi.const_zero,
        Matrix.zero_empty, univ_eq_empty, sum_empty]
      by_cases hn : n = 0
      · rw [if_pos hn, hn, mem_singleton]
        simp only [eq_iff_true_of_subsingleton, true_iff]
        rw [Subsingleton.eq_zero f, Finsupp.sum_zero_index]
      · simp only [if_neg hn, not_mem_empty, false_iff]
        rw [Subsingleton.eq_zero f, Finsupp.sum_zero_index]
        exact Ne.symm hn)
  | succ d ih => exact fun n f => by (
      simp only [finAntidiagonal, mem_biUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk,
        Prod.exists]
      constructor
      · rintro ⟨a, b, hab, g, hg, hf⟩
        rw [ih b g] at hg
        rw [← hf, Finsupp.sum_cons, hg, hab]
      · intro hf
        use f 0, Finsupp.sum (Finsupp.tail f) (fun _ e => e)
        constructor
        · rw [← Finsupp.cons_tail f, Finsupp.sum_cons] at hf
          exact hf
        exact ⟨Finsupp.tail f, by rw [ih], Finsupp.cons_tail f⟩)

lemma mem_finAntidiagonal' (d : ℕ) (n : μ) (f : Fin d →₀ μ) :
    f ∈ finAntidiagonal d n ↔ univ.sum f = n := by
  rw [mem_finAntidiagonal, Finsupp.sum_of_support_subset f (subset_univ _) _ (fun _ _ => rfl)]

end Fin

section

variable {ι μ : Type*}

variable [AddCommMonoid μ] [HasAntidiagonal μ] [HasPiAntidiagonal ι μ]

lemma mem_piAntidiagonal' (s : Finset ι) (n : μ) (f) :
    f ∈ piAntidiagonal s n ↔ f.support ≤ s ∧ s.sum f = n := by
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, and_congr_right_iff]
  intro hs
  rw [Finsupp.sum_of_support_subset _ hs]
  exact fun _ _ => rfl

theorem piAntidiagonal_empty_of_zero :
    piAntidiagonal (∅ : Finset ι) (0 : μ) = {0} := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, mem_singleton, Finset.subset_empty]
  rw [Finsupp.support_eq_empty, and_iff_left_iff_imp]
  intro hf
  rw [hf, Finsupp.sum_zero_index]

theorem piAntidiagonal_empty_of_ne_zero {n : μ} (hn : n ≠ 0) :
    piAntidiagonal (∅ : Finset ι) n = ∅ := by
  ext f
  rw [mem_piAntidiagonal]
  simp only [le_eq_subset, Finset.subset_empty, Finsupp.support_eq_empty, sum_empty,
    not_mem_empty, iff_false, not_and]
  intro hf
  rw [hf, Finsupp.sum_zero_index]
  exact Ne.symm hn

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
  simp only [mem_piAntidiagonal', le_eq_subset, mem_antidiagonal, Prod.exists]
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
      · simp only [Finsupp.update, Finsupp.mem_support_iff, ne_eq, not_not,
          Finsupp.support_erase, Finsupp.coe_mk]
        simp only [update, dif_neg hx]
        simp only [Finsupp.erase, Finsupp.coe_mk]
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
      simp only [Finsupp.erase, Finsupp.coe_mk, hx', ite_self]
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [Finsupp.erase, Finsupp.coe_mk, ite_eq_left_iff, if_neg (ne_of_mem_of_not_mem hx h)]
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
        simp only [Finsupp.update, Finsupp.coe_mk]
        unfold update
        rw [dif_neg (ne_of_mem_of_not_mem hx h)]

theorem piAntidiagonal_insert [DecidableEq ι] [DecidableEq μ] {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    piAntidiagonal (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
          (piAntidiagonal s p.snd).attach.map
          (Set.InjOn.embedding (f := fun f => Finsupp.update f a p.fst)
          (fun f hf g hg => by
            simp only [mem_val, mem_piAntidiagonal] at hf hg
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
    simp
  · rintro ⟨hg, hf⟩
    constructor
    · ext x
      rw [← hf]
      simp
    · exact hg

lemma Finset.mapRange_piAntidiagonal_subset
    {μ' : Type*} [AddCommMonoid μ'] [HasPiAntidiagonal ι μ']
    (e : μ ≃+ μ') (s : Finset ι) (n : μ) :
    Finset.map (Finsupp.mapRange.addEquiv e).toEmbedding  (piAntidiagonal s n) ⊆
      piAntidiagonal s (e n) := by
  intro f
  simp only [mem_map]
  simp only [mem_piAntidiagonal]
  rintro ⟨g, ⟨hsupp, hsum⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, Finsupp.mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    Finsupp.mapRange.equiv_apply, EquivLike.coe_coe, le_eq_subset]
  constructor
  · exact subset_trans (Finsupp.support_mapRange) hsupp
  · rw [Finsupp.sum_mapRange_index (fun _ => rfl),
      ← hsum, _root_.map_finsupp_sum]

lemma Finset.mapRange_piAntidiagonal_eq
    {μ' : Type*} [AddCommMonoid μ'] [HasPiAntidiagonal ι μ']
    (e : μ ≃+ μ') (s : Finset ι) (n : μ):
    Finset.map (Finsupp.mapRange.addEquiv e).toEmbedding  (piAntidiagonal s n) =
      piAntidiagonal s (e n) := by
  ext f
  constructor
  · apply Finset.mapRange_piAntidiagonal_subset
  · set h := (Finsupp.mapRange.addEquiv e).toEquiv with hh
    intro hf
    rw [Finset.mem_map_equiv]
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [this]
    apply Finset.mapRange_piAntidiagonal_subset
    rw [← Finset.mem_map_equiv]
    convert hf
    rw [Finset.map_map, hh]
    convert Finset.map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end


section CanonicallyOrderedAddCommMonoid

variable {ι μ : Type*} [CanonicallyOrderedAddCommMonoid μ] [HasPiAntidiagonal ι μ]

theorem piAntidiagonal_zero (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp only [mem_piAntidiagonal', mem_singleton, sum_eq_zero_iff]
  simp only [Finset.le_eq_subset]
  constructor
  · rintro ⟨hsupp, hsum⟩
    ext x
    by_cases hx : x ∈ f.support
    · exact hsum x (hsupp hx)
    · simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hx
  · intro hf
    simp [hf]

/- theorem piAntidiagonal_zero' (s : Finset ι) :
    piAntidiagonal s (0 : μ) = {(0 : ι →₀ μ)} := by
  ext f
  simp only [mem_piAntidiagonal, mem_singleton, sum_eq_zero_iff]
  simp only [Finset.le_eq_subset]
  constructor
  · rintro ⟨_, hsum⟩
    ext x
    by_cases hx : x ∈ f.support
    · rw [← Finsupp.add_sum_erase f x _ hx] at hsum
      simp only [Finsupp.mem_support_iff, ne_eq, not_not, add_eq_zero_iff] at hsum
      rw [hsum.1]
      rfl
    · simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hx
  · intro hf
    simp [hf] -/

end CanonicallyOrderedAddCommMonoid
end HasPiAntidiagonal

section Construction
/- Here, we construct an `HasPiAntidiagonal ι μ` whenever we are given `HasAntidiagonal μ` -/
open HasPiAntidiagonal
namespace HasAntidiagonal

namespace HasPiAntidiagonal

variable {ι : Type*} [DecidableEq ι]

variable {μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ]

/-- The Finset underlying `Finset.HasAntidiagonal.HasPiAntidiagonal` -/
noncomputable def piAntidiagonal' (s : Finset ι) (n : μ) : Finset (ι →₀ μ) := by
  exact (finAntidiagonal s.card n).map {
    toFun := Finsupp.embDomain {
        toFun := Subtype.val.comp (equivFin s).symm,
        inj' := by
          rw [Equiv.injective_comp]
          exact Subtype.val_injective }
    inj' := Finsupp.embDomain_injective _ }
      -- fun f g => by simp only [Finsupp.embDomain_inj, imp_self] }

lemma mem_embDomain {α β M : Type*} [AddCommMonoid M] (f : α ↪ β) (g : β →₀ M) :
    (∃  (v : α →₀ M), Finsupp.embDomain f v = g) ↔ (g.support : Set β) ⊆ (Set.range f) := by
  constructor
  · rintro ⟨v, rfl⟩
    simp only [Finsupp.support_embDomain, coe_map, Set.image_subset_iff, Set.preimage_range,
      Set.subset_univ]
  · intro hg
    set v : α →₀ M :=
    { toFun := g.toFun.comp f,
      support := Finset.preimage g.support f (Set.injOn_of_injective f.injective _),
      mem_support_toFun := fun a => by
        simp only [mem_preimage, Finsupp.mem_support_iff, ne_eq, comp_apply]
        rfl} with hv
    use v
    rw [hv]
    ext b
    by_cases hb : b ∈ Set.range f
    · simp only [Set.mem_range] at hb
      obtain ⟨a, rfl⟩ := hb
      simp only [Finsupp.embDomain_apply, Finsupp.coe_mk, comp_apply]
      rfl
    · suffices hb' : g b = 0
      · rw [hb', ← Finsupp.not_mem_support_iff, Finsupp.support_embDomain, mem_map]
        rintro ⟨a, _, rfl⟩
        apply hb
        exact Set.mem_range_self a
      rw [← Finsupp.not_mem_support_iff]
      intro hb'
      apply hb
      apply hg
      simp only [mem_coe, hb']

lemma mem_piAntidiagonal' {s : Finset ι} {n : μ} {f : ι →₀ μ} :
    f ∈ piAntidiagonal' s n ↔ f.support ≤ s ∧ Finsupp.sum f (fun _ x => x) = n := by
  simp only [piAntidiagonal', mem_map, Embedding.coeFn_mk, le_eq_subset]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_finAntidiagonal] at hf
    suffices hs : _ ≤ s
    apply And.intro hs
    rw [Finsupp.sum_embDomain, hf]
    · simp only [Finsupp.support_embDomain]
      intro i
      simp only [mem_map]
      rintro ⟨k, _, rfl⟩
      simp only [Embedding.coeFn_mk, comp_apply, coe_mem]
  · rintro ⟨hsupp, hsum⟩
    simp_rw [mem_finAntidiagonal]
    set e : Fin s.card ↪ ι :=
      Function.Embedding.trans s.equivFin.symm.toEmbedding (Embedding.subtype fun x ↦ x ∈ s) with he
    have he' : ∃ (v : Fin s.card →₀ μ), Finsupp.embDomain e v = f := by
      have hrange : Set.range e = s := by
        rw [he, Embedding.trans]
        simp only [Embedding.coe_subtype, Equiv.coe_toEmbedding, Embedding.coeFn_mk,
          EquivLike.range_comp, Subtype.range_coe_subtype, setOf_mem]
      rw [mem_embDomain e f, hrange, coe_subset]
      exact hsupp
    obtain ⟨v : Fin s.card →₀ μ, hv⟩ := he'
    use v
    constructor
    · rw [← hv] at hsum
      simp only [Finsupp.sum_embDomain] at hsum
      exact hsum
    · rw [← hv, he]
      rfl

end HasPiAntidiagonal

open Finset.HasAntidiagonal.HasPiAntidiagonal

/-- Given `HasAntidiagonal μ`, a definition of `HasPiAntidiagonal` -/
noncomputable def HasPiAntidiagonal {ι μ : Type*} [AddCommMonoid μ] [HasAntidiagonal μ]
  [DecidableEq μ]:
  HasPiAntidiagonal ι μ :=
{ piAntidiagonal     := piAntidiagonal'
  mem_piAntidiagonal := mem_piAntidiagonal' }

end HasAntidiagonal

end Construction

end HasPiAntidiagonal

end Finset

section MvPowerSeries

open MvPowerSeries BigOperators Finset.HasPiAntidiagonal Finset
namespace MvPowerSeries

variable {α : Type*} [CommSemiring α]
  {σ : Type*} [DecidableEq σ]
  {ι : Type*} [DecidableEq ι]

/-- Coefficients of a product of power series -/
theorem coeff_prod [HasPiAntidiagonal ι (σ →₀ ℕ)]
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
    · apply Finset.sum_congr rfl
      · rintro ⟨u, v⟩ huv
        simp only [mem_antidiagonal] at huv
        simp only [sum_map, Set.InjOn.embedding_apply, Finsupp.coe_update, ne_eq,
          Function.update_same]
        rw [ih, mul_sum, ← Finset.sum_attach]
        apply Finset.sum_congr rfl
        rintro ⟨x, hx⟩ _
        rw [Finset.prod_insert ha]
        apply congr_arg₂
        · apply congr_arg
          simp only [Function.update_same]
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_noteq]
          exact ne_of_mem_of_not_mem hi ha
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, mem_antidiagonal]
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      rw [Function.onFun_apply, disjoint_left]
      intro _
      simp only [mem_map, mem_attach, true_and, Subtype.exists]
      rintro ⟨k, _, rfl⟩
      rintro ⟨l, _, hkl⟩
      simp only [Set.InjOn.embedding, Function.Embedding.coeFn_mk, Set.restrict_apply] at hkl
      rw [FunLike.ext_iff] at hkl
      specialize hkl a
      simp only [Finsupp.coe_update, Function.update_same] at hkl
      simp only [hkl.symm, ← huv', add_right_inj] at huv
      apply h
      simp only [Prod.mk.inj_iff]
      exact ⟨hkl.symm, huv⟩

end MvPowerSeries
end MvPowerSeries

section PowerSeries

open PowerSeries
namespace PowerSeries

open BigOperators Finset.HasPiAntidiagonal Finset

variable {α : Type*} [CommSemiring α]
  {ι : Type*} [DecidableEq ι]

-- Ugly proof, by rewriting as much as possible to use the case of
-- multivariable power series

/-- When ι is finite and μ is an AddCommMonoid,
  then Finsupp.equivFunOnFinite gives and AddEquiv -/
noncomputable def Finsupp.addEquivFunOnFinite {μ : Type*} [AddCommMonoid μ]
    {ι : Type*} [Finite ι] : (ι →₀ μ) ≃+ (ι → μ) := {
  Finsupp.equivFunOnFinite with
  map_add' := fun _ _ => rfl }

/-- AddEquiv between (ι →₀ μ) and μ, when ι has a unique element -/
noncomputable def AddEquiv.finsuppUnique {μ : Type*} [AddCommMonoid μ]
    {ι : Type*} [Unique ι] : (ι →₀ μ) ≃+ μ := {
  Equiv.finsuppUnique with
  map_add' := fun _ _ => rfl }

/-- Coefficients of a product of power series -/
theorem coeff_prod [HasPiAntidiagonal ι ℕ]
    (f : ι → PowerSeries α) (d : ℕ) (s : Finset ι) :
    coeff α d (∏ j in s, f j) =
      ∑ l in piAntidiagonal s d,
        ∏ i in s, coeff α (l i) (f i) := by
  simp only [PowerSeries.coeff]
  haveI : HasPiAntidiagonal ι (Unit →₀ ℕ) := HasAntidiagonal.HasPiAntidiagonal
  convert MvPowerSeries.coeff_prod f (fun₀ | () => d) s
  have := Finset.mapRange_piAntidiagonal_eq (ι := ι)
    (AddEquiv.finsuppUnique (ι := Unit)) s (AddEquiv.finsuppUnique.symm d)
  simp only [AddEquiv.toEquiv_eq_coe, Finsupp.mapRange.addEquiv_toEquiv,
    AddEquiv.apply_symm_apply] at this
  rw [← this, Finset.sum_map]
  apply Finset.sum_congr
  · apply congr_arg₂ _ rfl
    ext
    simp only [PUnit.default_eq_unit, Finsupp.single_eq_same]
    rfl
  · intro d _
    apply Finset.prod_congr rfl
    intro i _
    congr
    simp only [Equiv.coe_toEmbedding, Finsupp.mapRange.equiv_apply, EquivLike.coe_coe,
      Finsupp.mapRange_apply]
    ext
    simp only [PUnit.default_eq_unit, Finsupp.single_eq_same]
    rfl

end PowerSeries

end PowerSeries
